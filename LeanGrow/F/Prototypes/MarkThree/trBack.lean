
import LeanGrow.F.Prototypes.MarkThree.trTypes
import LeanGrow.F.Data.Unification.UnifyForBackWUnis
import LeanGrow.F.Utils.Array
import Mathlib.Data.List.Basic

open Lean

def NodeExpr.toCExpr : NodeExpr → CExpr
|  .ofLNode i t =>  .lnode i (.ofBvar 42) t
|  .ofGNode i =>  .gnode i (.ofBvar 42)
|  .ofCExpr ce => ce


/-- returns assigned hyps, and unassigned hyps of applied thm, together with their typ,
where local dependent lnodes are replaced
by gnodes from the query-ltx that were derived from unification
Example of le_trans aplication : a and c get assigned, and we should propagate
this to the types of the hypotheses a ≤ b and b ≤ c
-/
def propagate_lnode_and_tag (thm_data : Array EmbedData) (backwardId : Nat)
  (matchData : Array (Option CExpr)) (assiP : List (Name × Level)) : List (Nat × CExpr) × List (Nat × CExpr) :=
  let (assigned, toFix) : List (Nat × CExpr) × List (Nat × CExpr) :=
    (matchData.foldl
    (fun (i,a,f) as? =>
        match as? with
        | .some ne => (i+1, (i, ne) :: a, f)
            -- may produce large terms when lnode was matched to a big expression
        | _ => (i+1, a, (i, (thm_data.get! i).cexpr) :: f)
    )
    (0,[],[])).2
  let u_ps := assiP.map Prod.fst
  let u_ls := assiP.map Prod.snd
  let rec update : CExpr → CExpr
    | .lnode i o .none => -- important to ignore taged ones, as they are to be considered constants
          match assigned.find? (fun x => x.1 == i) with
          | .some ce => ce.2
          | _ => .lnode i o (.some backwardId)
    | .app f a => .app (update f) (update a)
    | .lam n f a i => .lam n (update f) (update a) i
    | .forallE n f a i => .forallE n (update f) (update a) i
    | .letE n f a z i => .letE n (update f) (update a) (update z) i
    | .proj n i a => .proj n i (update a)
    | .const n l => .const n (l.map (fun x => x.instantiateParams u_ps u_ls))
    | ce => ce
  let fixed := toFix.map (fun (i,ce) => (i, update ce))
  (assigned, fixed)



partial def BackTree.modifyAtGoalId (id : Nat) (mod : BackTree → BackTree) : BackTree → BackTree
  | .fail => .fail
  | .ofAssign ce => .ofAssign ce
  | .ofUni ai ce => .ofUni ai ce
  | .ofPropa ai gi t bdirs gdirs sol => if gi == id then mod (.ofPropa ai gi t bdirs gdirs sol) else ofPropa ai gi t bdirs gdirs sol
  | .ofGoal j t bdirs gdirs sol => if j == id then mod (.ofGoal j t bdirs gdirs sol) else .ofGoal j t bdirs gdirs sol
  | .ofBack i n bdirs gdirs ts =>
      match gdirs.findIdx? (fun l => l.contains id) with
      | .none => .ofBack i n bdirs gdirs ts
      | .some j => .ofBack i n bdirs gdirs (ts.set! j (BackTree.modifyAtGoalId id mod (ts.get! j)))



partial def BackTree.modifyAtBackId (id : Nat) (mod : BackTree → BackTree) : BackTree → BackTree
  | .fail => .fail
  | .ofAssign ce => .ofAssign ce
  | .ofUni ai ce => .ofUni ai ce
  | .ofGoal j t bdirs gdirs ts =>
        if bdirs.contains id
        then .ofGoal j t bdirs gdirs (ts.map (BackTree.modifyAtBackId id mod))
        else .ofGoal j t bdirs gdirs ts
  | .ofPropa i j t bdirs gdirs ts =>
        if bdirs.contains id
        then .ofPropa i j t bdirs gdirs (ts.map (BackTree.modifyAtBackId id mod))
        else .ofPropa i j t bdirs gdirs ts
  | .ofBack i n bdirs gdirs ts =>
        if i == id
        then
          mod (.ofBack i n bdirs gdirs ts)
        else
          match bdirs.findIdx? (fun l => l.contains id) with
          | .none => .ofBack i n bdirs gdirs ts
          | .some j => .ofBack i n bdirs gdirs (ts.set! j (BackTree.modifyAtBackId id mod (ts.get! j)))


partial def BackTree.modifyAtBackId? (id : Nat) (mod : BackTree → Option BackTree) : BackTree → Option BackTree
  | .fail => .some (.fail)
  | .ofAssign ce => .some (.ofAssign ce)
  | .ofUni ai ce => .some (.ofUni ai ce)
  | .ofGoal j t bdirs gdirs ts =>
      if bdirs.contains id
      then
        let res := ts.map (BackTree.modifyAtBackId? id mod)
        if res.contains .none
        then .none
        else .some (.ofGoal j t bdirs gdirs res.reduceOption)
      else .some (.ofGoal j t bdirs gdirs ts)
  | .ofPropa i j t bdirs gdirs ts =>
      if bdirs.contains id
      then
        let res := ts.map (BackTree.modifyAtBackId? id mod)
        if res.contains .none
        then .none
        else .some (.ofPropa i j t bdirs gdirs res.reduceOption)
      else .some (.ofPropa i j t bdirs gdirs ts)
  | .ofBack i n bdirs gdirs ts =>
        if i == id
        then
          mod (.ofBack i n bdirs gdirs ts)
        else
          match bdirs.findIdx? (fun l => l.contains id) with
          | .none => .some (.ofBack i n bdirs gdirs ts)
          | .some j =>
              match (BackTree.modifyAtBackId? id mod (ts.get! j)) with
              | .none => .none
              | .some fix => .some (.ofBack i n bdirs gdirs (ts.set! j fix))

def List.hasNone : List (Option α) → Bool
  | [] => false
  | .none :: _ => true
  | _ :: xs => xs.hasNone

private def List.getSome : List (Option α) → Option α
  | [] => .none
  | .some x :: _ => .some x
  | _ :: xs => xs.getSome

partial def BackTree.modifyAtBackId_wRetrieve (id : Nat)
  (mod : BackTree → Option (BackTree × Option α) ) : BackTree → Option (BackTree × Option α)
  | .fail => .some (.fail, default)
  | .ofUni ai ce => .some (.ofUni ai ce, default)
  | .ofAssign ce => .some (.ofAssign ce, default)
  | .ofGoal j t bdirs gdirs ts =>
      if bdirs.contains id
      then
        let res := ts.map (BackTree.modifyAtBackId_wRetrieve  id mod)
        if res.hasNone
        then .none
        else
          let Ts := res.reduceOption
          .some (.ofGoal j t bdirs gdirs (Ts.map Prod.fst), (Ts.map Prod.snd).getSome)
      else .some (.ofGoal j t bdirs gdirs ts, .none)
  | .ofPropa i j t bdirs gdirs ts =>
      if bdirs.contains id
      then
        let res := ts.map (BackTree.modifyAtBackId_wRetrieve  id mod)
        if res.hasNone
        then .none
        else
          let Ts := res.reduceOption
          .some (.ofPropa i j t bdirs gdirs (Ts.map Prod.fst), (Ts.map Prod.snd).getSome)
      else .some (.ofPropa i j t bdirs gdirs ts, .none)
  | .ofBack i n bdirs gdirs ts =>
        if i == id
        then
          mod (.ofBack i n bdirs gdirs ts)
        else
          match bdirs.findIdx? (fun l => l.contains id) with
          | .none => .some (.ofBack i n bdirs gdirs ts, default)
          | .some j =>
              match (BackTree.modifyAtBackId_wRetrieve id mod (ts.get! j)) with
              | .none => .none
              | .some fix => .some (.ofBack i n bdirs gdirs (ts.set! j fix.1), fix.2)


def List.replaceByListAt (toAdd : List α) : List α → Nat → List α
  | [], _ => [] -- shouldn't happen
  | _ :: more, 0 => toAdd ++ more
  | h :: more, n+1 => h :: (List.replaceByListAt toAdd more n)

def List.replaceByListWhen (toAdd : List α) (p : α → Bool) : List α → List α
  | [] => []
  | h :: more => if p h then toAdd ++ more else h :: (List.replaceByListWhen toAdd p more)



partial def BackTree.modifyAtGoalId_wUpdates (id : Nat) (rep : List Nat) (newBid : Nat) (mod : BackTree → BackTree) : BackTree → BackTree
  | .fail => .fail
  | .ofAssign ce => .ofAssign ce
  | .ofUni ai ce => .ofUni ai ce
  | .ofGoal j t bdirs gdirs ts => if j == id then mod (.ofGoal j t bdirs gdirs ts) else .ofGoal j t bdirs gdirs ts
  | .ofPropa i j t bdirs gdirs ts => if j == id then mod (.ofPropa i j t bdirs gdirs ts) else .ofPropa i j t bdirs gdirs ts
  | .ofBack i n bdirs gdirs ts =>
      match gdirs.findIdx? (fun l => l.contains id) with
      | .none => .ofBack i n bdirs gdirs ts
      | .some j => .ofBack i n (bdirs.set! j (newBid :: (bdirs.get! j))) (gdirs.set! j (List.replaceByListWhen rep (fun x => x == id) (gdirs.get! j))) (ts.set! j (BackTree.modifyAtGoalId id mod (ts.get! j)))


partial def BackTree.modifyAtBackId_wUpdates (id : Nat) (rep : List Nat) (mod : BackTree → BackTree) : BackTree → BackTree
  | .fail => .fail
  | .ofAssign ce => .ofAssign ce
  | .ofUni ai ce => .ofUni ai ce
  | .ofGoal j t bdirs gdirs ts => .ofGoal j t bdirs gdirs ts
  | .ofPropa i j t bdirs gdirs ts => .ofPropa i j t bdirs gdirs ts
  | .ofBack i n bdirs gdirs ts =>
      match bdirs.findIdx? (fun l => l.contains id) with
      | .none => .ofBack i n bdirs gdirs ts
      | .some j => .ofBack i n (bdirs.set! j (List.replaceByListWhen rep (fun x => x == id) (bdirs.get! j))) gdirs (ts.set! j (BackTree.modifyAtGoalId id mod (ts.get! j)))




structure IntegBack where
  new_goals : List (Nat × CExpr)
  tree : BackTree


def integrate_backstep
  (thm_name : Name) (thm_data_size : Nat) (target_goal_id : Nat)
  (assigned newgoals : List (Nat × CExpr))
  (id_gen_back : Nat) (id_gen_goal : Nat)
  (backTree : BackTree) : IntegBack :=
    let common := (newgoals.foldl (fun (l,i) (pos,type) => (((pos,i,type) :: l),i+1)) ([], id_gen_goal)).1
    let new_dirs := common.map (fun x => x.2.1)
    let dirs_new := common.foldl
      (fun A (pos,gId,_) => A.set! pos [gId])
      (Array.mkArray thm_data_size [])
    let new_leaves_1 := (Array.mkArray thm_data_size .fail)
    let new_leaves_2 := assigned.foldl
      (fun A (pos, val) => A.set! pos (.ofAssign val))
      new_leaves_1
    let new_leaves_3 := common.foldl
      (fun A (pos, gId, type) => A.set! pos (.ofGoal gId type [] [] []))
      new_leaves_2
    let new_branches : BackTree → BackTree := fun _ =>
      .ofBack id_gen_back thm_name (Array.mkArray thm_data_size []) dirs_new new_leaves_3
    let finalT := BackTree.modifyAtGoalId_wUpdates target_goal_id new_dirs id_gen_back new_branches backTree
    ⟨common.map Prod.snd, finalT⟩

/-
Just realized:
.ofAssign may actually contain lnodes !
Example : say we use Eq.trans and we have a ≤ lnode 1 and lnode 1 ≤ b
and we apply Eq.trans again at a ≤ lnode 1, then the argument nr 3 of that
backstep will be .ofAssign  lnode 1.
So we should propagated to assignements too, when unifying

-/


def List.eraseF (p : α → Bool) : List α → List α
| [] => []
| x :: l => if p x then l else x :: (List.eraseF p l)


def integrate_backstep_main
  (thm_name : Name) (thm_data_size : Nat) (target_goal_id : Nat)
  (assigned newgoals : List (Nat × CExpr))
  (state : BackState) : BackState :=
  let ⟨G,T⟩ := integrate_backstep thm_name thm_data_size target_goal_id assigned newgoals state.id_gen_back state.id_gen_goal state.bt
  let nG := G ++ (List.eraseF (fun x => x.1 == target_goal_id) state.active_goals)
  ⟨state.id_gen_back + 1, state.id_gen_goal + G.length, state.id_gen_assign + assigned.length, nG,T⟩



structure PropUniState where
  tree : BackTree
  todo : List (Nat × Nat × CExpr)
  updated : List (Nat × Nat × CExpr)
  solvedGoals : List Nat


def propagate_uni_assign_step
  (tag idx : Nat) (guni : CExpr)
  (ltx : List (Array CExpr)) (ltx_handler : Nat → (Nat × Nat))
  (sofar : PropUniState)
  : Option PropUniState :=
  let mod : BackTree → Option (BackTree × List (Nat × Nat × CExpr) × List Nat)
    | .ofBack _ n bdirs gdirs args =>
          match args.get! idx with
          | .ofAssign ce =>
                match CExpr.MatchAssignSolutions' guni ce with
                | .some _ => .some (.ofBack tag n bdirs gdirs args, [], [])
                | _ => .none
          | .ofGoal gid type gbd ggd sols =>
                dbg_trace s!"Uni-propa test with goal id {gid} type {repr type}"
                match guni with
                | .gnode gidx o =>
                    let (gp,gi) := ltx_handler gidx
                    let gt := (ltx.get! gp).get! gi
                    match CExpr.MatchAssignSolutions' gt type with
                    | .none => dbg_trace s!"Uni-propa test none" ; .none
                    | .some res =>
                        dbg_trace s!"Uni-propa test with gid {gid}"
                        .some ((.ofBack tag n bdirs gdirs (args.set! idx (.ofAssign (.gnode gidx o)))), res.1, gid :: sofar.solvedGoals)
                      -- fix ↑ from passing from Data.Unification.UnifyForBack to Data.Unification.UnifyForBackWUnis
                | _ =>
                    -- no checks
                    dbg_trace s!"Uni-propa test to assign because gunni {repr guni}"
                    .some ((.ofBack tag n bdirs gdirs (args.set! idx (.ofAssign guni))), [], gid :: sofar.solvedGoals)
          | _ => .none
    | _ => .none
  let S? := BackTree.modifyAtBackId_wRetrieve ([],[]) tag mod sofar.tree
  match S? with
  | .some (T,next) => dbg_trace "propagate_uni_assign_step : {repr next}" ; .some ⟨T, next.1 ++ sofar.todo, (tag, idx, guni) :: sofar.updated,
        next.2 ++ sofar.solvedGoals⟩ -- ???
  | _ => .none

#check CExpr.MatchAssignSolutions'

#exit

partial def propagate_uni_assign
  (ltx : List (Array CExpr)) (ltx_handler : Nat → (Nat × Nat))
  (init_uni : List (Nat × Nat × CExpr))
  (init_tree : BackTree) :
  Option (BackTree × List (Nat × Nat × CExpr) × List Nat) :=
    let rec go (on : PropUniState) : Option PropUniState :=
      match on.todo with
      | [] => .some on
      | (tag,idx,guni) :: more =>
          dbg_trace "propagate_uni_assign more : {repr more}"
          let step? := propagate_uni_assign_step tag idx guni ltx ltx_handler ⟨on.tree, more, on.updated, on.solvedGoals⟩
          match step? with
          | .none => .none
          | .some step => go step
    let res := go ⟨init_tree, init_uni, [], []⟩
    match res with
    | .none => .none
    | .some s => dbg_trace s!"Call propagate_uni_assign return {repr s.updated} and {repr s.solvedGoals}" ; .some (s.tree, s.updated, s.solvedGoals)


partial def propagate_uni_levels (assiP : List (Name × Level)) (bt : BackTree) : BackTree :=
  let u_ps := assiP.map Prod.fst
  let u_ls := assiP.map Prod.snd
  let rec go : BackTree → BackTree
    | .ofBack id thm bdirs gdirs args =>
        -- **TODO** propagate universes ← as well
        .ofBack id thm bdirs gdirs (args.map go)
    | .ofGoal id type => .ofGoal id (CExpr.instantiateLevelParams type u_ps u_ls)
    | x => x
  go bt






def customSplit (toPropa : List (Nat × Nat × CExpr)) (bdirs : Array (List Nat)) : Array (List (Nat × Nat × CExpr)) :=
  let tofill := Array.mkArray bdirs.size []
  let rec entry (i : Nat) (dirs : List Nat) (sofar : Array (List (Nat × Nat × CExpr))) (todo : List (Nat × Nat × CExpr)) : List (Nat × Nat × CExpr) → Array (List (Nat × Nat × CExpr)) × List (Nat × Nat × CExpr)
    | [] => (sofar, todo)
    | (t,p,v) :: more =>
        if dirs.contains t
        then entry i dirs (sofar.modify i (fun L => (t,p,v) :: L)) todo more
        else entry i dirs sofar ((t,p,v) :: todo) more
  let rec go (sofar : Array (List (Nat × Nat × CExpr))) (todo : List (Nat × Nat × CExpr)) : Nat → Array (List (Nat × Nat × CExpr))
    | 0 => (entry 0 (bdirs.get! 0) sofar [] todo).1
    | n+1 =>
        let (next, nextTD) := entry n (bdirs.get! n) sofar [] todo
        go next nextTD n
  go tofill toPropa tofill.size


def customSplit' (toPropa : List (Nat)) (gdirs : Array (List Nat)) : Array (List (Nat)) :=
  let tofill := Array.mkArray gdirs.size []
  let rec entry (i : Nat) (dirs : List Nat) (sofar : Array (List (Nat))) (todo : List (Nat)) : List (Nat) → Array (List (Nat)) × List (Nat)
    | [] => (sofar, todo)
    | N :: more =>
        if dirs.contains N
        then entry i dirs (sofar.modify i (fun L => N :: L)) todo more
        else entry i dirs sofar (N :: todo) more
  let rec go (sofar : Array (List (Nat))) (todo : List (Nat)) : Nat → Array (List (Nat))
    | 0 => (entry 0 (gdirs.get! 0) sofar [] todo).1
    | n+1 =>
        let (next, nextTD) := entry n (gdirs.get! n) sofar [] todo
        go next nextTD n
  go tofill toPropa tofill.size


partial def derefrenceAssignedGoals (assigned : List Nat)  : BackTree → BackTree
  | .ofBack id n bdirs gdirs args =>
      let sp := customSplit' assigned gdirs
      let update : Array BackTree := (args.foldl
        (fun (A,I) T =>
          let newT := derefrenceAssignedGoals (sp.get! I) T
          (A.set! I newT, I+1)
          )
        (Array.mkArray args.size .fail, 0)).1
      .ofBack id n bdirs (gdirs.mapF (fun L => L.filter (fun x => !(assigned.contains x)))) update
  | t => t



def List.splitMore (p : α → Bool) : List (α × β) → (List (α × β) × List (α × β))
  | [] => ([], [])
  | (a,b) :: more =>
      let (y,n) := List.splitMore p more
      if p a
      then ((a,b) :: y, n)
      else (y, (a,b) :: n)

-- make efficient
def porpagate_at_cexpr (ancestors : List (Nat × Nat × CExpr)) : CExpr → CExpr
  | .lnode pos _ (.some t) =>
        match ancestors.find? (fun x => x.1 == t && x.2.1 == pos) with
        | .none => .failed
        | .some (_,_,val) => val
  | .app l r => .app (porpagate_at_cexpr ancestors l) (porpagate_at_cexpr ancestors r)
  | .lam n l r i => .lam n (porpagate_at_cexpr ancestors l) (porpagate_at_cexpr ancestors r) i
  | .forallE n l r i => .forallE n (porpagate_at_cexpr ancestors l) (porpagate_at_cexpr ancestors r) i
  | .letE n l r z i => .letE n (porpagate_at_cexpr ancestors l) (porpagate_at_cexpr ancestors r) (porpagate_at_cexpr ancestors z) i
  | .proj n i e => .proj n i (porpagate_at_cexpr ancestors e)
  | ce => ce


partial def propagate_uni_assign_toGoalsAssigns
  (updated : List (Nat × Nat × CExpr)) (init_tree : BackTree) : BackTree :=
  let rec go (ancestors : List (Nat × Nat × CExpr)) (splitable : List (Nat × Nat × CExpr)) : BackTree → BackTree
    | .fail => .fail
    | .ofBack id n bdirs gdirs args =>
          let (here, next) := List.splitMore (fun x => x == id) splitable
          let sp := customSplit next bdirs
          let new_ancestors := here ++ ancestors
          let update : Array BackTree := (args.foldl
            (fun (A,I) T =>
              let newT := go new_ancestors (sp.get! I) T
              (A.set! I newT, I+1)
              )
            (Array.mkArray args.size BackTree.fail, 0)).1
          .ofBack id n bdirs gdirs update
    | .ofGoal id ce => .ofGoal id (porpagate_at_cexpr (splitable ++ ancestors) ce)
    | .ofAssign ce => .ofAssign (porpagate_at_cexpr (splitable ++ ancestors) ce)
  go [] updated init_tree


def integrate_uni?
  (ltx : List (Array CExpr)) (ltx_handler : Nat → (Nat × Nat))
  (init_uni : List (Nat × Nat × CExpr)) (us : List (Name × Level))
  (init_tree : BackTree) : Option (BackTree × List (Nat × Nat × CExpr) × List Nat) :=
    dbg_trace "Call integrate_uni?"
    match propagate_uni_assign ltx ltx_handler init_uni init_tree with
    | .some (TA,A,G) =>
        let TD := derefrenceAssignedGoals G TA
        -- don't know if doing this always is a waste of time
        -- only becomes necessary if theres a lot of solved goals ?
        let TF := propagate_uni_levels us (propagate_uni_assign_toGoalsAssigns A TD)
        (TF, A, G)
    | .none => .none


def integrate_uni_full
  (now : BackState) (newTree : BackTree) (updated : List (Nat × Nat × CExpr)) (assiP : List (Name × Level)) (solved : List Nat) : BackState :=
  let u_ps := assiP.map Prod.fst
  let u_ls := assiP.map Prod.snd
  let newG := ((now.active_goals.filter (fun x => !(solved.contains x.1))).map (fun (id,g) => (id, CExpr.instantiateLevelParams (porpagate_at_cexpr updated g) u_ps u_ls)))
  dbg_trace s!"new active goals {repr newG}"
  {now with active_goals := ((now.active_goals.filter (fun x => !(solved.contains x.1))).map (fun (id,g) => (id, porpagate_at_cexpr updated g))), bt := newTree}

/-
Very important aspect:
right now, we're propagating assigned goals, but *not* assigned universes,
that may very well show up in other parts of the expreesion and get affacted by
this assignement

-/


import LeanGrow.F.Search.A.trTypes
import LeanGrow.F.Data.Unification.UnifyForBack
import LeanGrow.F.Utils.Array

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
  (matchData : Array (Option NodeExpr)) : List (Nat × CExpr) × List (Nat × CExpr) :=
  let (assigned, toFix) : List (Nat × CExpr) × List (Nat × CExpr) :=
    (matchData.foldl
    (fun (i,a,f) as? =>
        match as? with
        | .some ne => (i+1, (i, NodeExpr.toCExpr ne) :: a, f)
            -- may produce large terms when lnode was matched to a big expression
        | _ => (i+1, a, (i, (thm_data.get! i).cexpr) :: f)
    )
    (0,[],[])).2
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
    | ce => ce
  let fixed := toFix.map (fun (i,ce) => (i, update ce))
  (assigned, fixed)


partial def BackTree.modifyAtGoalId (id : Nat) (mod : BackTree → BackTree) : BackTree → BackTree
  | .fail => .fail
  | .ofAssign ce => .ofAssign ce
  | .ofGoal j t => if j == id then mod (.ofGoal j t) else .ofGoal j t
  | .ofBack i n bdirs gdirs ts =>
      match gdirs.findIdx? (fun l => l.contains id) with
      | .none => .ofBack i n bdirs gdirs ts
      | .some j => .ofBack i n bdirs gdirs (ts.set! j (BackTree.modifyAtGoalId id mod (ts.get! j)))

partial def BackTree.modifyAtBackId (id : Nat) (mod : BackTree → BackTree) : BackTree → BackTree
  | .fail => .fail
  | .ofAssign ce => .ofAssign ce
  | .ofGoal j t => .ofGoal j t
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
  | .ofGoal j t => .some (.ofGoal j t)
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


partial def BackTree.modifyAtBackId_wRetrieve (default : α) (id : Nat)
  (mod : BackTree → Option (BackTree × α) ) : BackTree → Option (BackTree × α)
  | .fail => .some (.fail, default)
  | .ofAssign ce => .some (.ofAssign ce, default)
  | .ofGoal j t => .some (.ofGoal j t, default)
  | .ofBack i n bdirs gdirs ts =>
        if i == id
        then
          mod (.ofBack i n bdirs gdirs ts)
        else
          match bdirs.findIdx? (fun l => l.contains id) with
          | .none => .some (.ofBack i n bdirs gdirs ts, default)
          | .some j =>
              match (BackTree.modifyAtBackId_wRetrieve default id mod (ts.get! j)) with
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
  | .ofGoal j t => if j == id then mod (.ofGoal j t) else .ofGoal j t
  | .ofBack i n bdirs gdirs ts =>
      match gdirs.findIdx? (fun l => l.contains id) with
      | .none => .ofBack i n bdirs gdirs ts
      | .some j => .ofBack i n (bdirs.set! j (newBid :: (bdirs.get! j))) (gdirs.set! j (List.replaceByListWhen rep (fun x => x == id) (gdirs.get! j))) (ts.set! j (BackTree.modifyAtGoalId id mod (ts.get! j)))


partial def BackTree.modifyAtBackId_wUpdates (id : Nat) (rep : List Nat) (mod : BackTree → BackTree) : BackTree → BackTree
  | .fail => .fail
  | .ofAssign ce => .ofAssign ce
  | .ofGoal j t => .ofGoal j t
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
      (fun A (pos, gId, type) => A.set! pos (.ofGoal gId type))
      new_leaves_2
    let new_branches : BackTree → BackTree := fun _ =>
      .ofBack id_gen_back thm_name (Array.mkArray thm_data_size []) dirs_new new_leaves_3
    let finalT := BackTree.modifyAtGoalId_wUpdates target_goal_id new_dirs id_gen_back new_branches backTree
    ⟨common.map Prod.snd, finalT⟩




def List.eraseF (p : α → Bool) : List α → List α
| [] => []
| x :: l => if p x then l else x :: (List.eraseF p l)


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
                if ce == guni -- we could unify, but we might get .lnode _ _ = .lnode _ _ which we can't handle ? or can we ?
                -- ↑ may actually become a problem once we unify under reductions, as == will also have be up to reductions
                then
                  .some (.ofBack tag n bdirs gdirs args, [], [])
                else
                  .none
          | .ofGoal gid type =>
                match guni with
                | .gnode gidx o =>
                    let (gp,gi) := ltx_handler gidx
                    let gt := (ltx.get! gp).get! gi
                    match CExpr.MatchAssignSolutions' gt type with
                    | .none => .none
                    | .some res => .some (.ofAssign (.gnode gidx o), res, gid :: sofar.solvedGoals)
                | _ =>
                    -- no checks
                    .some (.ofAssign guni, [], gid :: sofar.solvedGoals)
          | _ => .none
    | _ => .none
  let S? := BackTree.modifyAtBackId_wRetrieve ([],[]) tag mod sofar.tree
  match S? with
  | .some (T,next) => .some ⟨T, next.1 ++ sofar.todo, (tag, idx, guni) :: sofar.updated, next.2⟩
  | _ => .none



partial def propagate_uni_assign
  (ltx : List (Array CExpr)) (ltx_handler : Nat → (Nat × Nat))
  (init_uni : List (Nat × Nat × CExpr))
  (init_tree : BackTree) :
  Option (BackTree × List (Nat × Nat × CExpr) × List Nat) :=
    let rec go (on : PropUniState) : Option PropUniState :=
      match on.todo with
      | [] => .some on
      | (tag,idx,guni) :: more =>
          let step? := propagate_uni_assign_step tag idx guni ltx ltx_handler ⟨on.tree, more, on.updated, on.solvedGoals⟩
          match step? with
          | .none => .none
          | .some step => go step
    let res := go ⟨init_tree, init_uni, [], []⟩
    match res with
    | .none => .none
    | .some s => .some (s.tree, s.updated, s.solvedGoals)






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
  (init_uni : List (Nat × Nat × CExpr))
  (init_tree : BackTree) : Option BackTree :=
    match propagate_uni_assign ltx ltx_handler init_uni init_tree with
    | .some (TA,A,G) =>
        let TD := derefrenceAssignedGoals G TA
        propagate_uni_assign_toGoalsAssigns A TD
    | .none => .none

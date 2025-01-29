
import LeanGrow.F.Prototypes.MarkFour.trTypes
import LeanGrow.F.Data.Unification.UnifyForBackWUnis
import LeanGrow.F.Utils.Array
import Mathlib.Data.List.Basic
import LeanGrow.F.Data.CExpr.ReduceInferMuggle.Control



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


-- partial def BackTree.modifyAtGoalId (id : Nat) (mod : BackTree → BackTree) : BackTree → BackTree
--   | .ofGoal j t bdirs gdirs ts =>
--       if gdirs.contains id
--       then .ofGoal j t bdirs gdirs (ts.map (BackTree.modifyAtGoalId  id mod))
--       else .ofGoal j t bdirs gdirs ts
--   | .ofPropa i j t bdirs gdirs ts =>
--       if gdirs.contains id
--       then .ofPropa i j t bdirs gdirs (ts.map (BackTree.modifyAtGoalId  id mod))
--       else .ofPropa i j t bdirs gdirs ts
--   | .ofBack i n bdirs gdirs ts =>
--       match gdirs.findIdx? (fun l => l.contains id) with
--       | .none => .ofBack i n bdirs gdirs ts
--       | .some j => .ofBack i n bdirs gdirs (ts.set! j (BackTree.modifyAtGoalId id mod (ts.get! j)))
--   | x => x





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
  | .fail => .some (.fail, .none)
  | .ofUni ai  ce => .some (.ofUni ai  ce, .none)
  | .ofAssign ce => .some (.ofAssign ce, .none)
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
  | .ofIntro i t bvs bdirs gdirs ts =>
      if bdirs.contains id
      then
        let res := ts.map (BackTree.modifyAtBackId_wRetrieve  id mod)
        if res.hasNone
        then .none
        else
          let Ts := res.reduceOption
          .some (.ofIntro i t bvs bdirs gdirs (Ts.map Prod.fst), (Ts.map Prod.snd).getSome)
      else .some (.ofIntro i t bvs bdirs gdirs ts, .none)
  | .ofBack i n bdirs gdirs ts =>
        if i == id
        then
          mod (.ofBack i n bdirs gdirs ts)
        else
          match bdirs.findIdx? (fun l => l.contains id) with
          | .none => .some (.ofBack i n bdirs gdirs ts, .none)
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
  | .ofUni ai  ce => .ofUni ai  ce
  | .ofGoal j t bdirs gdirs ts =>
      --dbg_trace s!"(modifyAtGoalId_wUpdates) G {j} {id} {gdirs}\n"
      if j == id
      then mod (.ofGoal j t bdirs gdirs ts)
      else
        if ! gdirs.contains id
        then .ofGoal j t bdirs gdirs ts
        else .ofGoal j t (newBid :: bdirs) (rep ++ gdirs) (ts.map (BackTree.modifyAtGoalId_wUpdates id rep newBid mod))
  | .ofPropa i j t bdirs gdirs ts =>
      --dbg_trace s!"(modifyAtGoalId_wUpdates) P {i} {j}\n"
      if j == id
      then mod (.ofPropa i j t bdirs gdirs ts)
      else
        if ! gdirs.contains id
        then .ofPropa i j t bdirs gdirs ts
        else .ofPropa i j t (newBid :: bdirs) (rep ++ gdirs) (ts.map (BackTree.modifyAtGoalId_wUpdates id rep newBid mod))
  | .ofIntro i t bvs bdirs gdirs ts =>
      if i == id
      then mod (.ofIntro i t bvs bdirs gdirs ts)
      else
        if ! gdirs.contains id
        then .ofIntro i t bvs bdirs gdirs ts
        else .ofIntro i t bvs (newBid :: bdirs) (rep ++ gdirs) (ts.map (BackTree.modifyAtGoalId_wUpdates id rep newBid mod))
  | .ofBack i n bdirs gdirs ts =>
      --dbg_trace s!"(modifyAtGoalId_wUpdates) B {i}\n"
      match gdirs.findIdx? (fun l => l.contains id) with
      | .none => .ofBack i n bdirs gdirs ts
      | .some j => .ofBack i n (bdirs.set! j (newBid :: (bdirs.get! j))) (gdirs.set! j (List.replaceByListWhen (id :: rep) (fun x => x == id) (gdirs.get! j))) (ts.set! j (BackTree.modifyAtGoalId_wUpdates id rep newBid mod (ts.get! j)))



partial def BackTree.modifyAtGoalId_wUpdatesG (id : Nat) (newGid : Nat) (mod : BackTree → BackTree) : BackTree → BackTree
  | .fail => .fail
  | .ofAssign ce => .ofAssign ce
  | .ofUni ai  ce => .ofUni ai  ce
  | .ofGoal j t bdirs gdirs ts =>
      if j == id
      then mod (.ofGoal j t bdirs gdirs ts)
      else
        if ! gdirs.contains id
        then .ofGoal j t bdirs gdirs ts
        else .ofGoal j t (bdirs) (newGid :: gdirs) (ts.map (BackTree.modifyAtGoalId_wUpdatesG id newGid mod))
  | .ofPropa i j t bdirs gdirs ts =>
      if j == id
      then mod (.ofPropa i j t bdirs gdirs ts)
      else
        if ! gdirs.contains id
        then .ofPropa i j t bdirs gdirs ts
        else .ofPropa i j t (bdirs) (newGid :: gdirs) (ts.map (BackTree.modifyAtGoalId_wUpdatesG id newGid mod))
  | .ofIntro i t bvs bdirs gdirs ts =>
      if i == id
      then mod (.ofIntro i t bvs bdirs gdirs ts)
      else
        if ! gdirs.contains id
        then .ofIntro i t bvs bdirs gdirs ts
        else .ofIntro i t bvs (bdirs) (newGid :: gdirs) (ts.map (BackTree.modifyAtGoalId_wUpdatesG id newGid mod))
  | .ofBack i n bdirs gdirs ts =>
      match gdirs.findIdx? (fun l => l.contains id) with
      | .none => .ofBack i n bdirs gdirs ts
      | .some j => .ofBack i n bdirs (gdirs.set! j (newGid :: (gdirs.get! j))) (ts.set! j (BackTree.modifyAtGoalId_wUpdatesG id newGid mod (ts.get! j)))



partial def intro? (e : CExpr) (f_id_gen : Nat) : Option (Nat × CExpr × List (Nat × CExpr)) :=
  let rec go (c : Nat) (bvs : List (Nat × CExpr)) : CExpr → Option (Nat × CExpr × List (Nat × CExpr))
    | .forallE _ t b _ =>
        if t.hasLNodesF then .none else go (c+1) ((c,t) :: bvs) (CExpr.instantiate (.gnode c (.ofBvar 42)) b) -- no shifts needed ?
    | e => .some (c, e, bvs)
  match e with
  | .forallE _ _ _ _ => go f_id_gen [] e
  | _ => .none






structure IntegBack where
  new_goals : List (Nat × CExpr)
  tree : BackTree


def integrate_backstep (f_id_gen : Nat)
  (thm_name : Name) (thm_data_size : Nat) (target_goal_id : Nat)
  (assigned newgoals : List (Nat × CExpr))
  (id_gen_back : Nat) (id_gen_goal : Nat)
  (backTree : BackTree) : Nat × List (Nat × CExpr) × IntegBack :=
    --dbg_trace s!"(integrate_backstep) target_goal_id {target_goal_id}\n assigned {repr assigned}\n newgoals {repr newgoals} \nid_gen_back {id_gen_back} id_gen_goal {id_gen_goal}\nT {repr backTree}"
    let common := (newgoals.foldl (fun (l,i) (pos,type) => (((pos,i,type) :: l),i+1)) ([], id_gen_goal)).1
    --dbg_trace s!"(integrate_backstep) common {repr common}"
    let new_dirs := common.map (fun x => x.2.1)
    --dbg_trace s!"(integrate_backstep) new_dirs {repr new_dirs}"
    let dirs_new := common.foldl
      (fun A (pos,gId,_) => A.set! pos [gId])
      (Array.mkArray thm_data_size [])
    --dbg_trace s!"(integrate_backstep) dirs_new {repr dirs_new}"
    let new_leaves_1 := (Array.mkArray thm_data_size .fail)
    let new_leaves_2 := assigned.foldl
      (fun A (pos, val) => A.set! pos (.ofAssign val))
      new_leaves_1
    --dbg_trace s!"(integrate_backstep) new_leaves_2 {repr new_leaves_2}"
    let (new_leaves_3,nfid,ngns,commonFix) := common.foldl
      (fun (A,fid,ngns,cF) (pos, gId, type) =>
          match intro? type fid with
          | .none => (A.set! pos (.ofGoal gId type [] [] []),fid,ngns,(pos, gId, type):: cF)
          | .some (nfig,ng,ngnodes) => (A.set! pos (.ofIntro gId ng ngnodes [] [] []),nfig,ngnodes ++ ngns, (pos, gId, ng):: cF)
          )
      (new_leaves_2,f_id_gen,[],[])
    --dbg_trace s!"(integrate_backstep) new_leaves_3 {repr new_leaves_3}"
    let new_branches : BackTree → BackTree := fun X =>
      match X with
      | .ofGoal j t bdirs gdirs ts =>
        .ofGoal j t (id_gen_back :: bdirs) (new_dirs ++ gdirs)
          ((.ofBack id_gen_back thm_name (Array.mkArray thm_data_size []) dirs_new new_leaves_3) :: ts)
      | .ofPropa i j t bdirs gdirs ts =>
        .ofPropa i j t (id_gen_back :: bdirs) (new_dirs ++ gdirs)
          ((.ofBack id_gen_back thm_name (Array.mkArray thm_data_size []) dirs_new new_leaves_3) :: ts)
      | .ofIntro i t bvs bdirs gdirs ts =>
        .ofIntro i t bvs (id_gen_back :: bdirs) (new_dirs ++ gdirs)
          ((.ofBack id_gen_back thm_name (Array.mkArray thm_data_size []) dirs_new new_leaves_3) :: ts)

      | _ => .fail
    let finalT := BackTree.modifyAtGoalId_wUpdates target_goal_id new_dirs id_gen_back new_branches backTree
    --dbg_trace s!"(integrate_backstep) fstout {repr (common.map Prod.snd)} \nfinalT : {repr finalT}\n\n"
    (nfid, ngns,⟨commonFix.map Prod.snd, finalT⟩)

--#exit

/-
Just realized:
.ofAssign may actually contain lnodes !
Example : say we use Eq.trans and we have a ≤ lnode 1 and lnode 1 ≤ b
and we apply Eq.trans again at a ≤ lnode 1, then the argument nr 3 of that
backstep will be .ofAssign  lnode 1.
So we should propagated to assignements too, when unifying
↑ actually no, these assignements are fixed and should only be considered
  at assembly

-/


def List.eraseF (p : α → Bool) : List α → List α
| [] => []
| x :: l => if p x then l else x :: (List.eraseF p l)


def extractTarget (target_goal_id : Nat) (found : CExpr) : List (Nat × CExpr) → (CExpr × List (Nat × CExpr))
    | [] => (found,[])
    | (n,ce) :: xs =>
        if n == target_goal_id
        then
          extractTarget target_goal_id ce xs
        else
          let (res,L) := (extractTarget target_goal_id found xs)
          (res, (n,ce) :: L) -- important that order be preserved in the context of ↓

--#exit

def integrate_backstep_main (f_id_gen : Nat)
  (thm_name : Name) (thm_data_size : Nat) (target_goal_id : Nat)
  (assigned newgoals : List (Nat × CExpr))
  (state : BackState) : Nat × List (Nat × CExpr) × BackState :=
  let (nfid,ngnds,⟨G,T⟩) := integrate_backstep f_id_gen thm_name thm_data_size target_goal_id assigned newgoals state.id_gen_back state.id_gen_goal state.bt
  --dbg_trace s!"(integrate_backstep_main) \nG {repr G}\nT {repr T}"
  let (ta,gs) := extractTarget target_goal_id .failed state.active_goals
  --dbg_trace s!"(integrate_backstep_main) \nta {repr ta}\ngs {repr gs}"
  let nG := gs ++ G ++ [(target_goal_id,ta)] -- new goals and initial one we be placed
  -- at the back. Reason : durring search, we look for backsteps form goals from left to right
  -- so placing the new goals at the top causes BFS, the initial at top DFS, so we do a mix
  (nfid,ngnds,⟨state.id_gen_back + 1, state.id_gen_goal + G.length, state.id_gen_assign, nG,T⟩)



structure PropUniState where
  tree : BackTree
  todo : List (Nat × Nat × CExpr)
  updated : List (Nat × Nat × CExpr)


#check CExpr.inferType

def propagate_uni_assign_step (fctx : FixCtx)
  (tag idx : Nat) (guni : CExpr) (uni_id : Nat)
  --(ltx : List (Array CExpr)) (ltx_handler : Nat → (Nat × Nat))
  (sofar : PropUniState)
  : Option PropUniState :=
  let mod : BackTree → Option (BackTree × Option (List (Nat × Nat × CExpr)))
    | .ofBack _ n bdirs gdirs args =>
          match args.get! idx with
          | .ofAssign ce => -- just check, don't affect
                match CExpr.MatchAssignSolutions' guni ce with
                | .some _ => .some (.ofBack tag n bdirs gdirs args, .some ([]))
                | _ => .none
          | .ofGoal gid type gbd ggd sols =>
                --dbg_trace s!"Uni-propa test with goal id {gid} type {repr type}"
                let gt := CExpr.inferType fctx guni
                -- match guni with
                -- | .gnode gidx _ =>
                --     let (gp,gi) := ltx_handler gidx
                --     let gt := (ltx.get! gp).get! gi
                --     dbg_trace s!"PLEASE : {repr gt}"
                match CExpr.MatchAssignSolutions' gt type with
                | .none => --dbg_trace s!"Uni-propa test none" ;
                      .none
                | .some res =>
                    --dbg_trace s!"Uni-propa test with gid {gid}"
                    .some ((.ofBack tag n bdirs gdirs (args.set! idx ( .ofGoal gid type gbd ggd (.ofUni uni_id (guni) :: sols)))), .some (res.1))
                  -- fix ↑ from passing from Data.Unification.UnifyForBack to Data.Unification.UnifyForBackWUnis
                -- | _ => dbg_trace s!"PLEASE NO"
                --     -- no checks
                --     --dbg_trace s!"Uni-propa test to assign because gunni {repr guni}"
                --     .some ((.ofBack tag n bdirs gdirs (args.set! idx ( .ofGoal gid type gbd ggd (.ofUni uni_id (guni) :: sols)))), .some ([]))
          | .ofIntro gid type bvs gbd ggd sols =>
                -- like ↑ ; ofPropa not needed, as can only be child of ofGoal, but ofIntro acts as a special ofGoal
                let gt := CExpr.inferType fctx guni
                match CExpr.MatchAssignSolutions' gt type with
                | .none =>
                      .none
                | .some res =>
                    .some ((.ofBack tag n bdirs gdirs (args.set! idx (.ofIntro gid type bvs gbd ggd (.ofUni uni_id (guni) :: sols)))), .some (res.1))
          | _ => .none
    | _ => .none
  let S? := BackTree.modifyAtBackId_wRetrieve tag mod sofar.tree
  match S? with
  | .some (T, .some next) => --dbg_trace "propagate_uni_assign_step : {repr next}" ;
      .some ⟨T, next ++ sofar.todo, (tag, idx, guni) :: sofar.updated⟩ -- ???
  | _ => .none



partial def propagate_uni_assign (fctx : FixCtx)
  (init_uni : List (Nat × Nat × CExpr)) (uni_id : Nat)
  (init_tree : BackTree) :
  Option (BackTree × List (Nat × Nat × CExpr)) :=
    let rec go (ON : PropUniState) : Option PropUniState :=
      match ON.todo with
      | [] => .some ON
      | (tag,idx,guni) :: more =>
          --dbg_trace "propagate_uni_assign more : {repr more}"
          let step? := propagate_uni_assign_step fctx tag idx guni uni_id ⟨ON.tree, more, ON.updated⟩
          --dbg_trace s!"(propagate_uni_assign) at {repr (tag,idx,guni)}\nUpdated {repr (PropUniState.updated <$> step?)}"
          match step? with
          | .none => .none
          | .some step => go step
    let res := go ⟨init_tree, init_uni, []⟩
    match res with
    | .none => .none
    | .some s => --dbg_trace s!"Call propagate_uni_assign return {repr s.updated}" ;
      .some (s.tree, s.updated)



-- partial def propagate_uni_levels (assiP : List (Name × Level)) (bt : BackTree) : BackTree :=
--   let u_ps := assiP.map Prod.fst
--   let u_ls := assiP.map Prod.snd
--   let rec go : BackTree → BackTree
--     | .ofUni uniId value => .ofUni uniId (CExpr.instantiateLevelParams value u_ps u_ls)
--     | .ofPropa (uniId goal_id : Nat) (newtype : CExpr) (bdirs : (List Nat)) (gdirs : (List Nat)) (args : List BackTree) =>

--     | ofGoal (id : Nat) (type : CExpr) (bdirs : (List Nat)) (gdirs : (List Nat)) (args : List BackTree)
--     | ofBack (id : Nat) (thm : Lean.Name) (bdirs : Array (List Nat)) (gdirs : Array (List Nat)) (args : Array BackTree) -- add levels

--     -- | .ofBack id thm bdirs gdirs args =>
--     --     -- **TODO** propagate universes ← as well
--     --     .ofBack id thm bdirs gdirs (args.map go)
--     -- | .ofGoal id type => .ofGoal id (CExpr.instantiateLevelParams type u_ps u_ls)
--     -- | x => x
--   go bt


--#exit



def customSplit (toPropa : List (Nat × Nat × CExpr)) (bdirs : Array (List Nat)) : Array (List (Nat × Nat × CExpr)) :=
  let tofill := Array.mkArray bdirs.size []
  let rec entry (i : Nat) (dirs : List Nat) (sofar : Array (List (Nat × Nat × CExpr))) (todo : List (Nat × Nat × CExpr)) : List (Nat × Nat × CExpr) → Array (List (Nat × Nat × CExpr)) × List (Nat × Nat × CExpr)
    | [] => (sofar, todo)
    | (t,p,v) :: more =>
        if dirs.contains t
        then entry i dirs (sofar.modify i (fun L => (t,p,v) :: L)) todo more
        else entry i dirs sofar ((t,p,v) :: todo) more
  let rec go (sofar : Array (List (Nat × Nat × CExpr))) (todo : List (Nat × Nat × CExpr)) : Nat → Array (List (Nat × Nat × CExpr))
    | 0 => sofar --(entry 0 (bdirs.get! 0) sofar [] todo).1
    | n+1 =>
        let (next, nextTD) := entry n (bdirs.get! n) sofar [] todo
        go next nextTD n
  let res := go tofill toPropa tofill.size
  --dbg_trace s!"(customSplit)\n toPropa {repr toPropa} bdirs {bdirs} res {repr res}"
  res

--#exit

-- def customSplit' (toPropa : List (Nat)) (gdirs : Array (List Nat)) : Array (List (Nat)) :=
--   let tofill := Array.mkArray gdirs.size []
--   let rec entry (i : Nat) (dirs : List Nat) (sofar : Array (List (Nat))) (todo : List (Nat)) : List (Nat) → Array (List (Nat)) × List (Nat)
--     | [] => (sofar, todo)
--     | N :: more =>
--         if dirs.contains N
--         then entry i dirs (sofar.modify i (fun L => N :: L)) todo more
--         else entry i dirs sofar (N :: todo) more
--   let rec go (sofar : Array (List (Nat))) (todo : List (Nat)) : Nat → Array (List (Nat))
--     | 0 => (entry 0 (gdirs.get! 0) sofar [] todo).1
--     | n+1 =>
--         let (next, nextTD) := entry n (gdirs.get! n) sofar [] todo
--         go next nextTD n
--   go tofill toPropa tofill.size


-- partial def derefrenceAssignedGoals (assigned : List Nat)  : BackTree → BackTree
--   | .ofBack id n bdirs gdirs args =>
--       let sp := customSplit' assigned gdirs
--       let update : Array BackTree := (args.foldl
--         (fun (A,I) T =>
--           let newT := derefrenceAssignedGoals (sp.get! I) T
--           (A.set! I newT, I+1)
--           )
--         (Array.mkArray args.size .fail, 0)).1
--       .ofBack id n bdirs (gdirs.mapF (fun L => L.filter (fun x => !(assigned.contains x)))) update
--   | t => t



def List.splitMore (p : α → Bool) : List (α × β) → (List (α × β) × List (α × β))
  | [] => ([], [])
  | (a,b) :: more =>
      let (y,n) := List.splitMore p more
      if p a
      then ((a,b) :: y, n)
      else (y, (a,b) :: n)

-- make efficient
def porpagate_at_cexpr (ancestors : List (Nat × Nat × CExpr)) (paramNames : List Name) (lvls : List Level) : CExpr → CExpr
  | .lnode pos _ (.some t) =>
        match ancestors.find? (fun x => x.1 == t && x.2.1 == pos) with
        | .none => .failed
        | .some (_,_,val) => val
  | .app l r => .app (porpagate_at_cexpr ancestors paramNames lvls l) (porpagate_at_cexpr ancestors paramNames lvls r)
  | .lam n l r i => .lam n (porpagate_at_cexpr ancestors paramNames lvls l) (porpagate_at_cexpr ancestors paramNames lvls r) i
  | .forallE n l r i => .forallE n (porpagate_at_cexpr ancestors paramNames lvls l) (porpagate_at_cexpr ancestors paramNames lvls r) i
  | .letE n l r z i => .letE n (porpagate_at_cexpr ancestors paramNames lvls l) (porpagate_at_cexpr ancestors paramNames lvls r) (porpagate_at_cexpr ancestors paramNames lvls z) i
  | .proj n i e => .proj n i (porpagate_at_cexpr ancestors paramNames lvls e)
  | ce => CExpr.instantiateLevelParams ce paramNames lvls

#check CExpr.instantiateLevelParams


partial def CExpr.hasFailed (E : CExpr) : Bool :=
      let rec go : List CExpr → Bool
      | [] => false
      | nx :: L =>
            match nx with
            | .failed => true
            | .app f a => go (f :: a :: L)
            | .lam _ t b _ => go (t :: b :: L)
            | .forallE _ t b _ => go (t :: b :: L)
            | .letE _ t v b _ => go (t :: v :: b :: L)
            | .proj _ _ b => go (b :: L)
            | _ => go L
      go [E]


partial def propagate_uni_assign_toGoalsAssigns (f_id_gen : Nat)
  (uni_id : Nat) (paramNames : List Name) (lvls : List Level)
  (updated : List (Nat × Nat × CExpr)) (id_gen_goal : Nat) (init_tree : BackTree) : Nat × List (Nat × List (Nat × CExpr)) × BackTree × List (Nat × CExpr) × Nat :=
  let rec go (id_gen_goal nf_id_gen : Nat) (new_goals : List (Nat × CExpr)) (new_gnodes_wGid : List (Nat × List (Nat × CExpr)))
    (ancestors : List (Nat × Nat × CExpr)) (splitable : List (Nat × Nat × CExpr)) : BackTree → Nat × List (Nat × List (Nat × CExpr)) × BackTree × List (Nat × CExpr) × Nat
    | .fail => (nf_id_gen, [],.fail,[],id_gen_goal)
    | .ofBack id n bdirs gdirs args =>
          let (here, next) := List.splitMore (fun x => x == id) splitable
          let sp := customSplit next bdirs
          let new_ancestors := here ++ ancestors
          let (new_f_id_gen, new_gnode, update, new_new_goals, new_id_gen_goal, local_new_goals) : Nat × List (Nat × List (Nat × CExpr)) × Array BackTree × List (Nat × CExpr) × Nat × Array (List Nat) := (args.foldl
            (fun ((nf,ngn, A,ngs,gi,lng),I) T =>
              let (nnf,nngn,newT,nngs, ngi) := go nf gi ngs ngn new_ancestors (sp.get! I) T
              ((nnf, nngn, A.set! I newT,nngs,ngi, lng.set! I (((List.range (ngi - gi)).map (· + gi)) ++ (lng.get! I))), I+1)
              )
            ((nf_id_gen, new_gnodes_wGid,Array.mkArray args.size BackTree.fail, new_goals, id_gen_goal, Array.mkArray args.size []), 0)).1
          (new_f_id_gen, new_gnode, .ofBack id n bdirs (local_new_goals.foldl (fun (A,i) L => (A.set! i (L ++ (A.get! i)), i+1)) (gdirs,0)).1 update, new_new_goals,  new_id_gen_goal)
    | .ofGoal gid type gbd ggd sols =>
        let propad? := (porpagate_at_cexpr (splitable ++ ancestors) paramNames lvls type)
        --dbg_trace s!""
        --dbg_trace s!"(propagate_uni_assign_toGoalsAssigns)\npropad? : {repr propad?}\ntype : {repr type}"
        if propad? == type || (CExpr.hasFailed propad?) -- cause I'm lazy, make efficient ; basicly checks if it contained propaded vals or not
        then -- no point in trying intro, as we try it at the originating backstep, and nothing changed
          let (new_f_id_gen, new_gnode,fsols,ngs,ngi) := sols.foldl (fun (nf,ngn,tsols,tngs,tngi) T =>
            let (nnf,nngn,r,rngs,rngi) := go tngi nf tngs ngn ancestors splitable T
            (nnf,nngn,r :: tsols,rngs,rngi)
            ) (nf_id_gen, new_gnodes_wGid,[],new_goals,id_gen_goal)
          (new_f_id_gen, new_gnode, .ofGoal gid type gbd (((List.range (ngi - id_gen_goal)).map (· + id_gen_goal)) ++ ggd) fsols, ngs,ngi)
        else
          let (new_f_id_gen, new_gnode, fsols,ngs,ngi) := sols.foldl (fun (nf,ngn,tsols,tngs,tngi) T =>
            let (nnf,nngn, r,rngs,rngi) := go tngi nf tngs ngn ancestors splitable T
            (nnf,nngn,r :: tsols,rngs,rngi)
            ) (nf_id_gen, new_gnodes_wGid,[],new_goals,id_gen_goal)
          match intro? propad? nf_id_gen with
          | .none =>
              let propa! : BackTree := .ofGoal gid type gbd (((List.range ((ngi + 1) - id_gen_goal)).map (· + id_gen_goal)) ++ ggd)
                ((.ofPropa uni_id (ngi) propad? gbd (((List.range ((ngi) - id_gen_goal)).map (· + id_gen_goal)) ++ ggd)
                  -- just realised we're not using new ids, so multiple copies of backs and goals 0_0
                    fsols) :: fsols)
              (new_f_id_gen, new_gnode,propa!,(ngi,propad?) :: ngs, ngi+1)
          | .some (ff_id_gen, f_goal, add_gnodes) =>
              let propa! : BackTree := .ofGoal gid type gbd (((List.range ((ngi + 2) - id_gen_goal)).map (· + id_gen_goal)) ++ ggd)
                ((.ofPropa uni_id (ngi) propad? gbd (((List.range ((ngi+1) - id_gen_goal)).map (· + id_gen_goal)) ++ ggd)
                  -- just realised we're not using new ids, so multiple copies of backs and goals 0_0
                    ((.ofIntro (ngi+1) f_goal add_gnodes [] [] [])
                        :: fsols)
                    ) :: fsols)
              (ff_id_gen, (ngi+1, add_gnodes) :: new_gnode,propa!, (ngi+1, f_goal):: (ngi,propad?) :: ngs, ngi+2)
    | .ofPropa uid gid type gbd ggd sols => -- same as ↑
        let propad? := (porpagate_at_cexpr (splitable ++ ancestors) paramNames lvls type)
        --dbg_trace s!""
        --dbg_trace s!"(propagate_uni_assign_toGoalsAssigns)\npropad? : {repr propad?}\ntype : {repr type}"
        if propad? == type || (CExpr.hasFailed propad?) -- cause I'm lazy, make efficient ; basicly checks if it contained propaded vals or not
        then
          let (new_f_id_gen, new_gnode,fsols,ngs,ngi) := sols.foldl (fun (nf,ngn,tsols,tngs,tngi) T =>
            let (nnf,nngn,r,rngs,rngi) := go tngi nf tngs ngn ancestors splitable T
            (nnf,nngn,r :: tsols,rngs,rngi)
            ) (nf_id_gen, new_gnodes_wGid,[],new_goals,id_gen_goal)
          (new_f_id_gen, new_gnode, .ofPropa uid gid type gbd (((List.range (ngi - id_gen_goal)).map (· + id_gen_goal)) ++ ggd) fsols, ngs,ngi)
        else
          let (new_f_id_gen, new_gnode, fsols,ngs,ngi) := sols.foldl (fun (nf,ngn,tsols,tngs,tngi) T =>
            let (nnf,nngn, r,rngs,rngi) := go tngi nf tngs ngn ancestors splitable T
            (nnf,nngn,r :: tsols,rngs,rngi)
            ) (nf_id_gen, new_gnodes_wGid,[],new_goals,id_gen_goal)
          match intro? propad? nf_id_gen with
          | .none =>
              let propa! : BackTree := .ofPropa uid gid type gbd (((List.range ((ngi + 1) - id_gen_goal)).map (· + id_gen_goal)) ++ ggd)
                ((.ofPropa uni_id (ngi) propad? gbd (((List.range ((ngi) - id_gen_goal)).map (· + id_gen_goal)) ++ ggd)
                  -- just realised we're not using new ids, so multiple copies of backs and goals 0_0
                    fsols) :: fsols)
              (new_f_id_gen, new_gnode,propa!,(ngi,propad?) :: ngs, ngi+1)
          | .some (ff_id_gen, f_goal, add_gnodes) =>
              let propa! : BackTree := .ofPropa uid gid type gbd (((List.range ((ngi + 2) - id_gen_goal)).map (· + id_gen_goal)) ++ ggd)
                ((.ofPropa uni_id (ngi) propad? gbd (((List.range ((ngi+1) - id_gen_goal)).map (· + id_gen_goal)) ++ ggd)
                  -- just realised we're not using new ids, so multiple copies of backs and goals 0_0
                    ((.ofIntro (ngi+1) f_goal add_gnodes [] [] [])
                        :: fsols)
                    ) :: fsols)
              (ff_id_gen, (ngi+1, add_gnodes) :: new_gnode,propa!, (ngi+1, f_goal):: (ngi,propad?) :: ngs, ngi+2)
    | .ofIntro gid type bvs gbd ggd sols => -- same as ↑
        let propad? := (porpagate_at_cexpr (splitable ++ ancestors) paramNames lvls type)
        --dbg_trace s!""
        --dbg_trace s!"(propagate_uni_assign_toGoalsAssigns)\npropad? : {repr propad?}\ntype : {repr type}"
        if propad? == type || (CExpr.hasFailed propad?) -- cause I'm lazy, make efficient ; basicly checks if it contained propaded vals or not
        then
          let (new_f_id_gen, new_gnode,fsols,ngs,ngi) := sols.foldl (fun (nf,ngn,tsols,tngs,tngi) T =>
            let (nnf,nngn,r,rngs,rngi) := go tngi nf tngs ngn ancestors splitable T
            (nnf,nngn,r :: tsols,rngs,rngi)
            ) (nf_id_gen, new_gnodes_wGid,[],new_goals,id_gen_goal)
          (new_f_id_gen, new_gnode, .ofIntro gid type bvs gbd (((List.range (ngi - id_gen_goal)).map (· + id_gen_goal)) ++ ggd) fsols, ngs,ngi)
        else
          let (new_f_id_gen, new_gnode, fsols,ngs,ngi) := sols.foldl (fun (nf,ngn,tsols,tngs,tngi) T =>
            let (nnf,nngn, r,rngs,rngi) := go tngi nf tngs ngn ancestors splitable T
            (nnf,nngn,r :: tsols,rngs,rngi)
            ) (nf_id_gen, new_gnodes_wGid,[],new_goals,id_gen_goal)
          match intro? propad? nf_id_gen with
          | .none =>
              let propa! : BackTree := .ofIntro gid type bvs gbd (((List.range ((ngi + 1) - id_gen_goal)).map (· + id_gen_goal)) ++ ggd)
                ((.ofPropa uni_id (ngi) propad? gbd (((List.range ((ngi) - id_gen_goal)).map (· + id_gen_goal)) ++ ggd)
                  -- just realised we're not using new ids, so multiple copies of backs and goals 0_0
                    fsols) :: fsols)
              (new_f_id_gen, new_gnode,propa!,(ngi,propad?) :: ngs, ngi+1)
          | .some (ff_id_gen, f_goal, add_gnodes) =>
              let propa! : BackTree := .ofIntro gid type bvs gbd (((List.range ((ngi + 2) - id_gen_goal)).map (· + id_gen_goal)) ++ ggd)
                ((.ofPropa uni_id (ngi) propad? gbd (((List.range ((ngi+1) - id_gen_goal)).map (· + id_gen_goal)) ++ ggd)
                  -- just realised we're not using new ids, so multiple copies of backs and goals 0_0
                    ((.ofIntro (ngi+1) f_goal add_gnodes [] [] [])
                        :: fsols)
                    ) :: fsols)
              (ff_id_gen, (ngi+1, add_gnodes) :: new_gnode,propa!, (ngi+1, f_goal):: (ngi,propad?) :: ngs, ngi+2)
    | x => (nf_id_gen, new_gnodes_wGid, x,new_goals,id_gen_goal)
  go id_gen_goal f_id_gen [] [] [] updated init_tree


-- TODO in ↑ : propagate gdirs of new goals ! Did I do this ?

#check 1


--#exit


def integrate_uni? (f_id_gen : Nat)
  (uni_id id_gen_goal : Nat) (paramNames : List Name) (lvls : List Level)
  (fctx : FixCtx)
  (init_uni : List (Nat × Nat × CExpr))
  (init_tree : BackTree) : Option (List (Nat × Nat × CExpr) × Nat × List (Nat × List (Nat × CExpr)) × BackTree × List (Nat × CExpr) × Nat) :=
    --dbg_trace "Call integrate_uni?"
    match propagate_uni_assign fctx init_uni uni_id init_tree with
    | .some (TA,A) =>
        (A, propagate_uni_assign_toGoalsAssigns f_id_gen uni_id paramNames lvls A id_gen_goal TA)
    | .none => .none


def integrate_uni_full
  (now : BackState) (newTree : BackTree)  (ngs : List (Nat × CExpr)) (ngi : Nat) (target_goal : Nat) : BackState :=
  let (ta,gs) := extractTarget target_goal .failed now.active_goals
  {now with bt := newTree, active_goals := gs ++ ngs ++ [(target_goal,ta)], id_gen_assign := now.id_gen_assign.succ, id_gen_goal := ngi}



-- Thought : we now have to query whether thm was already applied to a goal, as goals aren't discarded


/-

Very important aspect:
right now, we're propagating assigned goals, but *not* assigned universes,
that may very well show up in other parts of the expreesion and get affacted by
this assignement

-/

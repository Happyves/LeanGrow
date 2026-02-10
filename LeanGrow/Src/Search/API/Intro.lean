
/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import LeanGrowBeta.Caching.Build
import LeanGrowBeta.Search.API.DepsCache
import LeanGrowBeta.Search.Score.Regularisation
import LeanGrowBeta.Utils.Lean.ImportExport
import LeanGrowBeta.Search.IntroTree.Operations
import LeanGrowBeta.Search.BackTree.Operations

open Lean Meta



#check processForMain

def introModule : Name := `dummyIntroModule

def introModuleB : ByteArray := (introModule.toString.toUTF8)

def PaIn.insertS (l1 : LocalContext) (l2 : LocalInstances) (T : PaIn (List Nat)) (goal : Expr) (idx : Nat)
  : MetaM (Prod3 (PaIn (List Nat)) LocalContext LocalInstances) :=
  PaIn.insert l1 l2 goal idx T [] (fun x => [x]) (List.orderedInsertOrLeave)

-- #exit
#check 1


-- The mtraces cause masive increased compilation time
def introCore
  (l1 : LocalContext) (l2 : LocalInstances)
  (st : SearchState (List Nat)) (ugNode : Name) (unode? : Option Expr) (T : Expr)
  : MetaM (Prod3 (SearchState (List Nat)) LocalContext LocalInstances) :=
  do --trace set Tracing.Flags.none in do
  --mtrace on .zero with s!"[introCore] call to add {ugNode} of type {← ppExpr T}"
  let ugIs := [] --T.getGUFVarsIds.foldl (fun R fid => match fid with | ⟨.num _ i⟩ => i :: R | _ => R) []
  -- ↑ change to [] yielded much better result in sandbox 1
  --mtrace on .zero with s!"[introCore] ugIs {ugIs}"
  let st := {st with forwHeights := updateForwHeight st.forwHeights ugIs}
  let st := {st with forwDepths := updateForwDepth st.forwDepths ugIs}
  --mtrace on .one with s!"[introCore] new forwHeights {st.forwHeights}"
  let st := {st with forwMetadata := st.forwMetadata.push .intro}
  --mtrace on .one with s!"[introCore] new forwMetadata {repr st.forwMetadata}"
  --mtrace on .one with s!"[introCore] new forwDepths {st.forwDepths.map (fun x => x.depth)}"
  let locThmIdx :=
    match st.thmData.find? introModuleB with
    | .none => 0
    | .some thms => thms.size
  --mtrace on .zero with s!"[introCore] locThmIdx {locThmIdx}"
  let (sg?,thms) := ← do
    match T.zeta with
    | x@(.forallE ..) => processForMain l1 l2 introModule locThmIdx (.inr ⟨ugNode⟩) #[] 0 x
    | x =>
        match parseEqIff x with
        | .some .. => processForMain l1 l2 introModule locThmIdx (.inr ⟨ugNode⟩) #[] 0 x
        | .none => return (false, [])
  --mtrace on .zero with s!"[introCore] generated local theorems {thms.map (fun x => repr x.name)}"
  let addThms (l1 : LocalContext) (l2 : LocalInstances) : MetaM (Prod3 (SearchState (List Nat)) LocalContext LocalInstances) := do
    Meta.withResetRecDepth do
      --mtrace on .zero with s!"[introCore] reset rec depth"
      match thms with
      | d@(.std _ _ _ hyps mctx _ goal sinks) :: [] =>
          --mtrace on .zero with s!"[introCore] std case"
          --mtrace on .one with s!"[introCore] sinks {sinks}"
          mctx.load -- paranoina ?
          let ⟨sofarBack,l1,l2⟩ ← st.stdBackPaIn.insertS l1 l2 goal st.thm_data.size
          let st := {st with stdBackPaIn := sofarBack}
          --mtrace on .zero with s!"[introCore] add goal to back"
          let HforFwdPaIn := sinks.foldl (fun S s => match hyps[s]! with | .inst .. => S | .reg type => (type) :: S) []
          HforFwdPaIn.foldlMcps (⟨PaIn.dead, st.stdForwSetTrie_idxToThmIdx.size,l1,l2⟩ : Prod4 _ _ _ _)  (fun e ⟨T,i,l1,l2⟩ q => do
            let ⟨res,l1,l2⟩ ← T.insertS l1 l2 e i
            --mtrace on .zero with s!"[introCore] for forw, added hyp {← ppExpr e}"
            q ⟨res, i+1,l1,l2⟩)
              <| fun ⟨FwdPaIn,_,l1,l2⟩ => do
                let st := {st with stdForwSetTrie := st.stdForwSetTrie.easyInsert FwdPaIn d}
                  -- TODO make efficient version of ↑ that merges more
                let st := {st with ugnodeToThmIdx := st.ugnodeToThmIdx.insert locThmIdx st.thm_data.size}
                let st := {st with thmIdxToUGnode := st.thmIdxToUGnode.insert st.thm_data.size locThmIdx}
                let st := {st with thmData := st.thmData.upsert introModuleB (fun | .none => (.some #[d]) | .some A => .some (A.push d))}
                let st := {st with thmNameToHypIdx := st.thmNameToHypIdx.insert ugNode.toString.toUTF8 (List.Ico st.stdForwSetTrie_idxToThmIdx.size (st.stdForwSetTrie_idxToThmIdx.size + HforFwdPaIn.length))}
                let st := {st with stdForwSetTrie_idxToThmIdx := (st.stdForwSetTrie_idxToThmIdx.pushN st.thm_data.size) HforFwdPaIn.length}
                let st := {st with thm_data := st.thm_data.push d}
                return ⟨st,l1,l2⟩
      | fst@(.rw _ _ _ goal replacement _ mctx _ _) :: snd :: [] => do
          --mtrace on .zero with s!"[introCore] rw case"
          mctx.load -- paranoina ?
          --mtrace on .zero with s!"[introCore] sg? {sg?} "
          if !sg?
          then
            let ⟨sofarBackRW,l1,l2⟩ ← st.rwBackPaIn.insertS l1 l2 goal st.thm_data.size
            let st := {st with rwBackPaIn := sofarBackRW}
            --mtrace on .zero with s!"[introCore] added left to back"
            let ⟨sofarFwdRW,l1,l2⟩ ← st.rwForwPaIn.insertS l1 l2 goal st.thm_data.size
            let st := {st with rwForwPaIn := sofarFwdRW}
            --mtrace on .zero with s!"[introCore] added left to forw"
            let st := {st with ugnodeToThmIdx := st.ugnodeToThmIdx.insert locThmIdx st.thm_data.size}
            let st := {st with thmIdxToUGnode := st.thmIdxToUGnode.insert st.thm_data.size locThmIdx}
            let st := {st with thm_data := st.thm_data.push fst}
            let ⟨sofarBackRW,l1,l2⟩ ← st.rwBackPaIn.insertS l1 l2 replacement st.thm_data.size
            let st := {st with rwBackPaIn := sofarBackRW}
            --mtrace on .zero with s!"[introCore] added right to back"
            let ⟨sofarFwdRW,l1,l2⟩ ← st.rwForwPaIn.insertS l1 l2 replacement st.thm_data.size
            let st := {st with rwForwPaIn := sofarFwdRW}
            --mtrace on .zero with s!"[introCore] added rigth to forw"
            let st := {st with ugnodeToThmIdx := st.ugnodeToThmIdx.insert (locThmIdx+1) st.thm_data.size}
            let st := {st with thmIdxToUGnode := st.thmIdxToUGnode.insert st.thm_data.size (locThmIdx+1)}
            let st := {st with thmData := st.thmData.upsert introModuleB (fun | .none => (.some #[fst,snd]) | .some A => .some ((A.push fst).push snd))}
            let st := {st with thm_data := st.thm_data.push snd}
            return ⟨st,l1,l2⟩
          else
            let ⟨sofarBackRW,l1,l2⟩ ← st.rwBackPaIn.insertS l1 l2 goal st.thm_data.size
            let st := {st with rwBackPaIn := sofarBackRW}
            --mtrace on .zero with s!"[introCore] added left to back"
            let st := {st with ugnodeToThmIdx := st.ugnodeToThmIdx.insert locThmIdx st.thm_data.size}
            let st := {st with thmIdxToUGnode := st.thmIdxToUGnode.insert st.thm_data.size locThmIdx}
            let st := {st with thm_data := st.thm_data.push fst}
            let ⟨sofarBackRW,l1,l2⟩ ← st.rwBackPaIn.insertS l1 l2 replacement st.thm_data.size
            let st := {st with rwBackPaIn := sofarBackRW}
            --mtrace on .zero with s!"[introCore] added right to back"
            let st := {st with ugnodeToThmIdx := st.ugnodeToThmIdx.insert (locThmIdx+1) st.thm_data.size}
            let st := {st with thmIdxToUGnode := st.thmIdxToUGnode.insert st.thm_data.size (locThmIdx+1)}
            let st := {st with thmData := st.thmData.upsert introModuleB (fun | .none => (.some #[fst,snd]) | .some A => .some ((A.push fst).push snd))}
            let st := {st with thm_data := st.thm_data.push snd}
            return ⟨st,l1,l2⟩
      | _ => return ⟨st,l1,l2⟩
  let ⟨st,l1,l2⟩  ← addThms l1 l2
  match unode? with
  | .none =>
      let ⟨ufv,l1,l2⟩ ← WithLocalDecl ugNode T l1 l2
      let dec ← FVarId.GetDecl ufv l1 l2
      let st := updateDepsCachesPreCompNoMonad dec ugIs st
      --mtrace on .zero with s!"[introCore] updated deps to {st.depsCache.map (fun x => x.mapTRR (fun y => y.userName))}"
      let st := {st with id_gen_forw := st.id_gen_forw + 1}
      return ⟨st,l1,l2⟩
  | .some val =>
      let ⟨ufv,l1,l2⟩ ← WithLetDecl ugNode T val l1 l2
      let dec ← FVarId.GetDecl ufv l1 l2
      let st := updateDepsCachesPreCompNoMonad dec ugIs st
      --mtrace on .zero with s!"[introCore] updated deps to {st.depsCache.map (fun x => x.mapTRR (fun y => y.userName))}"
      let st := {st with id_gen_forw := st.id_gen_forw + 1}
      return ⟨st,l1,l2⟩


#check 1

def IntroTree.integrateIntroS (l1 : LocalContext) (l2 : LocalInstances)
  (spawn_goal_id : Nat) (IT : IntroTree (List Nat)) (head_goal_id : Nat) (head_goal : Expr) (newIntroForw : ListProd Nat Expr)
  : MetaM (Prod3 (IntroTree (List Nat)) LocalContext LocalInstances) :=
  IntroTree.integrateIntro
    (List.orderedUnion) (List.orderedContains)
    id (fun x => [x]) [] (List.orderedInsertOrLeave)
    l1 l2 spawn_goal_id IT head_goal_id head_goal newIntroForw

#check 1

def BackTree.integrateIntroS
  (pass spawn_goal_id : Nat) (BT : BackTree) (head_back_id head_goal_id : Nat) (head_goal : Expr) (newIntroForw : ListProd FVarId Expr)
  : BackTree :=
  let introB : BackTree := .ofIntro pass head_back_id newIntroForw [] [head_goal_id] [.ofGoal pass head_goal_id head_goal [] [] []]
  BT.modifyAtGoalId spawn_goal_id (fun _ => pass) (fun l => l ++ [head_back_id]) (fun l => l ++ [head_goal_id])
  (fun
    | .ofGoal _ i t bd gd sols => .ofGoal pass i t (bd ++ [head_back_id]) (gd ++ [head_goal_id]) (introB :: sols)
    | .ofPropa _ j i t bd gd sols => .ofPropa pass j i t (bd ++ [head_back_id]) (gd ++ [head_goal_id]) (introB :: sols)
    | .ofIntro _ i bins bd gd sols => .ofIntro pass i bins (bd ++ [head_back_id]) (gd ++ [head_goal_id]) (introB :: sols) -- don't really expect this, but no issue if we do ?
    | x => panic s!"[BackTree.integrateIntroS] reached an branch {repr x} despite targeting goal {spawn_goal_id}"
    )



partial def introPass
  (l1 : LocalContext) (l2 : LocalInstances)
  (st : SearchState (List Nat)) (pass spawn_goal_id : Nat) (spawn_goal_type : Expr)
  : MetaM (Prod6 Nat Expr (ListProd Nat Expr) (SearchState (List Nat)) LocalContext LocalInstances) :=
  -- trace set Tracing.Flags.none in
  let rec go (l1 : LocalContext) (l2 : LocalInstances) (final? : Bool) (st : SearchState (List Nat)) (toIntro : Expr) (gnIdxAndTy : ListProd FVarId Expr) (gnIdxAndTy' : ListProd Nat Expr)
    : MetaM (Prod6 Nat Expr (ListProd Nat Expr) (SearchState (List Nat)) LocalContext LocalInstances) := do
    mtrace on .zero with s!"[introPass] looking at {← ppExpr toIntro}"
    if final?
    then
      let st := {st with goalHeights := updateGoalHeight st.goalHeights spawn_goal_id}
      let st := {st with backDepths := updateBackDepth st.backDepths spawn_goal_id}
      mtrace on .one with s!"[introPass] new goalHeights {st.goalHeights}"
      mtrace on .one with s!"[introPass] new backDepths {st.backDepths.map (fun x => x.depth)}"
      -- let spawnTN := st.goalSpawn[spawn_goal_id]!
      -- let st := {st with goalSpawn := st.goalSpawn.push spawnTN}
      let st := {st with goalSpawn := st.goalSpawn.push (.some st.id_gen_back 0)}
      mtrace on .one with s!"[introPass] new goalSpawn {repr st.goalSpawn}"
      mtrace on .zero with s!"[introPass] integrating to introtree"
      let ⟨it,l1,l2⟩ ← st.introTree.integrateIntroS l1 l2
        spawn_goal_id st.id_gen_goal toIntro gnIdxAndTy'
      mtrace on .zero with s!"[introPass] new introtree {it.pp 0}"
      let st := {st with introTree := it}
      mtrace on .zero with s!"[introPass] integrating to backtree"
      let st := {st with backTree := st.backTree.integrateIntroS pass spawn_goal_id st.id_gen_back st.id_gen_goal toIntro gnIdxAndTy}
      mtrace on .one with s!"[introPass] new back {← st.backTree.pp 0}"
      let introTn := tnode st.id_gen_back 0
      let ⟨_,l1,l2,⟩ ← WithLocalDecl introTn toIntro l1 l2
        -- propagate intro (k will have to take propad goals so that we have them at the end ?!?)

      mtrace on .zero with s!"[introPass] bump goal and back id"
      let st := {st with id_gen_goal := st.id_gen_goal + 1, id_gen_back := st.id_gen_back + 1}
      mtrace on .zero with s!"[introPass] pass concluded"
      return ⟨(st.id_gen_goal - 1), toIntro, gnIdxAndTy', st,l1,l2⟩
    else
      match toIntro with
      | .letE _ T V B _ => do
          -- if ← IsProp T l1 l2
          -- then
          --   mtrace on .zero with s!"[introPass] let bound prop, instantiating"
          --   go l1 l2 final? st (Expr.instantiate1 B V) gnIdxAndTy gnIdxAndTy'  -- we don't want props as unodes
          -- else
          if T.hasTnodes
          then
            go l1 l2 true st toIntro gnIdxAndTy gnIdxAndTy'
          else
            let forwId := st.id_gen_forw
            if ← IsProp T l1 l2
            then
              let un := gnode forwId
              mtrace on .zero with s!"[introPass] calling core"
              let ⟨st,l1,l2⟩ ← introCore l1 l2 st un (.some V) T
              go l1 l2 final? st (Expr.instantiate1 B (.fvar ⟨un⟩)) gnIdxAndTy (.cons forwId T gnIdxAndTy')
            else -- ↑↓ not added to `gnIdxAndTy` because we don't want them in the backtree, only in the introtree
              let un := unode forwId
              let st := {st with uNodes := st.uNodes.push forwId}
              mtrace on .zero with s!"[introPass] calling core"
              let ⟨st,l1,l2⟩ ← introCore l1 l2 st un (.some V) T
              go l1 l2 final? st (Expr.instantiate1 B (.fvar ⟨un⟩)) gnIdxAndTy (.cons forwId T gnIdxAndTy')
      | .forallE _ T B _ => do
          if T.hasTnodes
          then
            go l1 l2 true st toIntro gnIdxAndTy gnIdxAndTy'
          else
            let forwId := st.id_gen_forw
            let gn := gnode forwId
            mtrace on .zero with s!"[introPass] calling core"
            let ⟨st,l1,l2⟩ ← introCore l1 l2 st gn .none T
            go l1 l2 final? st (Expr.instantiate1 B (.fvar ⟨gn⟩)) (.cons ⟨gn⟩ T gnIdxAndTy) (.cons forwId T gnIdxAndTy')
      | _ =>
          go l1 l2 true st toIntro gnIdxAndTy gnIdxAndTy'
  go l1 l2 false st spawn_goal_type .nil .nil




#check 1

-- #exit


/--
Takes as input the goal to introduce via `spawn_goal_id` and `spawn_goal_type`
and a (potentially empty) list of goal already integrated, which it will ad the current
one and its introed versions to the continuation

- We do not check if a property in present twice or more in the hyps
- In the current implementation, the intro-binder-types at ofIntros are in reverse
  order then in the binding

Continuation takes the list of new goal-ids and their types (currently inculding the spawn id)
They will have to be unified with u-g-nodes and scored and fully integrated.
There's no point in unifying the u-g-nodes generated via intro with any goals, as the only
ones they are allowed to unify with are the ones that spawned them ...
-/
partial def introMain (l1 : LocalContext) (l2 : LocalInstances) (st : SearchState (List Nat))
  (initNewGoals  newForw : ListProd Nat Expr) (spawn_goal_id : Nat) (spawn_goal_type : Expr)
  : MetaM (Prod5 (ListProd Nat Expr) (ListProd Nat Expr) (SearchState (List Nat)) LocalContext LocalInstances)  :=
  do --trace set Tracing.Flags.none in do
  let spawn_goal_type ← whnfD spawn_goal_type
  match spawn_goal_type with
  | .forallE .. | .letE .. =>
    let .mk headId ohead introd st l1 l2 ← introPass l1 l2 st st.id_gen_apass spawn_goal_id spawn_goal_type
      mtrace on .zero with s!"[introMain] head {← ppExpr ohead}"
      let head ← WhnfD ohead l1 l2
      -- will unfold definitions, except for irreducible ones
      mtrace on .zero with s!"[introMain] whnfed to {← ppExpr head}"
      if head == ohead
      then
        return .mk (introd.append newForw) (.cons headId head initNewGoals) st l1 l2
      else
        introMain l1 l2 st (.cons headId ohead initNewGoals) (introd.append newForw) headId head
  | _ => return .mk newForw initNewGoals st l1 l2




partial def introWiLtxMain (l1 : LocalContext) (l2 : LocalInstances) (st : SearchState (List Nat))
  (initNewGoals : ListProd3 Nat Expr (PaIn (List Nat))) (newForw : ListProd Nat Expr)
  (spawn_goal_id : Nat) (spawn_goal_type : Expr) (spawn_goal_ltx : PaIn (List Nat))
  : MetaM (Prod5 (ListProd Nat Expr) (ListProd3 Nat Expr (PaIn (List Nat))) (SearchState (List Nat)) LocalContext LocalInstances) :=
  do --trace set Tracing.Flags.none in do
  mtrace on .zero with s!"[introWiLtxMain] call on goal {spawn_goal_id} of type {← ppExpr spawn_goal_type}"
  let spawn_goal_type ← WhnfD spawn_goal_type l1 l2
  mtrace on .zero with s!"[introWiLtxMain] reduced goal to type {← ppExpr spawn_goal_type}"
  match spawn_goal_type with
  | .forallE .. | .letE .. =>
    let .mk headId ohead ltxAdd st l1 l2 ← introPass l1 l2 st st.id_gen_apass spawn_goal_id spawn_goal_type
    mtrace on .zero with s!"[introWiLtxMain] head {← ppExpr ohead}"
    let head ← WhnfD ohead l1 l2
    -- will unfold definitions, except for irreducible ones
    mtrace on .zero with s!"[introWiLtxMain] whnfed to {← ppExpr head}"
    mtrace on .zero with s!"[introWiLtxMain] ltxAdd:"
    ltxAdd.foldlM () (fun ugi T _ => do mtrace on .zero with s!"[introWiLtxMain] index {ugi} type {← ppExpr T}" ; pure ())
    ltxAdd.foldlMcps (.mk spawn_goal_ltx l1 l2 : Prod3 _ _ _) (fun ugi e (.mk T l1 l2) q => do
      q (← T.insertS l1 l2 e ugi)) <| fun (.mk ltxHere l1 l2) => do
        if head == ohead
        then
          return .mk (ltxAdd.append newForw) (.cons headId head ltxHere initNewGoals) st l1 l2
        else
          introWiLtxMain l1 l2 st (.cons headId ohead ltxHere initNewGoals) (ltxAdd.append newForw) headId head ltxHere
  | _ => return .mk newForw initNewGoals st l1 l2

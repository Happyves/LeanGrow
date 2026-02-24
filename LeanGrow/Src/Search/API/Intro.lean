
/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import LeanGrow.Src.Search.API.DepsCache
import LeanGrow.Src.Search.Score.Regularisation
import LeanGrow.Src.Utils.Lean.ImportExport
import LeanGrow.Src.Search.IntroTree.Operations
import LeanGrow.Src.Search.BackTree.Operations

open Lean Meta



#check processForMain

def introModule : Name := `dummyIntroModule

def introModuleB : ByteArray := (introModule.toString.toUTF8)


def PaInG.insertS (l1 : LocalContext) (l2 : LocalInstances) (T : PaInG UInt32Array) (goal : Expr) (idx : Nat)
  : MetaM (Prod3 (PaInG UInt32Array) LocalContext LocalInstances) :=
  PaInG.insert l1 l2 goal idx T
    UInt32Array.empty (fun x => UInt32Array.single x.toUInt32)
    (fun x y => y.oInsert x.toUInt32)


#check 1


def SetTrieP.easyInsert {α : Type _} [Inhabited α] (T : SetTrieP α UInt32Array PaInG)
  (key : PaInG UInt32Array) (val : α) : SetTrieP α UInt32Array PaInG :=
  let is := key.getIndicesS
  match T with
  | .root all kids =>
    let all := PaInG.merge UInt32Array.union UInt32Array.empty all key
    let kids := kids.push (.leaf is val)
    .root all kids
  | _ => panic! s!"[SetTrieP.easyInsert] bad tree"

#check 1



def addThms (l1 : LocalContext) (l2 : LocalInstances)
  (st : SearchState UInt32Array) (sg? : Bool) (locThmIdx : Nat) (ugNode : ByteArray)
  (thms : ListProd badUniType ThmFormat)
  : MetaM (Prod3 (SearchState UInt32Array) LocalContext LocalInstances) := do
    mtracing
    -- Meta.withResetRecDepth do -- is a withReader and breakes TR :(
    mtrace on .zero with s!"[introCore] reset rec depth"
    match thms with
    | .nil => return ⟨st,l1,l2⟩
    | .cons badu d@(.std _ _ _ hyps _ _ goal sinks ..) more =>
        mtrace on .zero with s!" std case"
        mtrace on .zero with s!" badu {repr badu}"
        mtrace on .one with s!" sinks {sinks}"
        match badu with
        | .both =>
          addThms l1 l2 st sg? locThmIdx ugNode more
        | .fwdOnly =>
          let st := {st with ugnodeToThmIdx := st.ugnodeToThmIdx.insert locThmIdx st.thm_data.size}
          let st := {st with thmIdxToUGnode := st.thmIdxToUGnode.insert st.thm_data.size locThmIdx}
          let thmIdx := (match (st.thmData.find? introModuleB) with | .none => 0 | .some A => A.size)
          let st := {st with thmNameToThmIdx := st.thmNameToThmIdx.upsert ugNode (fun | .none => UInt32Array.single thmIdx.toUInt32 | .some is => is.oInsert thmIdx.toUInt32)}
          let st := {st with thmData := st.thmData.upsert introModuleB (fun | .none => (.some #[d]) | .some A => .some (A.push d))}
          let ⟨sofarBack,l1,l2⟩ ← st.stdBackPaIn.insertS l1 l2 goal st.thm_data.size
          let st := {st with stdBackPaIn := sofarBack}
          let st := {st with thm_data := st.thm_data.push d}
          addThms l1 l2 st sg? locThmIdx ugNode more
        | .bckOnly =>
          let st := {st with ugnodeToThmIdx := st.ugnodeToThmIdx.insert locThmIdx st.thm_data.size}
          let st := {st with thmIdxToUGnode := st.thmIdxToUGnode.insert st.thm_data.size locThmIdx}
          let thmIdx := (match (st.thmData.find? introModuleB) with | .none => 0 | .some A => A.size)
          let st := {st with thmNameToThmIdx := st.thmNameToThmIdx.upsert ugNode (fun | .none => UInt32Array.single thmIdx.toUInt32 | .some is => is.oInsert thmIdx.toUInt32)}
          let st := {st with thmData := st.thmData.upsert introModuleB (fun | .none => (.some #[d]) | .some A => .some (A.push d))}
          let (hfp_len, HforFwdPaIn) : Nat × ListProd Expr Nat := sinks.foldl (fun S s => match hyps[s]! with | .inst .. => S | .reg type => (S.1 + 1, .cons type s S.2)) (0,.nil)
          let .mk FwdPaIn hyptosink _ l1 l2 ← HforFwdPaIn.foldlM
            (Prod5.mk PaInG.dead st.stdForwSetTrie_idxToSinkIdx st.stdForwSetTrie_idxToThmIdx.size l1 l2)
            (fun e si (.mk T hyptosink i l1 l2) => do
              let ⟨res,l1,l2⟩ ← T.insertS l1 l2 e i
              let hyptosink := hyptosink.push si
              return (.mk res hyptosink (i+1) l1 l2))
          let st := {st with stdForwSetTrie := st.stdForwSetTrie.easyInsert FwdPaIn d}
          let st := {st with stdForwSetTrie_idxToSinkIdx := hyptosink}
          let interval := (List.Ico st.stdForwSetTrie_idxToThmIdx.size (st.stdForwSetTrie_idxToThmIdx.size + hfp_len)).foldl (fun R i =>
            R.push i.toUInt32) UInt32Array.empty
          let st := {st with thmNameToHypIdx := st.thmNameToHypIdx.insert ugNode interval}
          let st := {st with stdForwSetTrie_idxToThmIdx := (st.stdForwSetTrie_idxToThmIdx.pushN st.thm_data.size) hfp_len}
          let st := {st with thm_data := st.thm_data.push d}
          addThms l1 l2 st sg? locThmIdx ugNode more
        | .no =>
          let st := {st with ugnodeToThmIdx := st.ugnodeToThmIdx.insert locThmIdx st.thm_data.size}
          mtrace on .zero with "sanity 1"
          let st := {st with thmIdxToUGnode := st.thmIdxToUGnode.insert st.thm_data.size locThmIdx}
          mtrace on .zero with "sanity 2"
          let thmIdx := (match (st.thmData.find? introModuleB) with | .none => 0 | .some A => A.size)
          mtrace on .zero with "sanity 3"
          let st := {st with thmNameToThmIdx := st.thmNameToThmIdx.upsert ugNode (fun | .none => UInt32Array.single thmIdx.toUInt32 | .some is => is.oInsert thmIdx.toUInt32)}
          mtrace on .zero with "sanity 4"
          let st := {st with thmData := st.thmData.upsert introModuleB (fun | .none => (.some #[d]) | .some A => .some (A.push d))}
          mtrace on .zero with "sanity 5"
          let ⟨sofarBack,l1,l2⟩ ← st.stdBackPaIn.insertS l1 l2 goal st.thm_data.size
          mtrace on .zero with "sanity 6"
          let st := {st with stdBackPaIn := sofarBack}
          let (hfp_len, HforFwdPaIn) : Nat × ListProd Expr Nat := sinks.foldl (fun S s => match hyps[s]! with | .inst .. => S | .reg type => (S.1 + 1, .cons type s S.2)) (0,.nil)
          mtrace on .zero with "sanity 7"
          let .mk FwdPaIn hyptosink _ l1 l2 ← HforFwdPaIn.foldlM
            (Prod5.mk PaInG.dead st.stdForwSetTrie_idxToSinkIdx st.stdForwSetTrie_idxToThmIdx.size l1 l2)
            (fun e si (.mk T hyptosink i l1 l2) => do
              let ⟨res,l1,l2⟩ ← T.insertS l1 l2 e i
              mtrace on .zero with s!" for forw, added hyp {← ppExpr e}"
              let hyptosink := hyptosink.push si
              return (.mk res hyptosink (i+1) l1 l2))
          mtrace on .zero with "sanity 8"
          let st := {st with stdForwSetTrie := st.stdForwSetTrie.easyInsert FwdPaIn d}
          let st := {st with stdForwSetTrie_idxToSinkIdx := hyptosink}
          let interval := (List.Ico st.stdForwSetTrie_idxToThmIdx.size (st.stdForwSetTrie_idxToThmIdx.size + hfp_len)).foldl (fun R i =>
            R.push i.toUInt32) UInt32Array.empty
          let st := {st with thmNameToHypIdx := st.thmNameToHypIdx.insert ugNode interval}
          let st := {st with stdForwSetTrie_idxToThmIdx := (st.stdForwSetTrie_idxToThmIdx.pushN st.thm_data.size) hfp_len}
          let st := {st with thm_data := st.thm_data.push d}
          mtrace on .zero with "sanity 9"
          addThms l1 l2 st sg? locThmIdx ugNode more
    | .cons badu d@(.rw _ _ _ goal ..) more => do
      mtrace on .zero with s!" rw case"
      mtrace on .zero with s!" badu {repr badu}"
      match badu with
      | .no =>
        let st := {st with ugnodeToThmIdx := st.ugnodeToThmIdx.insert locThmIdx st.thm_data.size}
        let st := {st with thmIdxToUGnode := st.thmIdxToUGnode.insert st.thm_data.size locThmIdx}
        let thmIdx := (match (st.thmData.find? introModuleB) with | .none => 0 | .some A => A.size)
        let st := {st with thmNameToThmIdx := st.thmNameToThmIdx.upsert ugNode (fun | .none => UInt32Array.single thmIdx.toUInt32 | .some is => is.oInsert thmIdx.toUInt32)}
        let st := {st with thmData := st.thmData.upsert introModuleB (fun | .none => (.some #[d]) | .some A => .some (A.push d))}
        mtrace on .zero with s!" sg? {sg?} "
        if ! sg?
        then
          let ⟨sofarBack,l1,l2⟩ ← st.rwBackPaIn.insertS l1 l2 goal st.thm_data.size
          let st := {st with rwBackPaIn := sofarBack}
          mtrace on .zero with s!" added left to back"
          let ⟨sofarF,l1,l2⟩ ← st.rwForwPaIn.insertS l1 l2 goal st.thm_data.size
          let st := {st with rwForwPaIn := sofarF}
          let st := {st with thm_data := st.thm_data.push d}
          mtrace on .zero with s!" added left to forw"
          addThms l1 l2 st sg? locThmIdx ugNode more
        else
          let ⟨sofarBack,l1,l2⟩ ← st.rwBackPaIn.insertS l1 l2 goal st.thm_data.size
          let st := {st with rwBackPaIn := sofarBack}
          let st := {st with thm_data := st.thm_data.push d}
          mtrace on .zero with s!" added left to back"
          addThms l1 l2 st sg? locThmIdx ugNode more
      | _ =>
        addThms l1 l2 st sg? locThmIdx ugNode more


-- #exit

-- The mtraces cause masive increased compilation time
def introCore
  (l1 : LocalContext) (l2 : LocalInstances)
  (st : SearchState UInt32Array) (ugNode : Name) (unode? : Option Expr) (T : Expr)
  : MetaM (Prod3 (SearchState UInt32Array) LocalContext LocalInstances) :=
  do
  mtracing
  mtrace on .zero with s!"[introCore] call to add {ugNode} of type {← ppExpr T}"
  let ugIs := UInt32Array.empty  --T.getGUFVarsIds.foldl (fun R fid => match fid with | ⟨.num _ i⟩ => i :: R | _ => R) []
  -- ↑ change to [] yielded much better result in sandbox 1
  mtrace on .zero with s!"[introCore] ugIs {ugIs}"
  let st := {st with forwHeights := updateForwHeight st.forwHeights ugIs}
  let st := {st with forwDepths := updateForwDepth st.forwDepths ugIs}
  mtrace on .one with s!"[introCore] new forwHeights {st.forwHeights}"
  let st := {st with forwMetadata := st.forwMetadata.push .intro}
  mtrace on .one with s!"[introCore] new forwMetadata {repr st.forwMetadata}"
  mtrace on .one with s!"[introCore] new forwDepths {st.forwDepths.map (fun x => x.depth)}"
  let locThmIdx :=
    match st.thmData.find? introModuleB with
    | .none => 0
    | .some thms => thms.size
  mtrace on .zero with s!"[introCore] locThmIdx {locThmIdx}"
  let .mk sg? thms l1 l2 := ← (do
    match T.zeta with
    | x@(.forallE ..) => processForMain l1 l2 introModule locThmIdx (.inr ⟨ugNode⟩) #[] 0 x
    | x =>
        match parseEqIff x with
        | .some .. => processForMain l1 l2 introModule locThmIdx (.inr ⟨ugNode⟩) #[] 0 x
        | .none => return .mk false .nil l1 l2)
  mtrace on .zero with s!"[introCore] generated local theorems {thms.foldl [] (fun _ x L => x.name :: L)}"
  let ⟨st,l1,l2⟩  ← addThms l1 l2 st sg? locThmIdx ugNode.toString.toUTF8 thms
  match unode? with
  | .none =>
      let ⟨ufv,l1,l2⟩ ← WithLocalDecl ugNode T l1 l2
      let st ← updateDepsCachesPreCompNoMonad l1 l2 ufv st
      mtrace on .zero with s!"[introCore] updated deps to {st.depsCache.map (fun x => x.fTrans)}"
      let st := {st with id_gen_forw := st.id_gen_forw + 1}
      return ⟨st,l1,l2⟩
  | .some val =>
      let ⟨ufv,l1,l2⟩ ← WithLetDecl ugNode T val l1 l2
      let st ← updateDepsCachesPreCompNoMonad l1 l2 ufv st
      mtrace on .zero with s!"[introCore] updated deps to {st.depsCache.map (fun x => x.fTrans)}"
      let st := {st with id_gen_forw := st.id_gen_forw + 1}
      return ⟨st,l1,l2⟩


#check 1
#check IntroTree.integrateIntro


def IntroTree.integrateIntroS (l1 : LocalContext)
  (spawn_goal_id : Nat) (IT : IntroTree UInt32Array) (head_goal_id : Nat) (head_goal : Expr) (newIntroForw : ListProd3 Nat FVarId Expr)
  : MetaM (Prod (IntroTree UInt32Array) LocalContext) :=
  IntroTree.integrateIntro
    UInt32Array.union (fun x y => y.oContains x.toUInt32)
    (fun x => UInt32Array.single x.toUInt32) UInt32Array.empty
    (fun x y => y.oInsert x.toUInt32)
    l1 spawn_goal_id IT head_goal_id head_goal newIntroForw

#check 1

def BackTree.integrateIntroS
  (pass spawn_goal_id : Nat) (BT : BackTree) (head_back_id head_goal_id : Nat) (head_goal : Expr) (newIntroForw : ListProd FVarId Expr)
  : BackTree :=
  let introB : BackTree := .ofIntro pass head_back_id newIntroForw .empty (.single head_goal_id.toUInt32) [.ofGoal pass head_goal_id head_goal .empty .empty []]
  BT.modifyAtGoalId spawn_goal_id (fun _ => pass) (fun l => l.push head_back_id.toUInt32) (fun l => l.push head_goal_id.toUInt32)
  (fun
    | .ofGoal _ i t bd gd sols => .ofGoal pass i t (bd.push head_back_id.toUInt32) (gd.push head_goal_id.toUInt32) (introB :: sols)
    | .ofPropa _ j i t bd gd sols => .ofPropa pass j i t (bd.push head_back_id.toUInt32) (gd.push head_goal_id.toUInt32) (introB :: sols)
    | .ofIntro _ i bins bd gd sols => .ofIntro pass i bins (bd.push head_back_id.toUInt32) (gd.push head_goal_id.toUInt32) (introB :: sols) -- don't really expect this, but no issue if we do ?
    | x => panic s!"[BackTree.integrateIntroS] reached an branch {repr x} despite targeting goal {spawn_goal_id}"
    )

#check 1




partial def introPass
  (l1 : LocalContext) (l2 : LocalInstances)
  (st : SearchState UInt32Array) (pass spawn_goal_id : Nat) (spawn_goal_type : Expr)
  : MetaM (Prod6 Nat Expr (ListProd3 Nat FVarId Expr) (SearchState UInt32Array) LocalContext LocalInstances) :=
  do
  mtracing
  let rec go (l1 : LocalContext) (l2 : LocalInstances) (final? : Bool) (st : SearchState UInt32Array) (toIntro : Expr) (gnIdxAndTy : ListProd FVarId Expr)
    (gnIdxAndTy' : ListProd3 Nat FVarId Expr)
    : MetaM (Prod6 Nat Expr (ListProd3 Nat FVarId Expr) (SearchState UInt32Array) LocalContext LocalInstances) := do
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
      let ⟨it,l1⟩ ← st.introTree.integrateIntroS l1
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
              go l1 l2 final? st (Expr.instantiate1 B (.fvar ⟨un⟩)) (.cons ⟨un⟩ T gnIdxAndTy) (.cons forwId ⟨un⟩ T gnIdxAndTy')
            else
              -- At some point: ↑↓ not added to `gnIdxAndTy` because we don't want them in the backtree, only in the introtree
              -- lead to bugs, first occurence in test_3 of snadbox one ...
              let un := unode forwId
              let st := {st with uNodes := st.uNodes.push forwId}
              mtrace on .zero with s!"[introPass] calling core"
              let ⟨st,l1,l2⟩ ← introCore l1 l2 st un (.some V) T
              go l1 l2 final? st (Expr.instantiate1 B (.fvar ⟨un⟩)) (.cons ⟨un⟩ T gnIdxAndTy) (.cons forwId ⟨un⟩ T gnIdxAndTy')
      | .forallE _ T B _ => do
          if T.hasTnodes
          then
            go l1 l2 true st toIntro gnIdxAndTy gnIdxAndTy'
          else
            let forwId := st.id_gen_forw
            let gn := gnode forwId
            mtrace on .zero with s!"[introPass] calling core"
            let ⟨st,l1,l2⟩ ← introCore l1 l2 st gn .none T
            go l1 l2 final? st (Expr.instantiate1 B (.fvar ⟨gn⟩)) (.cons ⟨gn⟩ T gnIdxAndTy) (.cons forwId ⟨gn⟩ T gnIdxAndTy')
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
partial def introMain (l1 : LocalContext) (l2 : LocalInstances) (st : SearchState UInt32Array)
  (initNewGoals : ListProd Nat Expr) (newForw : ListProd3 Nat FVarId Expr) (spawn_goal_id : Nat) (spawn_goal_type : Expr)
  : MetaM (Prod5 (ListProd3 Nat FVarId Expr) (ListProd Nat Expr) (SearchState UInt32Array) LocalContext LocalInstances)  :=
  do
  mtracing
  let spawn_goal_type ← WhnfD spawn_goal_type l1 l2
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

#check 1




partial def introWiLtxMain (l1 : LocalContext) (l2 : LocalInstances) (st : SearchState UInt32Array)
  (initNewGoals : ListProd3 Nat Expr (PaInG UInt32Array)) (newForw : ListProd3 Nat FVarId Expr)
  (spawn_goal_id : Nat) (spawn_goal_type : Expr) (spawn_goal_ltx : PaInG UInt32Array)
  : MetaM (Prod5 (ListProd3 Nat FVarId Expr) (ListProd3 Nat Expr (PaInG UInt32Array)) (SearchState UInt32Array) LocalContext LocalInstances) :=
  do
  mtracing
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
    ltxAdd.foldlM () (fun ugi _ T _ => do mtrace on .zero with s!"[introWiLtxMain] index {ugi} type {← ppExpr T}" ; pure ())
    let .mk ltxHere l1 l2 ← ltxAdd.foldlM (.mk spawn_goal_ltx l1 l2 : Prod3 _ _ _) (fun ugi _ e (.mk T l1 l2) => do
      (T.insertS l1 l2 e ugi)
      )
    if head == ohead
    then
      return .mk (ltxAdd.append newForw) (.cons headId head ltxHere initNewGoals) st l1 l2
    else
      introWiLtxMain l1 l2 st (.cons headId ohead ltxHere initNewGoals) (ltxAdd.append newForw) headId head ltxHere
  | _ => return .mk newForw initNewGoals st l1 l2

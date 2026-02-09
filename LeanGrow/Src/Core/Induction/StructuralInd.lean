
/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/


import LeanGrow.Src.Utils.LeanGrow.Expr
import LeanGrow.Src.Core.Induction.Format
import LeanGrow.Src.Utils.Lean.Generalize
import LeanGrow.Src.Utils.Lean.Revert

open Lean Meta


@[inline]
private def getMajorTypeIndices (recursorInfo : RecursorInfo) (majorType : Expr) : MetaM (Option (Array Expr)) := do
  let majorTypeArgs := majorType.getAppArgs
  let res ← recursorInfo.indicesPos.toArray.mapM (fun idxPos => do
    if h : idxPos ≥ majorTypeArgs.size
    then
      return Option.none
    else
      let idx := majorTypeArgs[idxPos]
      unless idx.isFVar do return .none
      for hi : i in [:majorTypeArgs.size] do
        let arg := majorTypeArgs[i]
        if i != idxPos && arg == idx then
          return (.none : Option (Expr))
        if i < idxPos then
          if (← exprDependsOn arg idx.fvarId!) then
            return .none
        if i > idxPos && recursorInfo.indicesPos.contains i && arg.isFVar then
          let idxDecl ← idx.fvarId!.getDecl
          if (← localDeclDependsOn idxDecl arg.fvarId!) then
            return .none
      return .some idx)
  if res.contains .none
  then return .none
  else return res.reduceOption


private def addRecParams (mvarId : MVarId) (majorTypeArgs : Array Expr) : List (Option Nat) → Expr → MetaM (Option Expr)
  | [], recursor => pure recursor
  | some pos :: rest, recursor =>
    if h : pos < majorTypeArgs.size then
      addRecParams mvarId majorTypeArgs rest (mkApp recursor (majorTypeArgs[pos]))
    else
      return .none
  | none :: rest, recursor => do
    let recursorType ← inferType recursor
    let recursorType ← whnfForall recursorType
    match recursorType with
    | Expr.forallE _ d _ _ => do
      let param ← try synthInstance d catch _ => return .none
      addRecParams mvarId majorTypeArgs rest (mkApp recursor param)
    | _ =>
      return .none


private def mkRecursorAppPrefix (mvarId : MVarId)  (major : Expr) (recursorInfo : RecursorInfo) (indices : Array Expr) : MetaM (Option Expr) := do
  let target ← mvarId.getType
  let targetLevel ← getLevel target
  let targetLevel ← normalizeLevel targetLevel
  let some majorType ← whnfUntil (← inferType major) recursorInfo.typeName | return .none
  majorType.withApp fun majorTypeFn majorTypeArgs => do
    match majorTypeFn with
    | .const _ majorTypeFnLevels => do
      let majorTypeFnLevels := majorTypeFnLevels.toArray
      let lres ← recursorInfo.univLevelPos.foldlM (init := Option.some (#[], false))
          fun X (univPos : RecursorUnivLevelPos) =>
            match X with
            | .none => return .none
            | .some (recursorLevels, foundTargetLevel) => do
                match univPos with
                | RecursorUnivLevelPos.motive => return .some (recursorLevels.push targetLevel, true)
                | RecursorUnivLevelPos.majorType idx =>
                  if h : idx ≥ majorTypeFnLevels.size then
                    return .none
                  else
                    return .some (recursorLevels.push majorTypeFnLevels[idx], foundTargetLevel)
      let .some (recursorLevels, foundTargetLevel) := lres | return .none
      if !foundTargetLevel && !targetLevel.isZero then
        return .none
      let recursor := mkConst recursorInfo.recursorName recursorLevels.toList
      let .some recursor ← addRecParams mvarId majorTypeArgs recursorInfo.paramsPos recursor | return .none
      let motive := target
      let motive ← if recursorInfo.depElim then
        pure <| mkLambda `x BinderInfo.default (← inferType major) (Expr.abstractPat major motive)
      else
        pure motive
      let motive ← mkLambdaFVars indices motive
      return mkApp recursor motive
    | _ =>
      return .none


private def getTypeBody (type : Expr) (x : Expr) : MetaM (Option Expr) := do
  let type ← whnfForall type
  match type with
  | Expr.forallE _ _ b _ => return (.some (b.instantiate1 x))
  | _                    => return .none


private partial def getTargetArity : Expr → Nat
  | Expr.mdata _ b       => getTargetArity b
  | Expr.forallE _ _ b _ => getTargetArity b + 1
  | e                    => if e.isHeadBetaTarget then getTargetArity e.headBeta else 0

@[inline]
private partial def finalize
    (l1 : LocalContext) (l2 : LocalInstances)
    (backIdx : Nat)
    (mvarId : MVarId)  (recursorInfo : RecursorInfo)
    (major : Expr) (indices : Array Expr) (recursor : Expr)
    : MetaM (Prod3 (Option (Array Expr)) LocalContext LocalInstances) := do
  let target ← mvarId.getType
  let initialArity := getTargetArity target
  let recursorType ← inferType recursor
  let numMinors := recursorInfo.produceMotive.length
  let rec @[specialize] loop (l1 : LocalContext) (l2 : LocalInstances) (pos : Nat) (minorIdx : Nat) (recursor recursorType : Expr) (consumedMajor : Bool) (subgoals : Array Expr) : MetaM (Prod3 (Option (Array Expr)) LocalContext LocalInstances) := do
      let recursorType ← WhnfForall recursorType l1 l2
      if recursorType.isForall && pos < recursorInfo.numArgs then
        if pos == recursorInfo.firstIndexPos then
          let X ← indices.foldlM (init := Option.some (recursor, recursorType)) fun Y index => do
            match Y with
            | .none => return .none
            | .some (recursor, recursorType) =>
              let recursor := mkApp recursor index
              let .some recursorType ← GetTypeBody recursorType index l1 l2 | return Option.none
              return .some (recursor, recursorType)
          let .some (recursor, recursorType) := X | return ⟨.none,l1,l2⟩
          let recursor := mkApp recursor major
          let .some recursorType ← GetTypeBody recursorType major l1 l2 | return ⟨.none,l1,l2⟩
          loop l1 l2 (pos+1+indices.size) minorIdx recursor recursorType true subgoals
        else
          if minorIdx ≥ numMinors
          then return ⟨.none,l1,l2⟩
          else
            match recursorType with
            | Expr.forallE _ d _ c =>
              let d := d.headBeta
              if c.isInstImplicit then
                match (← SynthInstance d l1 l2) with
                | some inst =>
                  let recursor := mkApp recursor inst
                  let .some recursorType ← GetTypeBody recursorType inst l1 l2 | return ⟨.none,l1,l2⟩
                  loop l1 l2 (pos+1) (minorIdx+1) recursor recursorType consumedMajor subgoals
                | none => do
                  let node := .num (.num `t backIdx) subgoals.size
                  let ⟨nodeFv,l1,l2⟩ ← WithLocalDecl node d l1 l2
                  let fvar := .fvar nodeFv
                  let recursor := mkApp recursor fvar
                  let .some recursorType ← GetTypeBody recursorType fvar l1 l2 | return ⟨.none,l1,l2⟩
                  loop l1 l2 (pos+1) (minorIdx+1) recursor recursorType consumedMajor (subgoals.push fvar)
              else
                let arity := getTargetArity d
                if arity < initialArity
                then return ⟨.none,l1,l2⟩
                else
                  let node := .num (.num `t backIdx) subgoals.size
                  let ⟨nodeFv,l1,l2⟩ ← WithLocalDecl node d l1 l2
                  let fvar := .fvar nodeFv
                  let recursor := mkApp recursor fvar
                  let .some recursorType ← GetTypeBody recursorType fvar l1 l2 | return ⟨.none,l1,l2⟩
                  loop l1 l2 (pos+1) (minorIdx+1) recursor recursorType consumedMajor (subgoals.push fvar)
            | _ => unreachable!
      else
        mvarId.assign recursor
        return ⟨.some subgoals,l1,l2⟩
  loop l1 l2 (recursorInfo.paramsPos.length + 1) 0 recursor recursorType false #[]

#check 1

partial def checkTnodesSitchOkForInd (l1 : LocalContext) (l2 : LocalInstances)
  (relevant : Array FVarId) : Expr → MetaM Bool
  | .forallE _ T B _ =>
    if T.hasTnodes then return false else checkTnodesSitchOkForInd l1 l2 relevant B
  | T =>
    let tns := T.getTnodes
    let rec safedeps? (seen : ExprSet) : List Expr → MetaM Bool
      | [] => return true
      | t :: ts => do
        if seen.contains t
        then safedeps? seen ts
        else
          let nts := (← InferType t l1 l2).getTnodes
          if nts.any (fun x => relevant.contains x.fvarId!)
          then
            return false
          else
            let nx := nts.foldl (fun L t =>
              if seen.contains t then L else L.insert t
              ) ts
            safedeps? (seen.insert t) nx
    safedeps? {} tns


/-- mtrace causes massive codegen slowdown-/
@[specialize]
partial def inductiveInductionMain
  (introAdmissible? : Nat → Bool) (sinkRevCutOff : Nat) (depsCache : Array DepCache)
  (l1 : LocalContext) (l2 : LocalInstances)
  (backIdx : Nat) (major : Expr) (goal : Expr)
  : MetaM (Prod3 (OptionProd Expr (Array Expr)) LocalContext LocalInstances) :=
  withReader (fun ctx => {ctx with lctx := l1, localInstances := l2}) do
    mtracing
    -- mtrace on .one with s!"[inductiveInductionMain] major {← ppExpr major}"
    let majorT ← inferType major
    -- mtrace on .one with s!"[inductiveInductionMain] majorT {← ppExpr majorT}"
    let recursorName :=
      match (← whnfAtMostI majorT).getAppFn with
      | .const n _ => n
      | _ => .anonymous
    -- mtrace on .zero with s!"[inductiveInductionMain] recursorName {recursorName}"
    let recursorInfo ← mkRecursorInfo (.str recursorName "rec")
    let some majorType ← whnfUntil majorT recursorInfo.typeName | return ⟨.none,l1,l2⟩
    -- mtrace on .zero with s!"[inductiveInductionMain] majorType {← ppExpr majorType}"
    majorType.withApp fun _ majorTypeArgs => do
      let mut broke? := false
      for paramPos? in recursorInfo.paramsPos do
        match paramPos? with
        | none          => continue
        | some paramPos => if paramPos ≥ majorTypeArgs.size then broke? := true
      if broke?
      then return ⟨.none,l1,l2⟩
      else
        let .some indices ← getMajorTypeIndices recursorInfo majorType | return ⟨.none,l1,l2⟩
        -- mtrace on .zero with s!"[inductiveInductionMain] indices {← indices.mapM ppExpr}"
        let cont? ← (do
          if (← pure !recursorInfo.depElim)
          then
            match major with
            | .fvar majorId =>
              if ← exprDependsOn goal majorId
              then return false
              else return true
            | _ => return false
          else
            return true)
        if ! cont?
        then return ⟨.none,l1,l2⟩
        else
          let relevant :=
              match major with
              | .fvar majorId => (indices.map Expr.fvarId!).push majorId
              | _ => (indices.map Expr.fvarId!)
          let .mk gen revTnodes l1 l2 ← generalizeTnodesSafeIgnoring l1 l2 goal #[] (fun _ _ _ => return false)
          match gen with
          | .none =>
            return ⟨.none,l1,l2⟩
          | .some goal => do
            -- mtrace on .zero with s!"[elimInductionMain] generalised tnodes {← revTnodes.mapM ppExpr} to new goal {← ppExpr goal}"
            if ← (do if isStructureLike (← getEnv) recursorName then checkTnodesSitchOkForInd l1 l2 relevant goal else return !(goal.hasTnodes))
            then
              -- mtrace on .zero with s!"[inductiveInductionMain] generalised tnodes {← revTnodes.mapM ppExpr} to new goal {← ppExpr goal}"
              let .mk revgoal _ allRev l1 l2 ← revert_NoTn_cutOff_wDepsCache introAdmissible? l1 l2 goal relevant depsCache #[] sinkRevCutOff
              -- mtrace on .zero with s!"[inductiveInductionMain] reverted fvars {repr allRev} to new goal {← ppExpr revgoal}"
              let allRevFirst := ((allRev.take relevant.size).map Expr.fvar).filter (fun | .fvar x => !(x.isUnode) | _ => false)
              -- **Note* ↑↓ `instantiateForall` actually uses whnf, so will reduce lets !
              -- We crutially assume that `revert` reverts unused lets also !!
              let mvar ← mkFreshExprMVar (.some (← instantiateForall revgoal allRevFirst))
              let mvarId := mvar.mvarId!
              let .some recursor ← mkRecursorAppPrefix mvarId major recursorInfo indices | return ⟨.none,l1,l2⟩
              -- mtrace on .zero with s!"[inductiveInductionMain] recursor {← ppExpr recursor}"
              match ← finalize l1 l2 backIdx mvarId recursorInfo major indices recursor with
              | ⟨.none,l1,l2⟩ =>
                  clearMvarAssignments
                  return ⟨.none,l1,l2⟩
              | ⟨.some subgoals,l1,l2⟩  =>
                  withReader (fun ctx => {ctx with lctx := l1, localInstances := l2}) do
                    let .some proofterm := (← getMCtx).eAssignment.find? mvarId | return ⟨.none,l1,l2⟩
                    -- mtrace on .zero with s!"[inductiveInductionMain] pre proofterm: {← ppExpr proofterm}"
                    -- let allRevFinal ← ((allRev.drop relevant.size).map Expr.fvar).filterM (fun
                    --   | .fvar x => do (match ← x.GetDecl l1 l2 with
                    --     | .ldecl _ _ _ T .. => IsProp T l1 l2
                    --     | .cdecl .. => return true)
                    --   | _ => return false)
                    let allRevFinal := ((allRev.drop relevant.size).map Expr.fvar).filter (fun | .fvar x => !(x.isUnode) | _ => false)
                    -- ↑ used to filter on not being unodes but that wasn't enough since forwaard proofs are also let-bound
                    let proofterm := mkAppN (mkAppN proofterm allRevFinal) revTnodes
                    -- mtrace on .zero with s!"[inductiveInductionMain] final proofterm {← ppExpr proofterm}"
                    clearMvarAssignments
                    if ← isTypeCorrect proofterm
                    then
                      return ⟨.some proofterm (← subgoals.mapM inferType),l1,l2⟩
                    else
                      -- mtrace on .zero with s!"[inductiveInductionMain] incorrect proofterm"
                      return ⟨.none,l1,l2⟩
            else
              -- mtrace on .zero with s!"[inductiveInductionMain] bad tnodes"
              return ⟨.none,l1,l2⟩


#check 1
#check isStructureLike

-- run_meta do
--   let env ← getEnv
--   IO.println <| isStructureLike env `Fin

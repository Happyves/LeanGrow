
import LeanGrow.F.Data.CExpr.API
import LeanGrow.F.Data.CExpr.ReduceInfer.Magic
import LeanGrow.F.Data.CExpr.ReduceInfer.BetaZeta
import Lean

open Lean Meta

#check getMatcherInfoCore?


inductive CExpr_ReduceMatcherResult where
  | reduced (val : CExpr)
  | stuck   (val : CExpr)
  | notMatcher
  | partialApp

def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n+2 => (fib (n+1)) + (fib n)

#print fib.match_1

elab "testing" : command => do
  let env ← getEnv
  let ext := Lean.Meta.Match.Extension.extension.getState env
  let f1 := env.find? `fib.match_1
  let f2 := ext.map.find? `fib.match_1
  IO.println s!"{f1.isSome} and {repr f2}"

-- testing




def myForallBoundedTelescope (gnodeTypes : List (Array CExpr)) (gnodeTypesHandler : Nat → (Nat × Nat))
  (ltxTypes : List (Array EmbedData)) (current : Option (Array EmbedData))
  (cstData : CTrie CstInfo) (bvarCtx : List CExpr)
  (auxAppType : CExpr) : Nat → CExpr × List CExpr
  | 0 => (auxAppType, bvarCtx)
  | n+1 =>
    match auxAppType with
    | .forallE _ t b _ => myForallBoundedTelescope gnodeTypes gnodeTypesHandler ltxTypes current cstData (t :: bvarCtx) b n
    | _ =>
        let tryharder := cexprWhnf gnodeTypes gnodeTypesHandler ltxTypes current cstData bvarCtx auxAppType
        match tryharder with
        | .forallE _ t b _ => myForallBoundedTelescope gnodeTypes gnodeTypesHandler ltxTypes current cstData (t :: bvarCtx) b n
        | _ => (.failed, []) -- because we don't expect failure ??


def CExpr.reduceMatcher? (gnodeTypes : List (Array CExpr)) (gnodeTypesHandler : Nat → (Nat × Nat))
  (ltxTypes : List (Array EmbedData)) (current : Option (Array EmbedData))
  (cstData : CTrie CstInfo) (bvarCtx : List CExpr)
  (e : CExpr) : CExpr_ReduceMatcherResult :=
  let (h,args) := CExpr.getApp e
  match h with
  | .const n lvl =>
      match cstData.find? n.toString with
      | .some (.mat paras _ val info) =>
            let prefixSz := info.numParams + 1 + info.numDiscrs
            if args.length < prefixSz + info.numAlts
            then
              .partialApp
            else
              let f := CExpr.instantiateLevelParams val paras lvl
              let auxApp := CExpr.mkApp f (args.take (prefixSz))
              let auxAppType := cexprInferType gnodeTypes gnodeTypesHandler ltxTypes current cstData bvarCtx auxApp
              let (_,BV) := myForallBoundedTelescope gnodeTypes gnodeTypesHandler ltxTypes current cstData bvarCtx auxAppType info.numAlts
              let auxAppNew := cexprWhnf gnodeTypes gnodeTypesHandler ltxTypes current cstData
                BV (CExpr.mkApp auxApp ((List.range info.numAlts).map (CExpr.bvar)).reverse)
              let (H,AS) := CExpr.getApp auxAppNew
              match H with
              | .bvar I =>
                  let result := CExpr.mkApp (args.get! (prefixSz + (info.numAlts - 1 - I))) AS
                  let result' := CExpr.mkApp result (args.drop (prefixSz + info.numAlts))
                  .reduced (CExpr.beta result')
              | _ => .stuck auxApp
      | _ => .notMatcher
  | _ => .notMatcher


#print Nat.add.eq_1

#check (1+1)

#check Subarray

#check RecursorVal.k -- good docs


def CExpr.mkNullaryCtor (cstData : CTrie CstInfo) (n : Name) (lvl : List Level) (as : List CExpr) (nparams : Nat) : Option CExpr :=
  match cstData.find? n.toString with
  | .some (.indu _ _ info) =>
      let ct := info.ctors.head!
      .some (CExpr.mkApp (.const ct lvl) (as.take nparams))
  | _ => .none

#eval Array.shrink #[1,2,3] 1


def CExpr.toCtorWhenK (gnodeTypes : List (Array CExpr)) (gnodeTypesHandler : Nat → (Nat × Nat))
  (ltxTypes : List (Array EmbedData)) (current : Option (Array EmbedData))
  (cstData : CTrie CstInfo) (bvarCtx : List CExpr)
  (recVal : RecursorVal) (major : CExpr) : CExpr :=
  let majorType := cexprWhnf gnodeTypes gnodeTypesHandler ltxTypes current cstData bvarCtx
    (cexprInferType gnodeTypes gnodeTypesHandler ltxTypes current cstData bvarCtx major)
  let (H, AS) := CExpr.getApp majorType
  match H with
  | .const n lvl =>
      if !(n == recVal.getInduct)
      then
        major
      else
        match CExpr.mkNullaryCtor cstData n lvl AS recVal.numParams with
        | .none => major
        | .some newCtorApp => newCtorApp
  | _ => major



def CExpr.toCtorIfLit : CExpr → CExpr
  | .lit (.natVal v) =>
    if v == 0 then .const `Nat.zero []
    else .app (.const `Nat.succ []) (.lit (.natVal (v-1)))
  -- can't be bothered lol ; goal would be `#eval toExpr "this".toList` ; who'll use strings anyway :>
  -- | .lit (.strVal v) =>
  --   .app (.const `String.mk []) (toExpr v.toList)
  | e => e


/-
structure test where
  a : Nat
  b : Int

#reduce test.a --fun self ↦ self.1
-/

def toCtorWhenStructure_help (strucName : Name) (nfields : Nat) (major : CExpr) (sofar : CExpr) : Nat → CExpr
  | 0 => .app sofar (.proj strucName (nfields - 1) major)
  | n+1 => toCtorWhenStructure_help strucName nfields major (.app sofar (.proj strucName (nfields - 1 - n) major) ) n



def CExpr.toCtorWhenStructure (gnodeTypes : List (Array CExpr)) (gnodeTypesHandler : Nat → (Nat × Nat))
  (ltxTypes : List (Array EmbedData)) (current : Option (Array EmbedData))
  (cstData : CTrie CstInfo) (bvarCtx : List CExpr)
  (strucName : Name) (major : CExpr) : CExpr :=
  match cstData.find? strucName.toString with
  | .some (.struc _ _ ctN ctV) =>
      match (major.getApp).1 with
      | .const N _ =>
          if !(N == ctN)
          then
            major
          else
            let majorType := cexprInferType gnodeTypes gnodeTypesHandler ltxTypes current cstData bvarCtx major
            let majorTypeType := cexprWhnf gnodeTypes gnodeTypesHandler ltxTypes current cstData bvarCtx
              (cexprInferType gnodeTypes gnodeTypesHandler ltxTypes current cstData bvarCtx majorType)
            if majorTypeType == .sort .zero
            then
              major
            else
              let (h,as) := major.getApp
              match h with
              | .const _ lvl =>
                  let params := as.take ctV.numParams
                  let wp := CExpr.mkApp (.const ctN lvl) params
                  toCtorWhenStructure_help strucName ctV.numFields major wp ctV.numFields
              | _ => major

      | _ => major
  | _ => major




/-

private def reduceRec (recVal : RecursorVal) (recLvls : List Level) (recArgs : Array Expr) (failK : Unit → MetaM α) (successK : Expr → MetaM α) : MetaM α :=
  let majorIdx := recVal.getMajorIdx
  if h : majorIdx < recArgs.size then do
    let major := recArgs.get ⟨majorIdx, h⟩
    let mut major ← if isWFRec recVal.name && (← getTransparency) == .default then
      -- If recursor is `Acc.rec` or `WellFounded.rec` and transparency is default,
      -- then we bump transparency to .all to make sure we can unfold defs defined by WellFounded recursion.
      -- We use this trick because we abstract nested proofs occurring in definitions.
      -- Alternative design: do not abstract nested proofs used to justify well-founded recursion.
      withTransparency .all <| whnf major
    else
      whnf major
    if recVal.k then
      major ← toCtorWhenK recVal major
    major := major.toCtorIfLit
    major ← cleanupNatOffsetMajor major
    major ← toCtorWhenStructure recVal.getInduct major
    match getRecRuleFor recVal major with
    | some rule =>
      let majorArgs := major.getAppArgs
      if recLvls.length != recVal.levelParams.length then
        failK ()
      else
        let rhs := rule.rhs.instantiateLevelParams recVal.levelParams recLvls
        -- Apply parameters, motives and minor premises from recursor application.
        let rhs := mkAppRange rhs 0 (recVal.numParams+recVal.numMotives+recVal.numMinors) recArgs
        /- The number of parameters in the constructor is not necessarily
           equal to the number of parameters in the recursor when we have
           nested inductive types. -/
        let nparams := majorArgs.size - rule.nfields
        let rhs := mkAppRange rhs nparams majorArgs.size majorArgs
        let rhs := mkAppRange rhs (majorIdx + 1) recArgs.size recArgs
        successK rhs
    | none => failK ()
  else
    failK ()
-/



def CExpr.reduceRec  (gnodeTypes : List (Array CExpr)) (gnodeTypesHandler : Nat → (Nat × Nat))
  (ltxTypes : List (Array EmbedData)) (current : Option (Array EmbedData))
  (cstData : CTrie CstInfo) (bvarCtx : List CExpr)
  (recVal : RecursorVal) (recLvls : List Level) (recArgs : List Expr) (on : CExpr) : CExpr :=
  let majorIdx := recVal.getMajorIdx
  if h : majorIdx < recArgs.length
  then
    let major := cexprWhnf gnodeTypes gnodeTypesHandler ltxTypes current cstData bvarCtx (recArgs.get ⟨majorIdx, h⟩)
    let eta_1 := if recVal.k then (CExpr.toCtorWhenK gnodeTypes gnodeTypesHandler ltxTypes current cstData bvarCtx recVal major) else major
    let eta_2 := eta_1.toCtorIfLit
    let eta_3 := CExpr.toCtorWhenStructure gnodeTypes gnodeTypesHandler ltxTypes current cstData bvarCtx
      recVal.getInduct eta_2
    sorry

#check getRecRuleFor


import LeanGrow.F.Data.CExpr.API
import LeanGrow.F.Data.CExpr.ReduceInferMuggle.Types
import LeanGrow.F.Data.CExpr.ReduceInferMuggle.BetaZeta
import Lean

open Lean Meta


def myForallBoundedTelescope_1 : FlowState → FlowState
  | ⟨(.myForallBoundedTelescope_1, bvarCtx) :: mI, (.ofCExpr auxAppType) :: (.ofNat iter) :: mA⟩ =>
      match iter with
      | 0 => ⟨mI, (.ofList bvarCtx) :: mA⟩ -- differs from original in that we only return the list
      | n+1 =>
          match auxAppType with
          | .forallE _ t b _ =>
              ⟨(.myForallBoundedTelescope_1, t :: bvarCtx) :: mI, (.ofCExpr b) :: (.ofNat n) :: mA⟩
          | _ =>
              ⟨(.Whnf_1, bvarCtx) :: (.myForallBoundedTelescope_2, bvarCtx) :: mI, (.ofCExpr auxAppType) :: (.ofNat n) :: mA⟩
  | _  => FailedState


def myForallBoundedTelescope_2 : FlowState → FlowState
  | ⟨(.myForallBoundedTelescope_2, bvarCtx) :: mI, (.ofCExpr auxAppType) :: (.ofNat iter) :: mA⟩ =>
        match auxAppType with
        | .forallE _ t b _ =>
            ⟨(.myForallBoundedTelescope_1, t :: bvarCtx) :: mI, (.ofCExpr b) :: (.ofNat iter) :: mA⟩
        | _ => FailedState
  | _  => FailedState



def reduceMatcher?_1 (fctx : FixCtx) : FlowState → FlowState
  | ⟨(.reduceMatcher?_1, bvarCtx) :: mI, (.ofCExpr e) ::  mA⟩ =>
        let (h,args) := CExpr.getApp e
        match h with
        | .const n lvl =>
            match fctx.cstData.find? n.toString with
            | .some (.mat paras _ val info) =>
                  let prefixSz := info.numParams + 1 + info.numDiscrs
                  if args.length < prefixSz + info.numAlts
                  then
                    ⟨mI, (.ofReduceMatcherResult .partialApp) :: mA⟩
                  else
                    let f := CExpr.instantiateLevelParams val paras lvl
                    let auxApp := CExpr.mkApp f (args.take (prefixSz))
                    ⟨(.InferType_1, bvarCtx) :: (.reduceMatcher?_2, bvarCtx) :: mI, (.ofCExpr auxApp) :: (.ofCExpr auxApp) :: (.ofList args) :: (.ofMatcherInfo info) :: (.ofNat prefixSz) :: mA⟩
            | _ => ⟨mI, (.ofReduceMatcherResult .notMatcher) :: mA⟩
        | _ => ⟨mI, (.ofReduceMatcherResult .notMatcher) :: mA⟩
  | _  => FailedState


def reduceMatcher?_2 : FlowState → FlowState
  | ⟨(.reduceMatcher?_2, bvarCtx) :: mI, (.ofCExpr auxAppType) :: (.ofCExpr auxApp) :: (.ofList args) :: (.ofMatcherInfo info) :: (.ofNat prefixSz) :: mA⟩ =>
      ⟨(.myForallBoundedTelescope_1, bvarCtx) :: (.reduceMatcher?_3, bvarCtx) :: mI, (.ofCExpr auxAppType) :: (.ofNat info.numAlts) :: (.ofCExpr auxApp) :: (.ofList args) :: (.ofMatcherInfo info) :: (.ofNat prefixSz) :: mA⟩
  | _  => FailedState


def reduceMatcher?_3 : FlowState → FlowState
  | ⟨(.reduceMatcher?_3, bvarCtx) :: mI, (.ofList BV) :: (.ofCExpr auxApp) :: (.ofList args) :: (.ofMatcherInfo info) :: (.ofNat prefixSz) :: mA⟩ =>
      let interim := (CExpr.mkApp auxApp ((List.range info.numAlts).map (CExpr.bvar)).reverse)
      ⟨(.reduceMatcher?_4, BV) ::(.reduceMatcher?_4, bvarCtx) :: mI, (.ofCExpr interim) :: (.ofCExpr auxApp) :: (.ofList args) :: (.ofMatcherInfo info) :: (.ofNat prefixSz) :: mA⟩
  | _  => FailedState


def reduceMatcher?_4 : FlowState → FlowState
  | ⟨(.reduceMatcher?_4, _) :: mI, (.ofCExpr auxAppNew) :: (.ofCExpr auxApp) :: (.ofList args) :: (.ofMatcherInfo info) :: (.ofNat prefixSz) :: mA⟩ =>
      let (H,AS) := CExpr.getApp auxAppNew
      match H with
      | .bvar I =>
          let result := CExpr.mkApp (args.get! (prefixSz + (info.numAlts - 1 - I))) AS
          let result' := CExpr.mkApp result (args.drop (prefixSz + info.numAlts))
          ⟨mI, (.ofReduceMatcherResult (.reduced (CExpr.beta result'))) :: mA⟩
      | _ =>
        ⟨mI, (.ofReduceMatcherResult (.stuck auxApp)) :: mA⟩
  | _  => FailedState


def CExpr.mkNullaryCtor (cstData : CTrie CstInfo) (n : Name) (lvl : List Level) (as : List CExpr) (nparams : Nat) : Option CExpr :=
  match cstData.find? n.toString with
  | .some (.indu _ _ info) =>
      let ct := info.ctors.head!
      .some (CExpr.mkApp (.const ct lvl) (as.take nparams))
  | _ => .none



/-

def CExpr.toCtorWhenK (fctx : FixCtx) (bvarCtx : List CExpr)
  (recName : Name) (recVal : cRecursorVal) (major : CExpr) : CExpr :=
  let majorType := cexprWhnf fctx bvarCtx
    (cexprInferType fctx bvarCtx major)
  let (H, AS) := CExpr.getApp majorType
  match H with
  | .const n lvl =>
      if !(n == recName.getPrefix)
      then
        major
      else
        match CExpr.mkNullaryCtor fctx.cstData n lvl AS recVal.numParams with
        | .none => major
        | .some newCtorApp => newCtorApp
  | _ => major

-/

def toCtorWhenK_1 : FlowState → FlowState
  | ⟨(.toCtorWhenK_1, bvarCtx) :: mI, (.ofName recName) :: (.ofcRecursorVal recVal) ::(.ofCExpr major) ::  mA⟩ =>
      ⟨(.InferType_1, bvarCtx) :: (.Whnf_1, bvarCtx) :: (.toCtorWhenK_2, bvarCtx) :: mI, (.ofCExpr major) :: (.ofName recName) :: (.ofcRecursorVal recVal) ::(.ofCExpr major) ::  mA⟩
  | _  => FailedState


def toCtorWhenK_2 (fctx : FixCtx) : FlowState → FlowState
  | ⟨(.toCtorWhenK_2, _) :: mI, (.ofCExpr majorType) :: (.ofName recName) :: (.ofcRecursorVal recVal) ::(.ofCExpr major) ::  mA⟩ =>
        let (H, AS) := CExpr.getApp majorType
        match H with
        | .const n lvl =>
            if !(n == recName.getPrefix)
            then
              ⟨mI, (.ofCExpr major) :: mA⟩
            else
              match CExpr.mkNullaryCtor fctx.cstData n lvl AS recVal.numParams with
              | .none => ⟨mI, (.ofCExpr major) :: mA⟩
              | .some newCtorApp => ⟨mI, (.ofCExpr newCtorApp) :: mA⟩
        | _ => ⟨mI, (.ofCExpr major) :: mA⟩
  | _  => FailedState



def CExpr.toCtorIfLit : CExpr → CExpr
  | .lit (.natVal v) =>
    if v == 0 then .const `Nat.zero []
    else .app (.const `Nat.succ []) (.lit (.natVal (v-1)))
  -- can't be bothered lol ; goal would be `#eval toExpr "this".toList` ; who'll use strings anyway :>
  -- | .lit (.strVal v) =>
  --   .app (.const `String.mk []) (toExpr v.toList)
  | e => e


def toCtorWhenStructure_help (strucName : Name) (nfields : Nat) (major : CExpr) (sofar : CExpr) : Nat → CExpr
  | 0 => .app sofar (.proj strucName (nfields - 1) major)
  | n+1 => toCtorWhenStructure_help strucName nfields major (.app sofar (.proj strucName (nfields - 1 - n) major) ) n


def toCtorWhenStructure_1 (fctx : FixCtx) : FlowState → FlowState
  | ⟨(.toCtorWhenStructure_1, bvarCtx) :: mI, (.ofName strucName) :: (.ofCExpr major) ::  mA⟩ =>
        match fctx.cstData.find? strucName.toString with
        | .some (.struc _ _ ctN ctV) =>
            match (major.getApp).1 with
            | .const N _ =>
                if !(N == ctN)
                then
                  ⟨mI, (.ofCExpr major) :: mA⟩
                else
                  ⟨(.InferType_1, bvarCtx) :: (.InferType_1, bvarCtx) :: (.Whnf_1, bvarCtx) ::(.toCtorWhenStructure_2, bvarCtx) :: mI, (.ofCExpr major) :: (.ofName ctN) :: (.ofConstructorVal ctV) :: (.ofName strucName) :: (.ofCExpr major) :: mA⟩
            | _ => ⟨mI, (.ofCExpr major) :: mA⟩
        | _ => ⟨mI, (.ofCExpr major) :: mA⟩
  | _  => FailedState


def toCtorWhenStructure_2 : FlowState → FlowState
  | ⟨(.toCtorWhenStructure_2, _) :: mI, (.ofCExpr majorTypeType) :: (.ofName ctN) :: (.ofConstructorVal ctV) :: (.ofName strucName) :: (.ofCExpr major) :: mA⟩ =>
      if majorTypeType == .sort .zero
      then
        ⟨mI, (.ofCExpr major) :: mA⟩
      else
        let (h,as) := major.getApp
        match h with
        | .const _ lvl =>
            let params := as.take ctV.numParams
            let wp := CExpr.mkApp (.const ctN lvl) params
            let res := toCtorWhenStructure_help strucName ctV.numFields major wp ctV.numFields
            ⟨mI, (.ofCExpr res) :: mA⟩
        | _ => ⟨mI, (.ofCExpr major) :: mA⟩
  | _  => FailedState



def cRecursorVal.getMajorIdx (v : cRecursorVal) : Nat :=
  v.numParams + v.numMotives + v.numMinors + v.numIndices


def getRecRuleFor (recVal : cRecursorVal) : CExpr → Option cRecursorRule
  | .const fn _ => recVal.rules.find? fun r => r.ctor == fn
  | _           => none

/-

def CExpr.reduceRec (fctx : FixCtx) (bvarCtx : List CExpr)
  (recName : Name) (recLvlParams : List Name) (recVal : cRecursorVal) (recLvls : List Level) (recArgs : List CExpr) (on : CExpr) : CExpr :=
  let majorIdx := recVal.getMajorIdx
  if H : majorIdx < recArgs.length
  then
    let major := cexprWhnf fctx bvarCtx (recArgs.get ⟨majorIdx, H⟩)
    let eta_1 := if recVal.k then (CExpr.toCtorWhenK fctx bvarCtx recName recVal major) else major
    let eta_2 := eta_1.toCtorIfLit
    let eta_3 := CExpr.toCtorWhenStructure fctx bvarCtx
      recName.getPrefix eta_2
    let (h,as) := eta_3.getApp
    match getRecRuleFor recVal h with
    | .none => on
    | .some rule =>
        let rhs_1 := rule.rhs.instantiateLevelParams recLvlParams recLvls
        let rhs_2 := CExpr.mkApp rhs_1 (recArgs.take (recVal.numParams+recVal.numMotives+recVal.numMinors))
        let nparams := as.length - rule.nfields
        let rhs_3 := CExpr.mkApp rhs_2 (as.drop nparams)
        cexprWhnf fctx bvarCtx (CExpr.mkApp rhs_3 (recArgs.drop (majorIdx + 1)))
        -- not in `reduceRec`, but is success in `whnfCore`
  else
    on

-/



#exit




def CExpr.reduceQuotRec (fctx : FixCtx) (bvarCtx : List CExpr)
  (recVal : QuotVal) (recArgs : List CExpr) (on : CExpr) : CExpr :=
    let process (majorPos argPos : Nat) (on' : CExpr): CExpr :=
      if H : majorPos < recArgs.length
      then
        let major := cexprWhnf fctx bvarCtx (recArgs.get ⟨majorPos, H⟩)
        match major with
        | .app (.app (.app (.const majorFn _) _) _) majorArg =>
            match fctx.cstData.find? majorFn.toString with
            | .some (.quot _ _ ⟨_,.ctor⟩) =>
                  let f := recArgs.get! argPos
                  let r := CExpr.app f majorArg
                  let recArity := majorPos + 1
                  cexprWhnf fctx bvarCtx (CExpr.mkApp r (recArgs.drop recArity))
                  -- not in `reduceQuotRec`, but is success in `whnfCore`
            | _ => on'
        | _ => on'
      else
        on'
    match recVal.kind with
    | QuotKind.lift => process 5 3 on
    | QuotKind.ind  => process 4 3 on
    | _             => on

#print Eq.ndrec


def CExpr.projectCore? (cstData : CTrie CstInfo) (e : CExpr) (i : Nat) : Option CExpr :=
  let e := e.toCtorIfLit
  let (h,as) := e.getApp
  match h with
  | .const n _ =>
      match cstData.find? n.toString with
      | .some (.ctor _ _ val) =>
          let numArgs := as.length
          let idx := val.numParams + i
          if idx < numArgs
          then
            .some (as.get! idx)
          else
            .none
      | _ => .none
  | _ => .none

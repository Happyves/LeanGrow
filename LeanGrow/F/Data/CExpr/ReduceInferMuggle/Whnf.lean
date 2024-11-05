
import LeanGrow.F.Data.CExpr.ReduceInferMuggle.BetaZeta
import LeanGrow.F.Data.CExpr.ReduceInferMuggle.Iota
import LeanGrow.F.Data.CExpr.ReduceInferMuggle.Types

open Lean


def Whnf_1 : FlowState → FlowState
  | ⟨(.Whnf_1, bvarCtx) :: mI, (.ofCExpr ce) ::  mA⟩ =>
        match ce with
        | .forallE ..    => ⟨mI, (.ofCExpr ce) ::  mA⟩
        | .lam ..        => ⟨mI, (.ofCExpr ce) ::  mA⟩
        | .sort ..       => ⟨mI, (.ofCExpr ce) ::  mA⟩
        | .lit ..        => ⟨mI, (.ofCExpr ce) ::  mA⟩
        | .bvar ..       => ⟨mI, (.ofCExpr ce) ::  mA⟩
        | .lnode ..      => ⟨mI, (.ofCExpr ce) ::  mA⟩
        | .gnode ..      => ⟨mI, (.ofCExpr ce) ::  mA⟩
        | .const ..      => ⟨mI, (.ofCExpr ce) ::  mA⟩
        | .failed        => ⟨mI, (.ofCExpr ce) ::  mA⟩
        | .letE _ _ v b _ =>
            ⟨(.Whnf_1, bvarCtx) :: mI, (.ofCExpr (CExpr.instantiateShift v b)) ::  mA⟩
        | .app .. =>
            match ce.letFunAppArgs? with
            | .some (args, _, _, v, b) =>
                ⟨(.Whnf_1, bvarCtx) :: mI, (.ofCExpr (CExpr.mkApp (CExpr.instantiateShift v b) args)) ::  mA⟩
            | _ =>
                let (f,as) := ce.getApp
                ⟨(.Whnf_1, bvarCtx) :: (.Whnf_3, bvarCtx) :: mI, (.ofCExpr f) :: (.ofList as) :: mA⟩
        | .proj _ i c =>
            ⟨(.Whnf_1, bvarCtx) :: (.Whnf_2, bvarCtx) :: mI, (.ofCExpr c) :: (.ofNat i) :: (.ofCExpr ce) :: mA⟩
  | _  => FailedState


def Whnf_2 (fctx : FixCtx) : FlowState → FlowState
  | ⟨(.Whnf_2, bvarCtx) :: mI, (.ofCExpr c) :: (.ofNat i) :: (.ofCExpr ce) :: mA⟩ =>
        match CExpr.projectCore? fctx.cstData c i with
        | .some res => ⟨(.Whnf_1, bvarCtx) :: mI, (.ofCExpr res) :: mA⟩
        | _ => ⟨mI, (.ofCExpr ce) :: mA⟩
  | _  => FailedState


def Whnf_3 : FlowState → FlowState
  | ⟨(.Whnf_3, bvarCtx) :: mI, (.ofCExpr f') :: (.ofList as) :: mA⟩ =>
        let ce2 := f'.beta_help as
        ⟨(.reduceMatcher?_1, bvarCtx) :: (.Whnf_4, bvarCtx) :: mI, (.ofCExpr ce2) :: (.ofCExpr ce2) :: mA⟩
  | _  => FailedState


def Whnf_4 (fctx : FixCtx) : FlowState → FlowState
  | ⟨(.Whnf_4, bvarCtx) :: mI, (.ofReduceMatcherResult info) :: (.ofCExpr ce2) :: mA⟩ =>
        match info with
        | .reduced eNew => ⟨(.Whnf_1, bvarCtx) :: mI, (.ofCExpr eNew) :: mA⟩
        | .partialApp   => ⟨mI, (.ofCExpr ce2) :: mA⟩
        | .stuck _      => ⟨mI, (.ofCExpr ce2) :: mA⟩
        | .notMatcher   =>
              let (h,args) := ce2.getApp
              match h with
              | .const n lvl =>
                    match fctx.cstData.find? n.toString with
                    | .none => ⟨mI, (.ofCExpr ce2) :: mA⟩
                    | .some info =>
                        match info with
                        | .recu ps _ re =>
                            ⟨(.reduceRec_1, bvarCtx) :: mI, (.ofName n) :: (.ofListName ps) :: (.ofcRecursorVal re) :: (.ofListLevel lvl) :: (.ofList args) :: (.ofCExpr ce2) :: mA⟩
                        | .quot _ _ qu =>
                            ⟨(.reduceQuotRec_1, bvarCtx) :: mI, (.ofQuotVal qu) :: (.ofList args) :: (.ofCExpr ce2)  :: mA⟩
                        | _ => ⟨mI, (.ofCExpr ce2) :: mA⟩
              | _ => ⟨mI, (.ofCExpr ce2) :: mA⟩
  | _  => FailedState

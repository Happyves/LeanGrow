
import LeanGrow.F.Data.CExpr.ReduceInferSmart.Iota

open Lean


partial def myWhnfCore
  (fctx : FixCtx) (bvarCtx : List CExpr) (ce : CExpr)
  (cexprInferType  cexprWhnf : FixCtx → List CExpr→ CExpr → CExpr) : CExpr :=
    match ce with
    | .forallE ..    => ce
    | .lam ..        => ce
    | .sort ..       => ce
    | .lit ..        => ce
    | .bvar ..       => ce
    | .lnode ..      => ce
    | .gnode ..      => ce
    | .const ..      => ce
    | .failed        => ce
    | .letE _ _ v b _ =>
        myWhnfCore fctx bvarCtx (CExpr.instantiateShift v b) cexprInferType  cexprWhnf
    | .app .. =>
        match ce.letFunAppArgs? with
        | .some (args, _, _, v, b) =>
            myWhnfCore fctx bvarCtx (CExpr.mkApp (CExpr.instantiateShift v b) args) cexprInferType  cexprWhnf
        | _ =>
            let (f,as) := ce.getApp
            let f' := myWhnfCore fctx bvarCtx f cexprInferType  cexprWhnf
            let ce2 := myWhnfCore fctx bvarCtx (f'.beta_help as) cexprInferType  cexprWhnf
            match (ce2.reduceMatcher? fctx bvarCtx cexprInferType  cexprWhnf) with
            | .reduced eNew => myWhnfCore fctx bvarCtx eNew cexprInferType  cexprWhnf
            | .partialApp   => ce2
            | .stuck _      => ce2
            | .notMatcher   =>
                  let (h,args) := ce2.getApp
                  match h with
                  | .const n lvl =>
                        match fctx.cstData.find? n.toString with
                        | .none => ce2
                        | .some info =>
                            match info with
                            | .recu ps _ re => CExpr.reduceRec fctx bvarCtx n ps re lvl args ce2 cexprInferType  cexprWhnf
                            | .quot _ _ qu => CExpr.reduceQuotRec fctx bvarCtx qu args ce2  cexprWhnf
                            | _ => ce2
                  | _ => ce2
    | .proj _ i c =>
        let c' := myWhnfCore fctx bvarCtx c cexprInferType  cexprWhnf
        match CExpr.projectCore? fctx.cstData c' i with
        | .some res => myWhnfCore fctx bvarCtx res cexprInferType  cexprWhnf
        | _ => ce


def cexprWhnfImp
  (fctx : FixCtx) (bvarCtx : List CExpr) (ce : CExpr)
  (cexprInferType  cexprWhnf : FixCtx → List CExpr→ CExpr → CExpr) : CExpr :=
  myWhnfCore fctx bvarCtx ce cexprInferType  cexprWhnf

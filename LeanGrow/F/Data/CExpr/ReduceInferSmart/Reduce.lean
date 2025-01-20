
import LeanGrow.F.Data.CExpr.ReduceInferSmart.Top

open Lean Meta


private def dumbUnfoldDefinition? (fctx : FixCtx) (e : CExpr) : Option CExpr :=
  match e with
  | .app _ _ =>
      let (f,as) := CExpr.getApp e
      match f with
      | .const n lvl =>
          match fctx.cstData.find? n.toString with
          | .some (.wVal us _ v) => .some (CExpr.mkApp (CExpr.instantiateLevelParams v us lvl) as) -- we don't beta since this is done by whnf core ??
          | _ => .none
      | _ => .none
  | _ => .none


#check Meta.reduceNative?
#check reduceNat?
-- we don't use ↑, though we should
partial def cexprWhnfDelta (fctx : FixCtx) (bvarCtx : List CExpr) (e : CExpr) : CExpr :=
  let red := cexprWhnf fctx bvarCtx e
  match dumbUnfoldDefinition? fctx red with
  | .none => e
  | .some new => cexprWhnfDelta fctx bvarCtx new

def cexprWhnfDeltaOnce (fctx : FixCtx) (bvarCtx : List CExpr) (e : CExpr) : CExpr :=
  let red := cexprWhnf fctx bvarCtx e
  match dumbUnfoldDefinition? fctx red with
  | .none => e
  | .some new => cexprWhnf fctx bvarCtx new


partial def cexprReduce (fctx : FixCtx) (bvarCtx : List CExpr) (e : CExpr) : CExpr :=
  let T := cexprWhnf fctx bvarCtx (cexprInferType fctx bvarCtx e)
  match T with
  | .sort .zero => e
  | _ =>
    let E := cexprWhnfDelta fctx bvarCtx e
    match E with
    | .app f a => .app (cexprReduce fctx bvarCtx f) (cexprReduce fctx bvarCtx a)
    | .lam n t b i => .lam n t (cexprReduce fctx (t :: bvarCtx) b) i
    | .forallE n t b i => .forallE n t (cexprReduce fctx (t :: bvarCtx) b) i
    | .proj n i a => .proj n i (cexprReduce fctx bvarCtx a)
    | x => x

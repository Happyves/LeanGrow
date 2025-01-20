
import LeanGrow.F.Data.CExpr.ReduceInferSmart.Top

open Lean


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


#check Meta.reduceNative? -- next
#check Meta.reduce -- goal

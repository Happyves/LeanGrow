
import LeanGrow.F.Data.CExpr.ReduceInfer.BetaZeta
import LeanGrow.F.Data.CExpr.ReduceInfer.Iota
import LeanGrow.F.Data.CExpr.ReduceInfer.Magic

open Lean


partial def myWhnfCore
  (fctx : FixCtx) (bvarCtx : List CExpr) (ce : CExpr) : CExpr :=
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
        myWhnfCore fctx bvarCtx (CExpr.instantiateShift v b)
    | .app .. =>
        match ce.letFunAppArgs? with
        | .some (args, _, _, v, b) =>
            myWhnfCore fctx bvarCtx (CExpr.mkApp (CExpr.instantiateShift v b) args)
        | _ =>
            let (f,as) := ce.getApp
            let f' := myWhnfCore fctx bvarCtx f
            let ce2 := f'.beta_help as
            match (ce2.reduceMatcher? fctx bvarCtx) with
            | .reduced eNew => myWhnfCore fctx bvarCtx eNew
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
                            | .recu ps _ re => CExpr.reduceRec fctx bvarCtx n ps re lvl args ce2
                            | .quot _ _ qu => CExpr.reduceQuotRec fctx bvarCtx qu args ce2
                            | _ => ce2
                  | _ => ce2
    | .proj _ i c =>
        let c' := myWhnfCore fctx bvarCtx c
        match CExpr.projectCore? fctx.cstData c' i with
        | .some res => myWhnfCore fctx bvarCtx res
        | _ => ce


@[export lean_my_whnf]
def cexprWhnfImp
  (fctx : FixCtx) (bvarCtx : List CExpr) (ce : CExpr) : CExpr :=
  myWhnfCore fctx bvarCtx ce

/-
We just don't do delta.
It's something that is only required for unification, at wich stage
the solution is to, at a mismatch, prefrom one delta, and then reduce
again.
-/

@[export lean_my_test]
def myTestExternExportImp : Nat → Nat := Nat.succ

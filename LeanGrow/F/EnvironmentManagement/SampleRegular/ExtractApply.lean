


import LeanGrow.F.EnvironmentManagement.SampleRegular.API

open Lean Meta


def extractApply_main (proof : Expr) : MetaM (Option Name × List Expr) := do
  match proof with
  | .app _ _ =>
      let (h,as) := proof.getAppFnArgs
      if h == `Name.anonymous -- example, if (h : ∀ ...) in context, head of application can be fvar
      then
        let args ← getRelevantArgsOTerms as
        return (.none, args)
      else
        let args ← getRelevantArgsOTerms as
        return (.some h, args)
  | _ => return (.none,[])

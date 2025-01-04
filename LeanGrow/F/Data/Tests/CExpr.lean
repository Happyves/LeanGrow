
import LeanGrow.F.Data.CExpr.API
import Lean

open Lean Elab

#check Term.elabTermAndSynthesize
#check `(term| 1+1)

#eval ((do
  let s ← `(term| (1+1)+ (2*2))
  let e ← Term.elabTermAndSynthesize s .none
  IO.println s!"Real :\n{repr e}"
  IO.println s!"C :\n{repr (Lean.Expr.toCExprF e)}"
  ): TermElabM Unit)


#eval ((do
  let s ← `(term| ∀ x : Nat, (1+1)+ (2*2))
  let e ← Term.elabTermAndSynthesize s .none
  IO.println s!"Real :\n{repr e}"
  IO.println s!"C :\n{repr (Lean.Expr.toCExprF e)}"
  ): TermElabM Unit)

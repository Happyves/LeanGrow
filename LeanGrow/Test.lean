
import Mathlib
import Lean
import Qq


open Lean Qq


#exit


#eval q(∀ β : Type 0, [Inhabited β] → default)

#eval q(∀ β : Type 0, [Add β] → ∀ x y : β, x+y = y+x → True)

#eval q(@List.reverse Nat)

#check HAdd.hAdd


set_option pp.all true in
#print add_comm

#eval q(fun {G : Type 1} [inst : AddCommMagma.{1} G] ↦ @AddCommMagma.add_comm.{1} G inst)



elab "inst_in_ltx" :tactic => do
  let ltx ← getLCtx
  for d in ltx.decls do
    IO.println s!"{((FVarId.name ∘ LocalDecl.fvarId )<$> d)} type : {(LocalDecl.type <$> d)}\n"

set_option linter.unusedVariables false

example (β : Type 0) [Add β] (h : ∀ x y : β, x+y = y+x) : True :=
  by
  inst_in_ltx -- linter prevents messages from being stored, somehow ??
  trivial

example  (h : 1+2 = 3) : True :=
  by
  inst_in_ltx
  trivial

#check instAddNat

#eval q(Prop)

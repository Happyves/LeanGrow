
import LeanGrow.F.Data.RExprTests.API
import  LeanGrow.F.Data.CExpr.Types

open Lean


#check Eq.rec

#check fun n : Nat => Eq.refl n

#check fun n : 2+2=4 => n

#check fun n : Unit → 2+2=4 => n ()
#check (Unit → 2 + 2 = 4) → 2 + 2 = 4

#check let p : 2+2=4 := rfl ; p

/-
To check if a term is a proof, without using inferType, we could:
- for applications, get head, check that it's type is an forall with a Prop head
- lams are if there body is ; we should also check if the binder is a Prop
  (function app with const at head who's type is Prop.headed ; forall with a Prop head)
  so that we get corect answer in `fun n : 2+2=4 => n`
  Similar situation for let ?
- forall aren't terms
- for lnodes and gnodes, we'll need a context...

-/



import Lean
import Mathlib.Tactic.Convert
import Mathlib.Tactic.CongrM

open Lean


#check Lean.Elab.Tactic.Lean.Elab.Tactic.evalCongr

-- congr calls
#check MVarId.congrN

--convert is
#check MVarId.convert
-- which boils down to
#check MVarId.congrN!



/-

congrN
| Eq.refl
| HEq.refl
| fvar
| heq_of_eq? congrN
| implies_congr congrN congrN
| eq_of_heq? ((fun _ => (bvar 0) (terms <|> mvars)*) hcongrThmApp)
| ((fun _ => (bvar 0) (terms <|> mvars)*) congrThmApp)


hcongrThmApp
| hcongrThm term*
-- term will contain subexpressions being congred, and then proofs of equalities of these terms

hcongrThm
| Eq.refl
| HEq.refl
| fun _ => Eq.ndrec motive hcongrThm (eq_of_heq? bvar)

congrThmApp
| congrThm term*
-- term will contain subexpressions being congred, and then proofs of equalities of these terms

congrThm
| Eq.refl
| fun _ => Eq.rec motive congrThm (bvars*)
| fun _ => Eq.ndrec motive congrThm (Subsingleton.elim bvar bvar)
-- unclear on `Meta.mkCongrSimpCore?` ... uses subts in some cases ...



convert
| (Eq.mp <|> Eq.mpr) congrN! term


congrN!
| Eq.refl
| fvar
| heq_of_eq? congrN!
| iff_of_eq? congrN!
| proof_irrel_heq? congrN!
| propext congrN!
| term congrN!* -- user lemma
| eq_of_heq? ((fun _ => (bvar 0) (terms <|> mvars)*) smartHcongrThmApp)
| Lean.Meta.FastSubsingleton.helim ((Eq.symm <|> HEq.symm)? congrN!)
| lawful_beq_subsingleton
| funext congrN!
| Function.hfunext congrN!
| implies_congr' congrN!
| pi_congr congrN!



-/


#check Eq.ndrec
#check Lean.Meta.FastSubsingleton.helim
#check lawful_beq_subsingleton
#check funext
#check Function.hfunext
#check pi_congr
#check_failure implies_congr' --private
#check implies_congr


#check Meta.mkCongrSimpCore?
#check Meta.mkHCongr


theorem test_1 (n m k : Nat) : n + m - k = k + m - n := by
  congr
  all_goals sorry


#print test_1


def testh (n : Nat) (x : Fin n) : Nat := sorry


theorem test_2 (n m : Nat) (x : Fin n) (y : Fin m ) : testh n x = testh m y := by
  congr
  all_goals sorry


#print test_2


theorem test_3 (n m : Nat) (x : Fin n) (y : Fin m ) : testh n x = testh m y := by
  congr!
  all_goals sorry

#print test_3

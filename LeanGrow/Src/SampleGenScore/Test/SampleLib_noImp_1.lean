

import LeanGrow.Src.SampleGenScore.Test.SampleForw
import LeanGrow.Src.SampleGenScore.Test.SampleBack

import Mathlib.Data.List.Lemmas

import Mathlib.Combinatorics.Nullstellensatz
import Mathlib.Combinatorics.Additive.Randomisation
import Mathlib.Combinatorics.Additive.ErdosGinzburgZiv

import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Factors

open Lean Meta

set_option linter.style.longLine false



def testNoDelZet (printLift? : Bool) (thmName : Name) (depthDig depthStart depthStop : Nat) : MetaM Unit := do
  testNoDelZet_B printLift? thmName depthDig depthStart depthStop
  testNoDelZet_F printLift? thmName depthDig depthStart depthStop
  testNoDelZet_wH_F printLift? thmName depthDig depthStart depthStop

def testDelZet (printLift? : Bool) (thmName : Name)
  (depthDig depthStart depthStop deltaFuel zetaFuel : Nat) : MetaM Unit := do
  testDelZet_B printLift? thmName depthDig depthStart depthStop deltaFuel zetaFuel
  testDelZet_F printLift? thmName depthDig depthStart depthStop deltaFuel zetaFuel
  testNoDelZet_wH_F printLift? thmName depthDig depthStart depthStop


#check 1

#print List.Subset.dedup_append_right

-- #eval testNoDelZet false `List.Subset.dedup_append_right 1 2 2

#check List.Subset.union_eq_right
#check List.Subset.trans
#check List.subset_dedup


#check List.filter_comm

-- #eval testNoDelZet false `List.filter_comm 1 2 2

-- #eval testDelZet false `List.filter_comm 1 2 2 2 2
-- no difference because it's a simp

#check List.filter_eq_foldr

-- tracing_mode .std
-- tracing_flags [(`sampleCoreForw, TracingFlags.all),
--                ]

-- #eval testNoDelZet false `List.filter_eq_foldr 1 2 2


#check List.length_erase_add_one

-- #eval testNoDelZet false `List.length_erase_add_one 1 2 2

-- #eval testDelZet false `List.length_erase_add_one 1 2 2 2 2
-- **fix** delta should do something here ?!?

#check List.forall_map_iff

-- #eval testNoDelZet false `List.forall_map_iff 1 2 2


#check List.Forall.imp


-- #eval testNoDelZet false `List.Forall.imp 1 2 2


#print List.disjoint_pmap

-- #eval testNoDelZet false `List.disjoint_pmap 1 2 2


#check List.Perm.disjoint_right


-- #eval testNoDelZet false `List.Perm.disjoint_right 1 2 2


#check List.range'_0


-- #eval testNoDelZet false `List.range'_0 1 2 2


#check List.left_le_of_mem_range'


-- #eval testNoDelZet false `List.left_le_of_mem_range' 1 2 2


#check List.map_erase


-- #eval testNoDelZet false `List.map_erase 1 2 2


#print  List.injOn_insertIdx_index_of_notMem


-- #eval testNoDelZet false `List.injOn_insertIdx_index_of_notMem 1 2 2


#print List.injOn_insertIdx_index_of_notMem._simp_1_4


#check List.foldr_range_subset_of_range_subset


-- #eval testNoDelZet false `List.foldr_range_subset_of_range_subset 1 2 2

#check MvPolynomial.combinatorial_nullstellensatz_exists_eval_nonzero

-- #eval testNoDelZet false `MvPolynomial.combinatorial_nullstellensatz_exists_eval_nonzero 1 2 2

-- #eval testDelZet false `MvPolynomial.combinatorial_nullstellensatz_exists_eval_nonzero 1 2 2 2 2
-- 10ish sec ...


#check MvPolynomial.eq_zero_of_eval_zero_at_prod_finset


-- #eval testNoDelZet false `MvPolynomial.eq_zero_of_eval_zero_at_prod_finset 1 2 2
-- only 5 sec !

#check AddDissociated.randomisation

-- #eval testNoDelZet false `AddDissociated.randomisation 1 2 2

#check Int.erdos_ginzburg_ziv

-- #eval testNoDelZet false `Int.erdos_ginzburg_ziv 1 2 2
-- doesn't treat `Nat.prime_composite_induction` as a induction because it hasn't been given any attributes !


#check Nat.gcd_greatest

-- #eval testNoDelZet false `Nat.gcd_greatest 1 2 2

-- #eval testNoDelZet false `Nat.gcd_greatest 1 4 4


#check Nat.dvd_lcm_of_dvd_left

-- #eval testNoDelZet false `Nat.dvd_lcm_of_dvd_left 1 2 2

#check Nat.coprime_mul_right_add_right


-- #eval testNoDelZet false `Nat.coprime_mul_right_add_right 1 2 2
-- **fix** no iff refl ...

#check Nat.pow_sub_one_mod_pow_sub_one



-- #eval testNoDelZet false `Nat.pow_sub_one_mod_pow_sub_one 1 2 2
-- **fix** review after blacklisting omega ; undesired Eq.mpr backward samples

#check Nat.pow_sub_one_gcd_pow_sub_one

-- #eval testNoDelZet false `Nat.pow_sub_one_gcd_pow_sub_one 1 2 2
-- **fix** undesired duplication of induction hypothesis ...

#check Nat.coprime_pow_left_iff

-- #eval testNoDelZet false `Nat.coprime_pow_left_iff 1 2 2


#check Nat.Coprime.mul_add_mul_ne_mul

-- #eval testNoDelZet false `Nat.Coprime.mul_add_mul_ne_mul 1 2 2
-- **fix** terms in obtain seemingly not sampled ?

#check Nat.div_lcm_eq_div_gcd

-- #eval testNoDelZet false `Nat.div_lcm_eq_div_gcd 1 2 2
-- **fix** have ∨ hyp at backward Or.casesOn sample

#check Nat.prod_primeFactorsList

-- #eval testNoDelZet false `Nat.prod_primeFactorsList 1 2 2
-- **fix** undesired duplication of induction hypothesis ...



#check Nat.primeFactorsList_prime

-- #eval testNoDelZet false `Nat.primeFactorsList_prime 1 2 2

-- #eval testDelZet false `Nat.primeFactorsList_prime 1 2 2 2 2
-- **fix** duplication of hyp Nat.Prime p → 2 ≤ p ∧ p.minFac = p

#check Nat.primeFactorsList_eq_nil

-- #eval testNoDelZet false `Nat.primeFactorsList_eq_nil 1 2 2



#check Nat.mem_primeFactorsList_iff_dvd

-- #eval testNoDelZet false `Nat.mem_primeFactorsList_iff_dvd 1 2 2



#check Nat.primeFactorsList_unique

-- #eval testNoDelZet false `Nat.primeFactorsList_unique 1 2 2



#check Nat.eq_prime_pow_of_unique_prime_dvd

-- #eval testNoDelZet false `Nat.eq_prime_pow_of_unique_prime_dvd 1 2 2
-- **fix** bad rfl back samples


#check Nat.replicate_subperm_primeFactorsList_iff

-- #eval testNoDelZet false `Nat.replicate_subperm_primeFactorsList_iff 1 2 2
-- **fix** induc Nat.recAux should have generalised b in goal ???

#check Nat.dvd_of_primeFactorsList_subperm

-- #eval testNoDelZet false `Nat.dvd_of_primeFactorsList_subperm 1 2 2

-- #eval testDelZet false `Nat.dvd_of_primeFactorsList_subperm 1 2 2 2 2
-- **fix** hyp duplication

#print Nat.four_dvd_or_exists_odd_prime_and_dvd_of_two_lt

-- #eval testNoDelZet false `Nat.four_dvd_or_exists_odd_prime_and_dvd_of_two_lt 1 2 2
-- contradictions not sampled, as desired ... for now ...


-- tracing_mode .std
-- tracing_flags [(`delabTopBack, TracingFlags.all),
--                 (`delab_simpGoal, TracingFlags.all)
--                ]


/-
Todo:
- prohibit Lean.Omega
- discard Iff.refl wrt ↓, as for Eq.refl
  (also at sample, at same location as for test if private)
- at `Coprime.mul_add_mul_ne_mul` terms in obtain seemingly not sampled
- at `div_lcm_eq_div_gcd`, rcases on term (not fv) seems to cause term
  to be ignored (at least, as a hyp)
- `eq_prime_pow_of_unique_prime_dvd` weird rfl samples
- `replicate_subperm_primeFactorsList_iff` generalising induction
  doesn't seem to do reverts in motive ??
- delta in `length_erase_add_one`
- `primeFactorsList_prime`delta seems to cause hyp duplication


-/

#check Iff.refl
#check Iff.rfl

#check Omega.LinearCombo.coordinate

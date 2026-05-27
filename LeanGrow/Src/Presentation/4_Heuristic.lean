

import LeanGrow.Src.Presentation.Z_help_heuristic



-- # Generalisation heuristic: core

/-
Motivation

- Task : tell if using theorem in next search step is a good idea

- Collect data triplets (theorem, goal, hyps) from library of proofs

- At search, consider theorem a good step to explore if search goal
  *resembles* goals from data where theorem occured

- Resemblence will be non-assigning unification with a path index
  that merges and generalizes the goals from data


Generalisation procedure on path index:

- Leave frequent sub-expressions as is

- For infrequent ones, infer type and seek frequent types

- Replace infrequent expressions with frequent type
  by an mvar of that type

-/



def test_1 := testGen
  (fun w tot _ T _ => (w.toFloat / tot.toFloat ≥ 0.33) && (T != .sort 0))
  (fun w tot _ _ => (w.toFloat / tot.toFloat ≥ 0.5))
  `Test1


With context (n : Nat) (m : Nat) and objects (Nat.add n m), (Nat.sub n m), (Nat.mul n m) run test_1


def test_2 := testGen
  (fun w tot _ T _ => (w.toFloat / tot.toFloat ≥ 0.33) && (T != .sort 0))
  (fun w tot _ _ => (w.toFloat / tot.toFloat ≥ 0.33))
  `Test1


With context (n : Nat) (m : Nat) and objects (Nat.add n m), (Nat.sub n m), (Nat.mul n m) run test_2



tracing_mode .std
tracing_flags [(`generalizePaInCore, TracingFlags.all),
               ]

With context (n : Nat) (m : Nat) and objects (Nat.add n m), (Nat.sub n m), (Nat.mul n m) run test_1


/-
Aspects:

- Mvar garbadge collection: there could be mvars originating from
  generalization that have been further generalized and aren't
  referenced by the path index anymore

- Mvar reuse: use as few mvars as needed in this process ;
  very tricky, still in research state


-/



import LeanGrow.Src.Data.PathIndex.Testing.InsertBuild


-- # Path indexing

/-
Path Indexes (Indices ?):

- Stores set of syntax trees efficiently, like discrimination trees

- Main use is the heuristic we present next

-/


#print Lean.Expr

With context (n : Nat) (f : Nat → Nat) and objects Nat, f n, (fun x : Nat => x) run testInsertPres

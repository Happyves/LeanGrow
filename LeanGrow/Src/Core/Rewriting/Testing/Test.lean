

/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/


import LeanGrowBeta.Core.Rewriting.TestTools


open Lean Meta

universe u v w



def testBackRWA := testBackRW `Nat.add_comm

With gnodes (n : Nat) (m : Nat) and unodes and tnodes and objects (m+n = 0) run testBackRWA

With gnodes (n : Nat) (m : Nat) (x : Fin (n+m)) (P : (k : Nat) → Fin k → Prop) and unodes and tnodes and objects (P (n+m) x) run testBackRWA

With gnodes and unodes and tnodes and objects ((fun x y : Nat => x + y) = (fun x y => x*y)) run testBackRWA

With gnodes and unodes and tnodes and objects ((fun x y : Nat => x + y) = (fun x y => x + y)) run testBackRWA

With gnodes and unodes and tnodes and objects ((fun x y : Nat => x + y) = (fun x y => y + x)) run testBackRWA

structure LFin (n : Nat) where
  val : Nat
  prop : val ≤ n

With gnodes (n : Nat) (m : Nat) (P : (k : Nat) → LFin k → Prop) and unodes and tnodes and objects (P (n+m) ⟨0,(by apply Nat.zero_le)⟩) run testBackRWA

With gnodes (n :  Nat) (P : (k : Nat) → Fin k → Prop) and unodes and tnodes and objects (P (n+1) ⟨0,(by apply Nat.zero_lt_of_ne_zero ; apply Nat.add_one_ne_zero)⟩) run testBackRWA

With gnodes (n :  Nat) (x : Fin (n+1)) (P : (k : Nat) → Fin k → Prop) and unodes and tnodes and objects (P (n+1) (x + ⟨0,(by apply Nat.zero_lt_of_ne_zero ; apply Nat.add_one_ne_zero)⟩)) run testBackRWA

set_option pp.proofs true in
With gnodes (P : (k : Nat) → Fin k → Prop) and unodes and tnodes and objects ((fun (n : Nat)  => P (n+1) ⟨0,(by apply Nat.zero_lt_of_ne_zero ; apply Nat.add_one_ne_zero)⟩) = (fun _ => True)) run testBackRWA
-- this was a failure in alpha too !!!


With gnodes (P : (k : Nat) → Fin k → Prop) and unodes and tnodes and objects ((fun (n : Nat) (x : Fin (n+1)) => P (n+1) x) 41 (⟨0, by decide⟩ : Fin 42)) run testBackRWA
/- *negative example*
This fails because the type of the term rewritten under a binder depends on the rewrite.
Here, with free var `n`, the term `(fun (x : Fin (n+1)) => P (n+1) x) = (fun (x : Fin (1+n)) => P (n+1) x)`
isn't correct because the sides have different types.

For beta: get this to work with HEq somehow ?
-/

With gnodes (n : Nat) (m : Nat) (x : Fin (n+m)) (P : (k : Nat) → Fin k → Prop) and unodes (y : Fin (n+m) : x+x) and tnodes and objects (P (n+m) y) run testBackRWA

With gnodes (n : Nat) (m : Nat) (P : (k : Nat) → Fin k → Prop) and unodes and tnodes (t : m < n+1) and objects (P (n+1) ⟨m,t⟩) run testBackRWA

With gnodes (n : Nat) (P : (k : Nat) → Fin k → Prop) and unodes (y : Fin (n+1) : (⟨0, by apply Nat.zero_lt_of_ne_zero ; apply Nat.add_one_ne_zero⟩ : Fin (n+1))) and tnodes and objects (P (n+1) y) run testBackRWA
-- note for future tests : elaborating unodes may require type ascriptions

With gnodes (n : Nat) (x : Fin (n+1)) (P : (k : Nat) → Fin k → Prop) and unodes (y : Fin (n+1) : x+x) and tnodes (t : y.val + 1 < n+1) and objects (P (n+1) ⟨y.val + 1, t⟩) run testBackRWA


With gnodes and unodes (y : Nat : 42) and tnodes and objects ((fun x : Nat => x + y) = (fun x => y + x)) run testBackRWA

set_option pp.funBinderTypes true in
With gnodes (n : Nat) and unodes and tnodes and objects ((fun x y : Fin (n+1) => x + y) = (fun x y => x*y)) run testBackRWA
-- first occurence of applicable add_comm is in th binding type

set_option pp.proofs true in
With gnodes (n : Nat) and unodes and tnodes and objects ((fun (x : Fin (n+1)) (h : 0 < (n+1)) => x + ⟨0,h⟩) = ((fun (x : Fin (n+1)) (h : 0 < (n+1)) => x + ⟨0,h⟩))) run testBackRWA

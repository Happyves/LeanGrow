

/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/


import LeanGrow.Src.Core.Rewriting.TestTools


open Lean Meta

universe u v w



def testBackRWA := testBackRW_sandBox_noSub `Nat.add_comm

def testBackRWB := testBackRW_sandBox_wiSub `Nat.add_comm

def testBackRWC := testForwRW_sandBox `Nat.add_comm


-- With context g(n : Nat) g(m : Nat) and objects (m+n = 0) run testBackRWA

-- With context g(n : Nat) g(m : Nat) and objects (m+n = 0) run testBackRWB

-- With context g(n : Nat) g(m : Nat) and objects (m+n = 0) run testBackRWC



-- With context g(n : Nat) g(m : Nat) g(x : Fin (n+m)) g(P : (k : Nat) → Fin k → Prop) and objects (P (n+m) x) run testBackRWA

-- With context g(n : Nat) g(m : Nat) g(x : Fin (n+m)) g(P : (k : Nat) → Fin k → Prop) and objects (P (n+m) x) run testBackRWB

-- With context g(n : Nat) g(m : Nat) g(x : Fin (n+m)) g(P : (k : Nat) → Fin k → Prop) and objects (P (n+m) x) run testBackRWC

-- With context g(n : Nat) g(m : Nat) g(h : n+m > 0) g(P : (k : Nat) → k > 0 → Prop) and objects (P (n+m) h) run testBackRWC



-- With context and objects ((fun x y : Nat => x + y) = (fun x y => x*y)) run testBackRWA

-- With context and objects ((fun x y : Nat => x + y) = (fun x y => x*y)) run testBackRWB

-- With context and objects ((fun x y : Nat => x + y) = (fun x y => x*y)) run testBackRWC



-- With context and objects ((fun x y : Nat => x + y) = (fun x y => x + y)) run testBackRWA

-- With context and objects ((fun x y : Nat => x + y) = (fun x y => x + y)) run testBackRWB

-- With context and objects ((fun x y : Nat => x + y) = (fun x y => x + y)) run testBackRWC



-- With context and objects ((fun x y : Nat => x + y) = (fun x y => y + x)) run testBackRWA

-- With context and objects ((fun x y : Nat => x + y) = (fun x y => y + x)) run testBackRWB

-- With context and objects ((fun x y : Nat => x + y) = (fun x y => y + x)) run testBackRWC




structure LFin (n : Nat) where
  val : Nat
  prop : val ≤ n

-- With context g(n : Nat) g(m : Nat) g(P : (k : Nat) → LFin k → Prop) and objects (P (n+m) ⟨0,(by apply Nat.zero_le)⟩) run testBackRWA

-- With context g(n : Nat) g(m : Nat) g(P : (k : Nat) → LFin k → Prop) and objects (P (n+m) ⟨0,(by apply Nat.zero_le)⟩) run testBackRWB

-- With context g(n : Nat) g(m : Nat) g(P : (k : Nat) → LFin k → Prop) and objects (P (n+m) ⟨0,(by apply Nat.zero_le)⟩) run testBackRWC


-- With context g(n :  Nat) g(P : (k : Nat) → Fin k → Prop) and objects (P (n+1) ⟨0,(by apply Nat.zero_lt_of_ne_zero ; apply Nat.add_one_ne_zero)⟩) run testBackRWA

-- With context g(n :  Nat) g(P : (k : Nat) → Fin k → Prop) and objects (P (n+1) ⟨0,(by apply Nat.zero_lt_of_ne_zero ; apply Nat.add_one_ne_zero)⟩) run testBackRWB

-- With context g(n :  Nat) g(P : (k : Nat) → Fin k → Prop) and objects (P (n+1) ⟨0,(by apply Nat.zero_lt_of_ne_zero ; apply Nat.add_one_ne_zero)⟩) run testBackRWC


-- With context g(n :  Nat) g(x : Fin (n+1)) g(P : (k : Nat) → Fin k → Prop) and objects (P (n+1) (x + ⟨0,(by apply Nat.zero_lt_of_ne_zero ; apply Nat.add_one_ne_zero)⟩)) run testBackRWA

-- With context g(n :  Nat) g(x : Fin (n+1)) g(P : (k : Nat) → Fin k → Prop) and objects (P (n+1) (x + ⟨0,(by apply Nat.zero_lt_of_ne_zero ; apply Nat.add_one_ne_zero)⟩)) run testBackRWB

-- With context g(n :  Nat) g(x : Fin (n+1)) g(P : (k : Nat) → Fin k → Prop) and objects (P (n+1) (x + ⟨0,(by apply Nat.zero_lt_of_ne_zero ; apply Nat.add_one_ne_zero)⟩)) run testBackRWC


-- With context g(P : (k : Nat) → Fin k → Prop) and objects ((fun (n : Nat)  => P (n+1) ⟨0,(by apply Nat.zero_lt_of_ne_zero ; apply Nat.add_one_ne_zero)⟩) = (fun _ => True)) run testBackRWA

-- With context g(P : (k : Nat) → Fin k → Prop) and objects ((fun (n : Nat)  => P (n+1) ⟨0,(by apply Nat.zero_lt_of_ne_zero ; apply Nat.add_one_ne_zero)⟩) = (fun _ => True)) run testBackRWB

-- With context g(P : (k : Nat) → Fin k → Prop) and objects ((fun (n : Nat)  => P (n+1) ⟨0,(by apply Nat.zero_lt_of_ne_zero ; apply Nat.add_one_ne_zero)⟩) = (fun _ => True)) run testBackRWC


-- With context g(P : (k : Nat) → Fin k → Prop) and objects ((fun (n : Nat) (x : Fin (n+1)) => P (n+1) x) = (fun (n : Nat) (x : Fin (n+1)) => 2+2=4)) run testBackRWA
/- Issue is that the first occurence is the the type of the equality, where the
pattern is present under a binder and our approach fails. Should work if we take
the expected occurece with n ?
-/

-- With context g(P : (k : Nat) → Fin k → Prop) and objects ((fun (n : Nat) (x : Fin (n+1)) => P (n+1) x) = (fun (n : Nat) (x : Fin (n+1)) => 2+2=4)) run testBackRWB

-- With context g(P : (k : Nat) → Fin k → Prop) and objects ((fun (n : Nat) (x : Fin (n+1)) => P (n+1) x) = (fun (n : Nat) (x : Fin (n+1)) => 2+2=4)) run testBackRWC



-- With context g(n : Nat) g(m : Nat) g(x : Fin (n+m)) g(P : (k : Nat) → Fin k → Prop) u(y : Fin (n+m) : x+x) and objects (P (n+m) y) run testBackRWA

-- With context g(n : Nat) g(m : Nat) g(x : Fin (n+m)) g(P : (k : Nat) → Fin k → Prop) u(y : Fin (n+m) : x+x) and objects (P (n+m) y) run testBackRWB

-- With context g(n : Nat) g(m : Nat) g(x : Fin (n+m)) g(P : (k : Nat) → Fin k → Prop) u(y : Fin (n+m) : x+x) and objects (P (n+m) y) run testBackRWC


-- With context g(n : Nat) g(m : Nat) g(P : (k : Nat) → Fin k → Prop) g(t : m < n+1) and objects (P (n+1) ⟨m,t⟩) run testBackRWA

-- With context g(n : Nat) g(m : Nat) g(P : (k : Nat) → Fin k → Prop) g(t : m < n+1) and objects (P (n+1) ⟨m,t⟩) run testBackRWB

-- With context g(n : Nat) g(m : Nat) g(P : (k : Nat) → Fin k → Prop) g(t : m < n+1) and objects (P (n+1) ⟨m,t⟩) run testBackRWC


-- With context g(n : Nat) g(P : (k : Nat) → Fin k → Prop) u(y : Fin (n+1) : (⟨0, by apply Nat.zero_lt_of_ne_zero ; apply Nat.add_one_ne_zero⟩ : Fin (n+1))) and objects (P (n+1) y) run testBackRWA

-- With context g(n : Nat) g(P : (k : Nat) → Fin k → Prop) u(y : Fin (n+1) : (⟨0, by apply Nat.zero_lt_of_ne_zero ; apply Nat.add_one_ne_zero⟩ : Fin (n+1))) and objects (P (n+1) y) run testBackRWB

-- With context g(n : Nat) g(P : (k : Nat) → Fin k → Prop) u(y : Fin (n+1) : (⟨0, by apply Nat.zero_lt_of_ne_zero ; apply Nat.add_one_ne_zero⟩ : Fin (n+1))) and objects (P (n+1) y) run testBackRWC


-- With context g(n : Nat) g(x : Fin (n+1)) g(P : (k : Nat) → Fin k → Prop) u(y : Fin (n+1) : x+x)  t(37 : 67 : t : y.val + 1 < n+1) and objects (P (n+1) ⟨y.val + 1, t⟩) run testBackRWA

-- With context g(n : Nat) g(x : Fin (n+1)) g(P : (k : Nat) → Fin k → Prop) u(y : Fin (n+1) : x+x)  t(37 : 67 : t : y.val + 1 < n+1) and objects (P (n+1) ⟨y.val + 1, t⟩) run testBackRWB

-- With context g(n : Nat) g(x : Fin (n+1)) g(P : (k : Nat) → Fin k → Prop) u(y : Fin (n+1) : x+x)  t(37 : 67 : t : y.1 + 1 < n+1) and objects (P (n+1) ⟨y.1 + 1, t⟩) run testBackRWA



-- With context u(y : Nat : 42) and objects ((fun x : Nat => x + y) = (fun x => y + x)) run testBackRWA

-- With context u(y : Nat : 42) and objects ((fun x : Nat => x + y) = (fun x => y + x)) run testBackRWB

-- With context u(y : Nat : 42) and objects ((fun x : Nat => x + y) = (fun x => y + x)) run testBackRWC


-- set_option pp.funBinderTypes true in
-- With context g(n : Nat) and objects ((fun x y : Fin (n+1) => x + y) = (fun x y => x*y)) run testBackRWA
-- first occurence of applicable add_comm is in th binding type

-- With context g(n : Nat) and objects ((fun x y : Fin (n+1) => x + y) = (fun x y => x*y)) run testBackRWB

-- With context g(n : Nat) and objects ((fun x y : Fin (n+1) => x + y) = (fun x y => x*y)) run testBackRWC


-- With context g(n : Nat) and objects ((fun (x : Fin (n+1)) (h : 0 < (n+1)) => x + ⟨0,h⟩) = ((fun (x : Fin (n+1)) (h : 0 < (n+1)) => x + ⟨0,h⟩))) run testBackRWA

-- With context g(n : Nat) and objects ((fun (x : Fin (n+1)) (h : 0 < (n+1)) => x + ⟨0,h⟩) = ((fun (x : Fin (n+1)) (h : 0 < (n+1)) => x + ⟨0,h⟩))) run testBackRWB

-- With context g(n : Nat) and objects ((fun (x : Fin (n+1)) (h : 0 < (n+1)) => x + ⟨0,h⟩) = ((fun (x : Fin (n+1)) (h : 0 < (n+1)) => x + ⟨0,h⟩))) run testBackRWC



-- With context and objects ((fun (x y : Nat) (h : x = 42) => x + y) = (fun (x y : Nat) (h : x = 42) => x*y)) run testBackRWA

-- With context and objects ((fun (x y : Nat) (h : x = 42) => x + y) = (fun (x y : Nat) (h : x = 42) => x*y)) run testBackRWB



-- With context g(n : Nat) g(P : Nat → Prop) and objects (P (⟨0, Nat.zero_lt_succ n⟩ : Fin (n+1)).val) run testBackRWA
-- not found because reduce turns it to 0

-- With context g(n : Nat) g(P : {k : Nat} → Fin k → Prop) and objects (P (⟨0, Nat.zero_lt_succ n⟩ : Fin (n+1))) run testBackRWA

-- With context g(n : Nat) g(P : {k : Nat} → Fin k → Prop) and objects (P (⟨0, Nat.zero_lt_succ n⟩ : Fin (n+1))) run testBackRWB

-- With context g(n : Nat) g(P : {k : Nat} → Fin k → Prop) and objects (P (⟨0, Nat.zero_lt_succ n⟩ : Fin (n+1))) run testBackRWC


-- With context g(n : Nat) g(P : (k : Nat) → Fin k → Prop) g(x : Fin n.succ) and objects (P (n+1) x) run testBackRWA

-- With context g(n : Nat) g(P : (k : Nat) → Fin k → Prop) g(x : Fin n.succ) and objects (P (n+1) x) run testBackRWB

-- With context g(n : Nat) g(P : (k : Nat) → Fin k → Prop) g(x : Fin n.succ) and objects (P (n+1) x) run testBackRWC


-- With context g(n : Nat) g(P : (k : Nat) → (y : Fin k) → y = y → Prop) g(x : Fin n.succ) and objects (P (n+1) x (Eq.refl x)) run testBackRWA

-- With context g(n : Nat) g(P : (k : Nat) → (y : Fin k) → y = y → Prop) g(x : Fin n.succ) and objects (P (n+1) x (Eq.refl x)) run testBackRWB

-- With context g(n : Nat) g(P : (k : Nat) → (y : Fin k) → y = y → Prop) g(x : Fin n.succ) and objects (P (n+1) x (Eq.refl x)) run testBackRWC




#check Nat.zero_lt_succ
#check Nat.succ_eq_add_one


-- With context g(n : Nat) g(m : Nat) and objects (∀  x : Fin (n+m), x.val = 42) run testBackRWA

#check Nat.add_sub_assoc

def testBackRWA' := testBackRW_sandBox_noSub `Nat.add_sub_assoc

def testBackRWB' := testBackRW_sandBox_wiSub `Nat.add_sub_assoc


-- With context and objects ((fun (x y z : Nat) (h : x = 42) => x + y - z) = (fun (x y z : Nat) (h : x = 42) => x*y*z)) run testBackRWA'
-- can't really test adding binders to subgoals, but at least ↓ looks good as it adds a funext for h
-- With context and objects ((fun (x y z : Nat) (h : x = 42) => x + y - z) = (fun (x y z : Nat) (h : x = 42) => x*y*z)) run testBackRWB'

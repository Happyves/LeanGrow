
import Lean


open Lean Meta Elab Tactic


#check PreDefinition

#check Structural.structuralRecursion

#check wfRecursion


def test_1 : Nat → Nat
| 0 => 1
| n+1 => (n+1) * test_1 n

#print test_1
#check Nat.brecOn
#print Nat.brecOn
#print Nat.brecOn.go
#check Nat.below
#print Nat.below
#check (@Nat.below (fun _ => Nat) 2)
#check test_1.match_1
#print test_1.match_1


noncomputable
def hmm_1 (x : Nat) : Nat :=
  @Nat.brecOn (fun _ ↦ Nat) x (fun x f ↦
    ((test_1.match_1
      (fun x ↦ @Nat.below (fun _ ↦ Nat) x → Nat)
      x
      (fun a x ↦ 1)
      (fun n x ↦
        have y := x.1
        have z := x.2
        (n + 1) * x.1)) : (@Nat.below (fun _ ↦ Nat) x) → Nat)
      f)


def test_2 : Nat → Nat
| 0 => 1
| 1 => 1
| n+2 => (test_2 (n+1)) + test_2 n


#print test_2
#print test_2.match_1

noncomputable
def hmm_2 (x : Nat) : Nat :=
  @Nat.brecOn (fun _ ↦ Nat) x (fun x f ↦
    ((test_2.match_1
      (fun x ↦ @Nat.below (fun _ ↦ Nat) x → Nat)
      x
      (fun a x ↦ 1)
      (fun a x ↦
        have y := x.1
        1)
      (fun n x ↦
        have y := x.1
        have z := x.2
        y + z.1)) : (@Nat.below (fun _ ↦ Nat) x) → Nat)
      f)

def testing : (@Nat.below (fun _ => Nat) 3) :=
  PProd.mk 1 (PProd.mk 2 (PProd.mk 3 ()))

/-
`Nat.below n` acts as a product of `n` times the motive, so for example
`@Nat.below (fun _ => Nat) 3` is `Nat × Nat × Nat`.

`Nat.brecOn.go` conputes a sequence of values, stored as a product in the
form of a `Nat.below`, and `Nat.brecOn` simply takes the last computed value.
The argument to `Nat.brecOn` describles how to compute the next value to be stored
as first entry of the product, based on the prior values of the product: typically,
its a matcher. `Nat.brecOn.go` then makes a new product out of this value and the
prior product


-/


def test_3 {α : Type} : List α → List α
| [] => []
| x :: xs => (test_3 xs) ++ [x]


#print test_3
#print List.brecOn
#print List.brecOn.go
#print List.below


def test_3_1 : Nat → Nat → Nat
| 0, _ => 1
| n+1, 0 => (n+1) * test_3_1 n 0
| n+1, m+1 => test_3_1 n (m+2)

#print test_3_1
-- structural rec on n recognized, motive is function in n

def test_3_2 : Nat → Nat → Nat
| m+1, n+1 => test_3_2 (m+2) n
| _,0 => 1
| _,n+1 => (n+1) * test_3_2 n 0

#print test_3_2
-- argument which causes to become wellfounded rec
#print test_3_2._unary


def test_3_3 : Nat → Nat → Nat → Nat
| 0, _, _ => 1
| n+1, 0, _ => (n+1) * test_3_3 n 0 0
| n+1, m+1, k+1 => test_3_3 n (m+2) k
| _,_,0 => 37

#print test_3_3


def test_4 (x : Nat) : Nat :=
  if h : x = 0
  then 1
  else x * test_4 (x-1)
decreasing_by
  apply Nat.sub_lt
  · apply Nat.pos_of_ne_zero h
  · decide


#print test_4
#print test_4._proof_1

#print WellFounded.fix
-- will perform recursion with
#print WellFounded.fixF
-- which wraps arround Acc.rec, and discards the useless arg in the recursor
#check Acc.rec
-- to get an Acc to recurse on, we use projection
#print WellFounded.apply
-- and the assumption
#print WellFounded


#check WellFounded.rec
#print invImage
#print InvImage
#print WellFoundedRelation
#print WellFounded

def test_4_1 (x : List Nat) : List Nat :=
  if h : x = []
  then [42]
  else x ++ test_4_1 (x.tail)
decreasing_by
  rw [← ne_eq, List.ne_nil_iff_exists_cons] at h
  obtain ⟨_,_,h⟩ := h
  rw [h]
  dsimp
  grind

#check sizeOf
#synth SizeOf (List Nat)
#print List._sizeOf_inst
#print List._sizeOf_1

#print test_4_1


def test_5 (x : Nat) : Nat :=
  if h : x = 0
  then 1
  else x * test_5 (x-1)
termination_by x -- docstring
decreasing_by -- docstring
  apply Nat.sub_lt
  · apply Nat.pos_of_ne_zero h
  · decide

#print test_5

def test_6 : Nat → Nat → Nat
| 0, _ => 1
| 1 ,n+1 => test_6 n n
| 1 ,0 => 42
| n+2, x => test_6 (n+1) n
termination_by x y => max x y

#print test_6

#print test_6._unary
-- Seems to be regular wellfounded rec, except that arg is product of original args

-- proofs of decrease
#print test_6._unary._proof_2
#print test_6._unary._proof_3


def test_7 (x  y: Nat) : Nat :=
  if h : x = 0
  then y
  else x * test_7 (x-1) (y+1)


#print test_7

#print test_7._unary
-- same idea as before, recognized that x is decreasing !

def test_8 : Nat → Nat → Nat → Nat
| 0, _,_ => 1
| 1 ,n+1,m => test_8 n n n
| 1 ,0, _ => 42
| n+2, x, m+1 => test_8 (n+1) x m
| _,_,0 => 67
termination_by x y z => max (max x y) z
decreasing_by
· grind
· rw [Nat.max_lt]
  constructor
  · rw [@Nat.max_def (max n.succ.succ x) m.succ]
    split
    · sorry -- false
    · sorry
  · grind

#print test_8
#print test_8._unary

#print Nat.add_comm


def ack : Nat → Nat → Nat
  | 0, n => n + 1
  | m + 1, 0 => ack m 1
  | m + 1, n + 1 => ack m (ack (m + 1) n)

#print ack._unary

/-

Wf
| c._unary term
| WellFounded.fix _* F(fun (x : _) (acc : _) => wfc)

wfc
| term(acc _ _)
| PSigma.casesOn _ ((fun x y z => wfc) acc)
| (matcher (fun acc => term(acc))) acc


brec
| brec terms* -- when motive is function
| c.brecOn _ (fun x y => (matcher (fun (x : _.below _) => term(x(.i)*))) y)

-/


#check WellFounded.fix
#check PSigma.casesOn
#check List.brecOn
#print FunInfo
#check getFunInfo

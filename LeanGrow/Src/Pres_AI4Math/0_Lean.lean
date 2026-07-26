

-- # Refresher on Lean

prelude

noncomputable section


axiom Nat : Type
-- there is a type of objects called *Nat*ural numbers
axiom Nat.zero : Nat
-- there is a  *Nat*ural number called zero
axiom Nat.succ (n : Nat) : Nat
-- given a *Nat*ural number, there is a successor for it


def Nat.one : Nat := Nat.succ Nat.zero
-- defines 1

def Nat.two : Nat := Nat.succ Nat.one
-- defines 2

axiom Nat.leq (n m : Nat) : Prop
-- there is a relation between natural numbers

axiom Nat.leq_zero (n : Nat) : Nat.leq Nat.zero n
-- ∀ n, 0 ≤ n

axiom Nat.leq_step (n m: Nat) (h : Nat.leq n m) : Nat.leq (Nat.succ n) (Nat.succ m)
-- ∀ n m, n ≤ m → n+1 ≤ m+1


def myFirstTheorem : Nat.leq Nat.one Nat.two := -- 1 ≤ 2
  Nat.leq_step -- will follow from 0 ≤ 1
    Nat.zero -- as 1 is defined as 0+1
    Nat.one -- and 2 as 1+1
    (Nat.leq_zero Nat.one) -- the last argument must be of type 0 ≤ 1
    -- this follows from theorem `Nat.leq_zero`


axiom Nat.recursion (n : Nat) (expr : Nat → Sort u)
  (base : expr Nat.zero) (step : ∀ m, expr m → expr (Nat.succ m)) : expr n


def mySecondTheorem (n : Nat) : Nat.leq n (Nat.succ n) := -- n ≤ n+1
  Nat.recursion -- induction
    n (fun x => Nat.leq x (Nat.succ x))
    (base := Nat.leq_zero (Nat.succ Nat.zero)) -- 0 ≤ 1
    (step := -- ∀ n, n ≤ n+1 → n+1 ≤ (n+1)+1
      fun n ih => -- ∀ n : ℕ, ih : n ≤ n+1
        Nat.leq_step n (Nat.succ n) ih
      )


example (n : Nat) : Nat.leq n (Nat.succ n) := -- n ≤ n+1
  have fwd : Nat.leq Nat.zero (Nat.succ Nat.zero) := -- 0 ≤ 1
    Nat.leq_zero (Nat.succ Nat.zero)
  -- We now have 0 ≤ 1 in context
  Nat.recursion -- induction
    n (fun x => Nat.leq x (Nat.succ x))
    (base := fwd)
    (step := -- ∀ n, n ≤ n+1 → n+1 ≤ (n+1)+1
      fun n ih => -- ∀ n : ℕ, ih : n ≤ n+1
        Nat.leq_step n (Nat.succ n) ih
      )

axiom Eq {T : Sort u} (a b : T) : Prop

axiom Eq.refl {T : Sort u} (a : T) : Eq a a

axiom Eq.rewrite {T : Sort u} (a b : T) (eq : Eq a b) (expr : T → Sort v) (h : expr a) : expr b

def Eq.symm {T : Sort u} (a b : T) (eq : Eq a b) : Eq b a :=
  Eq.rewrite a b eq -- will follow from Eq a a, after rewriting b
    (expr := fun x => Eq x a)
    (h := Eq.refl a) -- last argument must have type Eq a a, which is provided by reflexivity


#exit

def Nat.add (n m : Nat) : Nat :=
  Nat.recursion n (fun _ => Nat)
    (base := m)
    (step := fun k res_k =>  Nat.succ res_k)

axiom Nat.recursion_base {expr : Nat → Sort u}
  {base : expr Nat.zero} {step : ∀ m, expr m → expr (Nat.succ m)} :
  Eq
    (Nat.recursion Nat.zero expr base step)
    (base)

def Nat.add_zero (n : Nat) : Eq (Nat.add Nat.zero n) n :=
  Nat.recursion_base

axiom Nat.recursion_step {n : Nat} {expr : Nat → Type} {recu : expr n}
  {base : expr Nat.zero} {step : ∀ m, expr m → expr (Nat.succ m)} :
  Eq
    (Nat.recursion (Nat.succ n) expr base step)
    (step n recu)

def Nat.add_succ (n m : Nat) : Eq (Nat.add (Nat.succ n) m) (Nat.succ (Nat.add n m)) :=
  Nat.recursion_step


def mySecondTheorem (n m : Nat) : Nat.leq n (Nat.add n m) :=
  Nat.recursion -- by induction
    n (fun n => Nat.leq n (Nat.add n m))
    (base := Nat.leq_zero (Nat.add Nat.zero m))
    -- base case ; argument must have type 0 ≤ 0+m ; follows from `Nat.leq_zero`
    (step := -- step ; argument must have type ∀ k, k ≤ k+m → k+1 ≤ (k+1)+m
      fun k step =>
      -- for any k ∈ ℕ, and hypothesis step : k ≤ k+m
      have tmp : Nat.leq (Nat.succ k) (Nat.succ (Nat.add k m)) :=
        -- let's show that k+1 ≤ (k+m)+1
        Nat.leq_step k (Nat.add k m) step
        -- `Nat.leq_step` applied with hypothesis `step`
      Eq.rewrite (Nat.succ (Nat.add k m)) (Nat.add (Nat.succ k) m)
        -- will follow from `tmp` after we rewrite (k+m)+1 = (k+1)+m
        (eq := Eq.symm _ _
          -- (k+m)+1 = (k+1)+m will follow from (k+1)+m = (k+m)+1
          (Nat.add_succ k m)
          -- and that's just `Nat.add_succ`
          )
        (h := tmp)
      )



import LeanGrow.F.Utils.CExprTrie.Types
import LeanGrow.F.Utils.List

open Lean

namespace CExprTrie


partial def build_target (T : CExprTrie) (idx : Nat) : CExpr :=
  match T with
  | .dead => .failed
  | .br lnodes gnodes bvars sorts consts lits apf apa api laf laa lai alf ala ali lef lea lez lei projs =>
        match lnodes.find? (fun x => List.orderedContains (· ≤ ·) idx x.1) with
        | .some (_,i,t) => .lnode i (.ofBvar 42) t
        | _ =>
          match gnodes.find? (fun x => List.orderedContains (· ≤ ·) idx x.1) with
          | .some (_,i) => .gnode i (.ofBvar 42)
          | _ =>
            match bvars.find? (fun x => List.orderedContains (· ≤ ·) idx x.1) with
            | .some (_,i) => .bvar i
            | _ =>
              match sorts.find? (fun x => List.orderedContains (· ≤ ·) idx x.1) with
              | .some (_,i) => .sort i
              | _ =>
                match consts.find? (fun x => List.orderedContains (· ≤ ·) idx x.1) with
                | .some (_,n,l) => .const n l
                | _ =>
                  match lits.find? (fun x => List.orderedContains (· ≤ ·) idx x.1) with
                  | .some (_,i) => .lit i
                  | _ =>
                    if List.orderedContains (· ≤ ·) idx api
                    then .app (build_target apf idx) (build_target apa idx)
                    else
                      if List.orderedContains (· ≤ ·) idx lai
                      then .lam `dummy (build_target laf idx) (build_target laa idx) .default
                      else
                        if List.orderedContains (· ≤ ·) idx ali
                        then .forallE `dummy (build_target alf idx) (build_target ala idx) .default
                        else
                          if List.orderedContains (· ≤ ·) idx lei
                          then .letE `dummy (build_target lef idx) (build_target lea idx) (build_target lez idx) true
                          else
                            match projs.find? (fun x => List.orderedContains (· ≤ ·) idx x.1) with
                            | .some (_,n,i,t) => .proj n i (build_target t idx)
                            | _ => .failed





partial def factor_with (T : CExprTrie) (idx : Nat) (dirs : List oDirs) (insert : Nat → CExpr) : CExpr :=
    let rec go (depth : Nat) (T : CExprTrie) (dirs : List oDirs) : CExpr :=
      match T with
      | .dead => .failed
      | .br _ _ _ _ _ _ apf apa _ laf laa _ alf ala _ lef lea lez _ projs =>
        match dirs with
        | [] => insert depth
        | nx :: more =>
            match nx with
            | .apf => .app (go depth apf more) (apa.build_target idx)
            | .apa => .app (apf.build_target idx) (go depth apa more)
            | .laf => .lam `dummy (go depth laf more) (laa.build_target idx) .default
            | .laa => .lam `dummy (laf.build_target idx) (go (depth+1) laa more) .default
            | .alf => .forallE `dummy (go depth alf more) (ala.build_target idx) .default
            | .ala => .forallE `dummy (alf.build_target idx) (go (depth+1) ala more) .default
            | .lef => .letE `dummy (go depth lef more) (lea.build_target idx) (lez.build_target idx) true
            | .lea => .letE `dummy (lef.build_target idx) (go depth lea more) (lez.build_target idx) true
            | .lez => .letE `dummy (lef.build_target idx) (lea.build_target idx) (go (depth+1) lez more) true
            | .pro n i =>
                match List.find? (fun x => x.2.1 == n && x.2.2.1 == i) projs with
                | .some (_,_,_,t) => .proj n i (go depth t more)
                | _ => .failed
    go 0 T dirs



def factor (T : CExprTrie) (idx : Nat) (dirs : List oDirs) : CExpr :=
  (CExprTrie.factor_with T idx dirs (fun d => .bvar d))

def buildRWtype (T : CExprTrie) (idx : Nat) (dirs : List oDirs) (replacement : CExpr) : CExpr :=
  CExprTrie.factor_with T idx dirs (fun _ => replacement)

end CExprTrie


/-
Problem of dependent rewites.
Example : we have f : (n : Nat) → (p : P n) → X for a predicate P and we want to show f 2 p₁ = f (1+1) p₂.
There is no simple solution to this, so for the moment, fust infer type  of assumed rewritten type,
and if it returns .failed (check that we fail durring inference !), then don't carry out the rewrite.
-/


#check Eq.rec


def test  {α : Sort _} {β : Sort _} {a : α} {c : β} {motive : (b : α) → a = b → (d : β) → c = d → Sort _}
  (ha : motive a rfl c rfl)
  {b : α} {d : β} (ta : a = b) (tc : c = d) : motive b ta d tc :=
    have inter : motive a rfl d tc :=
      @Eq.rec β c (fun x hx => motive a rfl x hx) ha d tc
    @Eq.rec α a (fun x hx => motive x hx d tc) inter b ta

noncomputable
def test2  {α : Sort _} {β : Sort _} {a : α} {c : β} {motive : (b : α) → a = b → (β : Sort _) → (d : β) → HEq c d → Sort _}
  (ha : motive a rfl β c HEq.rfl)
  {b : α} {d : β} (ta : a = b) (tc : HEq c d) : motive b ta β d tc :=
    have inter : motive a rfl β d tc :=
      @HEq.rec β c (@fun γ x hx => motive a rfl γ x hx) ha β d tc
    @Eq.rec α a (fun x hx => motive x hx β d tc) inter b ta

#check HEq.rfl


noncomputable
def test3  {α : Sort _} {β : Sort _} {γ : Sort _} {a : α} {c : β}
  {motive : (b : α) → a = b → (β : Sort _) → (d : β) → HEq c d → Sort _}
  (ha : motive a rfl β c HEq.rfl)
  {b : α} {d : γ} (ta : a = b) (tc : HEq c d) : motive b ta γ d tc :=
    have inter : motive a rfl γ d tc :=
      @HEq.rec β c (@fun γ x hx => motive a rfl γ x hx) ha γ d tc
    @Eq.rec α a (fun x hx => motive x hx γ d tc) inter b ta


-- noncomputable
-- def test4  {α : Sort _} {β : (α : Sort _) → α → Sort _} {a : α} {c : β α a}
--   {motive : (b : α) → a = b → (γ : (α : Sort _) → α → Sort _) → (d : γ α b) → HEq c d → Sort _}
--   (ha : motive a rfl β c HEq.rfl)
--   {b : α} {d : β α b} (ta : a = b) (tc : HEq c d) : motive b ta β d tc :=
--     have inter : motive a rfl β (by rw [ta] ; exact d) (sorry ):=
--       @HEq.rec (β α a) c (@fun γ x hx => motive a rfl β x hx) ha d tc
--     @Eq.rec α a (fun x hx => motive x hx γ d tc) inter b ta

-- #check HEq.subst
-- #check HEq.trans

inductive dHEq : (α : Sort _) → (β : α → Sort _) → (a b : α) → β a → β b → Prop where
  | refl (β : α → Sort _) (x : β a) : dHEq α β a a x x

#check dHEq.rec



theorem dHEq.rfl (α : Sort _) (β : α → Sort _) (a : α) (x : β a) : dHEq α β a a x x :=
  dHEq.refl β x

theorem dHEq.symm (α : Sort _) (β : α → Sort _) (a b : α) (x : β a) (y : β b) (h : dHEq α β a b x y) : dHEq α β b a y x :=
  @dHEq.rec α (fun B Ba Bb z w _ => dHEq α B Bb Ba w z) (fun B Bx => dHEq.refl B Bx) β a b x y h

#check HEq.symm

#check HEq.ndrec

noncomputable
def dHEq.ndrec {α : Sort _} {motive : (β : α → Sort u_2) → (a b : α) → (a_1 : β a) → (a_2 : β b) → Sort _}
    (m : {a : α} → (β : α → Sort _) → (x : β a) → motive β a a x x)
    {β : α → Sort _} {a b : α} {x : β a} {y : β b} (t : dHEq α β a b x y) : motive β a b x y :=
    @dHEq.rec α (fun B Ba Bb z w _ => motive B Ba Bb z w) m β a b x y t

theorem eq_of_dheq {a : α} {x y : β a} (h : dHEq α β a a x y) : Eq x y :=
  have : (a b : α) → (z : β a) → (w : β b) → dHEq α β a b z w → (h : Eq a b) → Eq (cast (congrArg β h) z) w :=
    fun _ _ _ _ h₁ =>
      h₁.rec (fun _ _ _ => rfl)
  this a a x y h rfl

#check congrArg

-- def dHEq.subst (α : Sort _) (β : α → Sort _) (a b : α) (x : β a) (y : β b) (h : dHEq α β a b x y)
--   (P : (β : α → Sort _) → (c : α) → β c → Sort _) (hp : P β a x): P β b y :=
--   @dHEq.ndrec α (fun _ _ _ _ _ => P β a x) (fun _ _  => hp) β a b x y h

-- noncomputable
-- def test4 {α : Sort _} {β : Sort _} {γ : β → Sort _} {a : α} {c : β} {f : γ c}
--   {motive : (b : α) → a = b → (d : β) → (e : γ d) → dHEq β γ c d f e → Sort _}
--   (ha : motive a rfl c f (@dHEq.refl β c γ f))
--   {b : α} {d : β} {e : γ d} (ta : a = b) (tc : dHEq β γ c d f e) : motive b ta d e tc :=
--     have inter : motive a rfl d e tc :=
--       @dHEq.rec β (@fun γ c d f e H => motive a rfl d e) ha γ d tc
--     @Eq.rec α a (fun x hx => motive x hx γ d tc) inter b ta

inductive DHEq : (α : Sort _) → (β : α → Sort _) → (a b : α) → β a → β b → Prop where
  | refl (a : α) (x : β a) : DHEq α β a a x x

#check DHEq.rec

theorem DHEq.rfl (α : Sort _) (β : α → Sort _) (a : α) (x : β a) : DHEq α β a a x x :=
  DHEq.refl a x

theorem DHEq.symm (α : Sort _) (β : α → Sort _) (a b : α) (x : β a) (y : β b) (h : DHEq α β a b x y) : DHEq α β b a y x :=
  @DHEq.rec α β a (fun b z w _ => DHEq α β b a w z) (fun x => DHEq.refl a x) b x y h

noncomputable
def DHEq.ndrec {α : Sort _} {β : α → Sort _} {a : α}
  {motive : (b : α) → (x : β a) → (y : β b) → Sort _}
  (refl : (x : β a) → motive a x x)
  {b : α} {x : β a}  {y : β b} (t : DHEq α β a b x y) : motive b x y :=
    @DHEq.rec α β a (fun b z w _ => motive b z w) refl b x y t

theorem eq_of_Dheq {a : α} {x y : β a} (h : DHEq α β a a x y) : Eq x y :=
  have : (a b : α) → (z : β a) → (w : β b) → DHEq α β a b z w → (h : Eq a b) → Eq (cast (congrArg β h) z) w :=
    fun _ _ _ _ h₁ =>
      h₁.rec (fun _ _=> rfl)
  this a a x y h rfl

noncomputable
def DHEq.subst (α : Sort _) (β : α → Sort _) (a b : α) (x : β a) (y : β b) (h : DHEq α β a b x y)
  (P : (c : α) → β c → Sort _) (hp : ∀ x, P a x) : P b y :=
  @DHEq.ndrec α β a (fun b _ y => P b y) (fun x  => hp x) b x y h

noncomputable
def test4 {α : Sort _} {β : Sort _} {γ : β → Sort _} {a : α} {c : β} {f : γ c}
  {motive : (b : α) → a = b → (d : β) → (e : γ d) → Sort _}
  (ha : ∀ f, motive a rfl c f)
  {b : α} {d : β} {e : γ d} (ta : a = b) (tc : DHEq β γ c d f e) : motive b ta d e :=
    have inter : motive a rfl d e  :=
      @DHEq.ndrec β γ c (@fun d _ e => motive a rfl d e) ha d f e tc
    @Eq.rec α a (fun x hx => motive x hx d e) inter b ta

--#exit

theorem proof_irrel_Dheq {p : α → Prop} {a b : α} (eq : a = b) (hp : p a) (hq : p b) : DHEq α p a b hp hq := by
  have fst := proof_irrel_heq hp hq
  apply @test3 α (p a) (p b) a hp
    (fun c ceq q d _ => DHEq α p a c hp (by rw [← ceq] ; exact hp))
    (DHEq.refl a hp) b hq
    eq fst

example (l : List Nat) (x : Nat) :
  let p1 : l.length < (x :: l).reverse.length := by rw [List.length_reverse] ; dsimp ; exact Nat.lt.base (List.length l) ;
  let p2 : l.length < (l.reverse ++ [x]).length := by rw [List.length_append, List.length_reverse] ; dsimp ; exact Nat.lt.base (List.length l)
  ((x :: l).reverse).get  ⟨l.length, p1 ⟩ =
  List.get (l.reverse ++ [x]) ⟨l.length, p2⟩ :=
  by
  intro p1 p2
  --have h : HEq p1 p2 := proof_irrel_heq p1 p2
  have H := @test4
    (List Nat) (List Nat) (fun X => (l.length < X.length))
    (x :: l).reverse (x :: l).reverse p1
    (fun b _ d e => (x :: l).reverse.get ⟨l.length, p1⟩ = d.get ⟨l.length, e⟩)
    (fun _ => rfl)
    (l.reverse ++ [x]) (l.reverse ++ [x]) p2
    (List.reverse_cons x l)
    (by apply proof_irrel_Dheq
        apply List.reverse_cons
        )
  exact H

#check List.reverse_cons

#check proof_irrel_heq
#check propext
#check iff_of_true
#check proof_irrel

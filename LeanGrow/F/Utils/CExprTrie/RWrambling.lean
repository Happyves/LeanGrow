

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

theorem testPara (l : List Nat) (x : Nat) :
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


inductive dhEq : (α : Sort _) → (β : α → Sort _) → (a b : α) → β a → β b → Prop where
  | refl (x : (by exact β a)) : dhEq α β a a x x

#check dhEq.rec
#check DHEq.rec


noncomputable
def test5 {α : Sort _} {γ : α → Prop} {a : α} {f : γ a}
  {motive : (b : α) → (d : α) → (e : γ d) → Sort _}
  (ha : motive a a f)
  {b : α} {e : γ b} (ta : a = b) : motive b b e :=
    @test4 α α γ
      a a f
      (fun b _ d e => motive b d e)
      (fun p => by rw [proof_irrel p f] ; exact ha)
      b b e
      ta
      (by apply proof_irrel_Dheq
          apply ta
          )

#check HEq.subst


#check Fin.ext

@[ext]
structure FIN where
  n : Nat
  v : Fin n

#check FIN.ext
#print FIN.ext

-- open Lean in
-- #eval (do let r := (← getEnv).find? `FIN.ext ; if r.isSome then IO.println "yes" : CoreM _)
-- -- requires Lean as import, but output yes

#check FIN.ext.match_1
#check FIN.rec

#check test3



theorem testin (x y : FIN) (h1 : x.n = y.n) (h2 : HEq x.v y.v) : x = y :=
  have hmm : (⟨x.n,x.v⟩ : FIN) = ⟨y.n,y.v⟩ := sorry
  hmm

#print testin

noncomputable
def test6 {α : Sort _} {γ : α → Sort _} {a : α} {f : γ a}
  {motive : (b : α) → (d : α) → (e : γ d) → Sort _}
  (ha : ∀ f, motive a a f)
  {b : α} {e : γ b} (eq1 : a = b) (eq2 : DHEq α γ a b f e) : motive b b e :=
    @test4 α α γ
      a a f
      (fun b _ d e => motive b d e)
      (fun p => ha p)
      b b e
      eq1 eq2

#check test6


theorem Dheq_of_heq {a b : α} {x : β a} {y : β b} (h1 : a = b) (h2 : HEq x y) : DHEq α β a b x y :=
  sorry


#check PSigma.rec
#check PSigma
#check PSigma.ext
#print PSigma.ext

noncomputable
def test7  {α : Sort _} {β : α → Sort _}  {a : α} {c : β a}
  {motive : (b : α) → (d : β b) → Sort _}
  (ha : motive a c)
  {b : α} {d : β b} (ta : a = b) (tc : HEq c d) : motive b d :=
    have wow := @PSigma.ext α β ⟨a,c⟩ ⟨b,d⟩ ta tc
    @Eq.ndrec (@PSigma α β) ⟨a,c⟩ (fun z => motive z.fst z.snd) ha ⟨b,d⟩ wow

#check Fin.mk
#check FIN.mk

#check HEq.subst



theorem testin2 (x y : FIN) (h1 : x.n = y.n) (h2 : HEq x.v y.v) : x = y :=
  --@test6 Nat Fin x.n x.v
  -- @test3 Nat (Fin x.n) (Fin y.n) x.n x.v
  --   (fun b eq β d heq => HEq x )
  @test7 Nat Fin x.n x.v (fun b d => x = ⟨b,d⟩) rfl y.n y.v h1 h2

theorem testPara2 (l : List Nat) (x : Nat) :
  let p1 : l.length < (x :: l).reverse.length := by rw [List.length_reverse] ; dsimp ; exact Nat.lt.base (List.length l) ;
  let p2 : l.length < (l.reverse ++ [x]).length := by rw [List.length_append, List.length_reverse] ; dsimp ; exact Nat.lt.base (List.length l)
  ((x :: l).reverse).get  ⟨l.length, p1 ⟩ =
  List.get (l.reverse ++ [x]) ⟨l.length, p2⟩ :=
  by
  intro p1 p2
  apply @test7 (List Nat) (fun X => l.length < X.length)
    (x :: l).reverse p1
    (fun b d => ((x :: l).reverse).get  ⟨l.length, p1⟩ = List.get b ⟨l.length, d⟩)
    rfl (l.reverse ++ [x]) p2
    (List.reverse_cons x l)
    (proof_irrel_heq p1 p2)

-- from mathlib
theorem Fin.val_eq_val (a b : Fin n) : (a : Nat) = b ↔ a = b :=
  ext_iff.symm

-- from mathlib
theorem Fin.heq_ext_iff {k l : Nat} (h : k = l) {i : Fin k} {j : Fin l} :
    HEq i j ↔ (i : Nat) = (j : Nat) := by
  subst h
  simp [Fin.val_eq_val]

theorem testPara3 (l : List Nat) (x : Nat) :
  let p1 : l.length < (x :: l).reverse.length := by rw [List.length_reverse] ; dsimp ; exact Nat.lt.base (List.length l) ;
  let p2 : l.length < (l.reverse ++ [x]).length := by rw [List.length_append, List.length_reverse] ; dsimp ; exact Nat.lt.base (List.length l)
  ((x :: l).reverse).get  ⟨l.length, p1 ⟩ =
  List.get (l.reverse ++ [x]) ⟨l.length, p2⟩ :=
  by
  intro p1 p2
  apply @test7 (List Nat) (fun X => Fin X.length)
    (x :: l).reverse ⟨l.length, p1⟩
    (fun b d => ((x :: l).reverse).get  ⟨l.length, p1⟩ = List.get b d)
    rfl (l.reverse ++ [x]) ⟨l.length, p2⟩
    (List.reverse_cons x l)
    (by rw [Fin.heq_ext_iff] ; rw [List.reverse_cons])

@[ext]
structure FSigma {α : Sort _} {ι : Sort _} (β : ι → α → Sort _) where
  fst : α
  snd : (i : ι) → β i fst


#check FSigma.rec
#check FSigma.ext

-- from mathlib
theorem hfunext {α α' : Sort u} {β : α → Sort v} {β' : α' → Sort v} {f : ∀a, β a} {f' : ∀a, β' a}
    (hα : α = α') (h : ∀a a', HEq a a' → HEq (f a) (f' a')) : HEq f f' := by
  subst hα
  have : ∀a, HEq (f a) (f' a) := λ a => h a a (HEq.refl a)
  have : β = β' := by funext a
                      exact type_eq_of_heq (this a)
  subst this
  apply heq_of_eq
  funext a
  exact eq_of_heq (this a)

noncomputable
def test8  {α : Sort _} {β : α → Sort _}  {a : α} {c : β a}
  {motive : (b : α) → (d : β b) → Sort _}
  (ha : motive a c)
  {b : α} {d : β b} (ta : a = b) (tc : HEq c d) : motive b d :=
    have wow := @FSigma.ext α Nat (fun _ => β) ⟨a,(fun _ => c)⟩ ⟨b,(fun _ => d)⟩
      ta (by apply hfunext ; rfl ; intro _ _ _ ; apply tc)
    @Eq.ndrec (@FSigma α Nat (fun _ => β)) ⟨a,(fun _ => c)⟩ (fun z => motive z.fst (z.snd 0)) ha ⟨b,(fun _ => d)⟩ wow


#check funext

noncomputable
def test9  {α : Sort _} {β γ : α → Sort _}  {a : α} {c : β a} {e : γ a}
  {motive : (b : α) → (d : β b) → (f : γ b) →  Sort _}
  (ha : motive a c e) {b : α} {d : β b} {f : γ b}
  (ta : a = b) (tc : HEq c d) (te : HEq e f) : motive b d f :=
    have wow := @FSigma.ext α Nat (fun | 0 => β | _ => γ) ⟨a,(fun | 0 => c | _+1 => e)⟩ ⟨b,(fun | 0 => d | _+1 => f)⟩
      ta (by
            apply hfunext
            · rfl
            · intro x y hq
              replace hq := eq_of_heq hq
              cases x
              · cases y
                · exact tc
                · contradiction
              · cases y
                · contradiction
                · exact te
              )
    @Eq.ndrec (@FSigma α Nat (fun | 0 => β | _ => γ)) ⟨a,(fun | 0 => c | _+1 => e)⟩ (fun z => motive z.fst (z.snd 0) (z.snd 1)) ha ⟨b,(fun | 0 => d | _+1 => f)⟩ wow


noncomputable
def test10  {α : Sort _} {β γ δ: α → Sort _}  {a : α} {c : β a} {e : γ a} {g : δ a}
  {motive : (b : α) → (d : β b) → (f : γ b) → (h : δ b) → Sort _}
  (ha : motive a c e g) {b : α} {d : β b} {f : γ b} {h : δ b}
  (ta : a = b) (tc : HEq c d) (te : HEq e f) (tg : HEq g h) : motive b d f h :=
    have wow := @FSigma.ext α Nat (fun | 0 => β | 1 => γ | _ => δ) ⟨a,(fun | 0 => c | 1 => e | _+2 => g)⟩ ⟨b,(fun | 0 => d | 1 => f | _+2 => h)⟩
      ta (by
            apply hfunext
            · rfl
            · intro x y hq
              replace hq := eq_of_heq hq
              cases x
              · cases y
                · exact tc
                · contradiction
              · cases y
                · contradiction
                · rename_i z w
                  cases z
                  · cases w
                    · exact te
                    · rw [Nat.succ_inj'] at hq
                      contradiction
                  · cases w
                    · rw [Nat.succ_inj'] at hq
                      contradiction
                    · exact tg
              )
    @Eq.ndrec (@FSigma α Nat (fun | 0 => β | 1 => γ | _ => δ)) ⟨a,(fun | 0 => c | 1 => e | _+2 => g)⟩  (fun z => motive z.fst (z.snd 0) (z.snd 1) (z.snd 2)) ha ⟨b,(fun | 0 => d | 1 => f | _+2 => h)⟩ wow



-- structure RSigma {α : Sort _} {ι : Sort _} (β : ι → α → Sort _) where
--   fst : α
--   snd : (i : ι) → β i fst

-- def RSigma : Nat → Sort _ → Prop
-- | 0, α => α
-- | n+1, α => ∀ β : α → Prop, (RSigma n β)

@[ext]
structure TSigma {α : Sort _} {ι : Sort _} {κ : Sort _} (β : ι → α → Sort _) (γ : (j : κ) → (i : ι) → (a : α) → β i a → Sort _) where
  fst : α
  snd : (i : ι) → β i fst
  thd : (j : κ) → (i : ι) → γ j i fst (snd i)

#check TSigma.ext

noncomputable
def test11  {α : Sort _} {β : α → Sort _} {γ : (a : α) → β a → Sort _}  {a : α} {c : β a} {e : γ a c}
  {motive : (b : α) → (d : β b) → (f : γ b d) →  Sort _}
  (ha : motive a c e) {b : α} {d : β b} {f : γ b d}
  (ta : a = b) (tc : HEq c d) (te : HEq e f) : motive b d f :=
    have wow := @TSigma.ext α Unit Unit (fun _ => β) (fun _ _ => γ) ⟨a,(fun _ => c),(fun _ _ => e)⟩ ⟨b,(fun _ => d),(fun _ _ => f)⟩
      ta (by apply hfunext ; rfl ; intro _ _ _ ; apply tc) (by apply hfunext ; rfl ; intro _ _ _ ; apply hfunext ; rfl ; intro _ _ _ ; apply te)
    @Eq.ndrec (@TSigma α Unit Unit (fun _ => β) (fun _ _ => γ)) ⟨a,(fun _ => c),(fun _ _ => e)⟩ (fun z => motive z.fst (z.snd ()) (z.thd () ()) ) ha ⟨b,(fun _ => d),(fun _ _ => f)⟩ wow

-- For example for rewrites with {n : Nat} {e : Fin n} {h : P n e}

-- testing if smaller arity version can be derived from larger one
noncomputable
def test12  {α : Sort _} {β : α → Sort _}  {a : α} {c : β a}
  {motive : (b : α) → (d : β b) →  Sort _}
  (ha : motive a c) {b : α} {d : β b}
  (ta : a = b) (tc : HEq c d) : motive b d :=
  @test10 α β (fun _ => Unit) (fun _ => Unit) a c () ()
    (fun x y _ _ => motive x y) ha
    b d () () ta tc HEq.rfl HEq.rfl

#check test12
-- no constraint added on universe param of motive :)

def testSort (t : Nat → Sort _) : Nat → Sort _
  | 0 => t 0
  | n+1 => (t (n+1)) → (testSort t n)

#check testSort
#reduce (types := true) testSort (fun _ => Unit) 5


#check TSigma
--def RSigma


def testSort2 (t : (n : Nat) → Sort n) : (n : Nat) → Sort n
  | 0 => t 0
  | n+1 => (t (n+1)) → (testSort t n)

#check testSort2
-- #reduce (types := true) testSort (fun n => Sort n) 5

#check List (List Nat)

def testBump := fun (α : Sort _) => α → Nat

#check testBump

--@[ext] -- fails
def SSigma {α : Sort _} {β : α → Sort _} (γ : (a : α) → β a → Sort _) :=
  @PSigma α (fun a => @PSigma (β a) (γ a))


def testSSigma {α : Sort _} {β : α → Sort _} {γ : (a : α) → β a → Sort _}  {a : α} {c : β a} {e : γ a c} :
  SSigma γ := ⟨a,⟨c,e⟩⟩

#check PSigma.ext

theorem eqRec_heq' {α : Sort u} {φ : α → Sort v} {a a' : α} : (h : a = a') → (p : φ a) → HEq (Eq.rec (motive := fun x _ => φ x) p h) p
  | rfl, p => HEq.refl p

noncomputable
def test13  {α : Sort _} {β : α → Sort _} {γ : (a : α) → β a → Sort _}  {a : α} {c : β a} {e : γ a c}
  {motive : (b : α) → (d : β b) → (f : γ b d) →  Sort _}
  (ha : motive a c e) {b : α} {d : β b} {f : γ b d}
  (ta : a = b) (tc : HEq c d) (te : HEq e f) : motive b d f :=
    -- have fst : HEq (⟨c,e⟩ : PSigma (γ a)) (⟨d,f⟩ : PSigma (γ b))  :=
    --   @PSigma.ext α
    have snd : (⟨a,⟨c,e⟩⟩ : SSigma γ) = ⟨b,⟨d,f⟩⟩ :=
      @PSigma.ext α (fun a => @PSigma (β a) (γ a)) ⟨a,⟨c,e⟩⟩ ⟨b,⟨d,f⟩⟩ ta
        (by dsimp
            apply heq_of_eqRec_eq (by rw [ta])
            apply PSigma.ext
            · apply eq_of_heq
              apply HEq.trans _ tc
              apply heq_of_eqRec_eq (by rw [ta])
              dsimp
              sorry
            · dsimp
              sorry
            -- have e1 : β b = β a := by rw [ta]
            -- have e2 : HEq (γ b) (γ a) := by rw [ta]
            -- have : @PSigma.mk (β b) (γ b) d f = @PSigma.mk (β a) (γ a) (cast e1 d) (HEq.elim e2 f) := sorry
            )
    sorry


#check HEq.elim
#check heq_of_eqRec_eq

#print TSigma.ext

#check TSigma.rec

theorem customExt : ∀ {α : Sort u_1} {ι : Sort u_2} {κ : Sort u_3}
  {β : ι → α → Sort u_4} {γ : κ → (i : ι) → (a : α) → β i a → Sort u_5} (x y : TSigma β γ),
  x.fst = y.fst → HEq x.snd y.snd → HEq x.thd y.thd → x = y := by
    intro α ι κ β γ x y
    apply @TSigma.rec α ι κ β γ (fun y => x.fst = y.fst → HEq x.snd y.snd → HEq x.thd y.thd → x = y)
    intro f s t e1 --e2 e3
    dsimp
    dsimp at e1
    revert t s
    apply @Eq.rec α x.fst (fun f _ => ∀ (s : (i : ι) → β i f) (t : (j : κ) → (i : ι) → γ j i f (s i)), HEq x.snd s → HEq x.thd t → x = { fst := f, snd := s, thd := t }) _ _ e1
    intro s t e2 --e2 e3
    dsimp
    revert t
    replace e2 := eq_of_heq e2
    apply @Eq.rec _ x.snd (fun s _ => ∀ (t : (j : κ) → (i : ι) → γ j i x.fst (s i)), HEq x.thd t → x = { fst := x.fst, snd := s, thd := t }) _ _ e2
    intro t e3
    replace e3 := eq_of_heq e3
    apply @Eq.rec _ x.thd (fun t _ => x = { fst := x.fst, snd := x.snd, thd := t }) _ _ e3
    rfl

-- combine this technique and the ext Eq rec for motives ?

#check HEq.rec

#check PSigma.rec

#print customExt
#print TSigma.ext


def HList : List (Type u) → Type u
| [] => PUnit
| α :: αs => α × HList αs


def PHList : List (Type u) → Type u
| [] => PUnit
| α :: αs => @PSigma α (fun a => PHList αs)


def mkFun : List (Sort u) → Sort (u+1)
  | [] => Sort u
  | t :: ts => t → (mkFun ts)

def mkFun' (h : Sort u) : List (Sort u) → Sort u
  | [] => h
  | t :: ts => t → (mkFun' h ts)

@[reducible]
def mkDeps (h : Sort u) : Nat → Sort u
  | 0 => h
  | n+1 =>
      let hm := (List.range (n+1)).map (mkDeps h)
      mkFun' h hm
decreasing_by
  sorry

example : mkDeps (2+2=4) 1 = ((2+2=4) → (2+2=4) ):= rfl

example : mkDeps (2+2=4) 2 = ((2+2=4) → ((2+2=4) → (2+2=4)) → (2+2=4)):= rfl

@[reducible]
def mkFun'' (h : Sort u) : List (Sort u) → (t : Sort u) → (x : t) → Sort u
  | [] => fun _ _ => h
  | t :: ts => fun _ _ => (x : t) → mkFun'' h ts t x

#reduce (types := true) mkFun'' Unit [Unit,Unit] Unit ()


noncomputable
def test14  {α : Sort _} {β : α → Sort _} {γ : (a : α) → β a → Sort _}  {a : α} {c : β a} {e : γ a c}
  {motive : (b : α) → (d : β b) → (f : γ b d) →  Sort _}
  (ha : motive a c e) {b : α} {d : β b} {f : γ b d}
  (ta : a = b) (tc : HEq c d) (te : HEq e f) : motive b d f :=
    have snd : (⟨a,⟨c,e⟩⟩ : SSigma γ) = ⟨b,⟨d,f⟩⟩ :=
      @PSigma.ext α (fun a => @PSigma (β a) (γ a)) ⟨a,⟨c,e⟩⟩ ⟨b,⟨d,f⟩⟩ ta
        (by dsimp
            revert d f
            apply @Eq.rec α a (fun b _ => ∀ {d : β b} {f : γ b d}, HEq c d → HEq e f → HEq (⟨c, e⟩ : PSigma (γ a)) (⟨d, f⟩ : PSigma (γ b))) _ _ ta
            intro d f e1
            replace e1 := eq_of_heq e1
            revert f
            apply @Eq.rec (β a) c (fun d _ => ∀ {f : γ a d}, HEq e f → HEq (⟨c, e⟩ : PSigma (γ a)) (⟨d, f⟩ : PSigma (γ a))) _ _ e1
            intro f e2
            replace e2 := eq_of_heq e2
            apply heq_of_eq
            congr
            )
    @Eq.rec (SSigma γ) ⟨a,⟨c,e⟩⟩ (fun x _ => motive x.1 x.2.1 x.2.2) ha _ snd

@[ext]
structure ISigma {α : Sort _} (β : α → Nat → Sort _) where
  fst : α
  snd : (n : Nat) → β fst n


noncomputable
def test15 {α : Sort _} {β γ: α → Sort _} {δ : (a : α) → β a → γ a → Sort _}
  {a : α} {b : β a} {c : γ a} {d : δ a b c}
  {motive : (w : α) → (x : β w) → (y : γ w) → (z : δ w x y) →  Sort _} (H : motive a b c d)
  {e : α} {f : β e} {g : γ e} {h : δ e f g}
  (ta : a = e) (tb : HEq b f) (tc : HEq c g) (td : HEq d h) : motive e f g h :=
  let Inter {α : Sort _} {β γ: α → Sort _} {δ : (a : α) → β a → γ a → Sort _} :=
    -- @ISigma α (fun a n =>
    --   @ISigma
    --   -- match n with
    --   -- | 0 =>
    --   -- | m+1 =>
    --   )
    @PSigma α (fun a => @PSigma (β a) (fun b => @PSigma (γ a) (δ a b)))
  have inter : (⟨a,⟨b,⟨c,d⟩⟩⟩ : @Inter α β γ δ) = ⟨e,⟨f,⟨g,h⟩⟩⟩ :=
    @PSigma.ext α (fun a => @PSigma (β a) (fun b => @PSigma (γ a) (δ a b)))
      ⟨a,⟨b,⟨c,d⟩⟩⟩ ⟨e,⟨f,⟨g,h⟩⟩⟩ ta
      (by dsimp
          revert f g h
          rw [← ta]
          --apply @Eq.rec α a (fun e _ => ∀ {f : β e} {g : γ e} {h : δ e f g}, HEq b f → HEq c g → HEq d h → HEq (⟨b, ⟨c, d⟩⟩ : (b : β a) ×' PSigma (δ a b)) (⟨f, ⟨g, h⟩⟩ : (b : β e) ×' PSigma (δ e b))) _ _ ta
          intro f g h e1
          replace e1 := eq_of_heq e1
          revert g h
          apply @Eq.rec (β a) b (fun f _ => ∀ {g : γ a} {h : δ a f g}, HEq c g → HEq d h → HEq (⟨b, ⟨c, d⟩⟩ : (b : β a) ×' PSigma (δ a b)) (⟨f, ⟨g, h⟩⟩ : (b : β a) ×' PSigma (δ a b))) _ _ e1
          intro g h e2
          replace e2 := eq_of_heq e2
          revert h
          apply @Eq.rec (γ a) c (fun g _ => ∀ {h : δ a b g}, HEq d h → HEq (⟨b, ⟨c, d⟩⟩ : (b : β a) ×' PSigma (δ a b)) (⟨b, ⟨g, h⟩⟩ : (b : β a) ×' PSigma (δ a b))) _ _ e2
          intro h e3
          replace e3 := eq_of_heq e3
          congr
          )
  @Eq.rec (@Inter α β γ δ) ⟨a,⟨b,⟨c,d⟩⟩⟩ (fun x _ => motive x.1 x.2.1 x.2.2.1 x.2.2.2) H _ inter


#check test7

example (F : (n : Nat) → Fin n → Nat) (A B : List Unit) (eq : A = B) (h : 2 < A.length)
  (todo : F A.length ⟨2,h⟩ = 37) : True := by
    have := @test7 (List Unit) (fun A => 2 < A.length) A h
      (fun A HA => F A.length ⟨2,HA⟩ = 37) todo B
      (@Eq.subst (List Unit) (fun A => 2 < A.length) _ _ eq h) eq (by apply proof_irrel_heq)
    apply True.intro

#check test11


example (F : (n : Nat) → Fin n → Nat) (A B : List Unit) (eq : A = B) (h : 2 < A.length)
  (todo : F A.length ⟨2,h⟩ = 37) : True := by
    have fst : A.length = B.length := by rw [eq]
    have snd := @test7 Nat (fun X => 2 < X) A.length h
      (fun X XP => F X ⟨2,XP⟩ = 37) todo B.length
      (Eq.subst fst h) fst (by apply proof_irrel_heq)
    apply True.intro

#check cast
#check Eq.subst

noncomputable
def Eq.cast {α : Sort _} {motive : α → Sort _} {a b : α} (h₁ : Eq a b) (h₂ : motive a) : motive b :=
  Eq.ndrec h₂ h₁

#check @Eq.cast Nat Fin 4 (2+2) rfl ⟨0, by decide⟩
#reduce @Eq.cast Nat Fin 4 (2+2) rfl ⟨0, by decide⟩
  -- reduces to Fin 4
#check cast (show Fin 4 = Fin (2+2) from rfl) ⟨0, by decide⟩
#reduce cast (show Fin 4 = Fin (2+2) from rfl) ⟨0, by decide⟩

noncomputable
def test16  {α : Sort _} {β : α → Sort _}  {a : α} {c : β a}
  {motive : (b : α) → (d : β b) → Sort _}
  (ha : motive a c)
  {b : α} (ta : a = b)
    : -- and tc can be solve with proof_irrel if β is predicate
    let P : β a = β b := by rw [ta]
    let d := cast P c
    motive b d := by
      intro P d
      apply @test7 α β a c motive ha b d ta
       (by apply HEq.symm ; apply cast_heq)


theorem testPara4 (l : List Nat) (x : Nat) :
  let p1 : l.length < (x :: l).reverse.length := by rw [List.length_reverse] ; dsimp ; exact Nat.lt.base (List.length l) ;
  let p2 : l.length < (l.reverse ++ [x]).length := by rw [List.length_append, List.length_reverse] ; dsimp ; exact Nat.lt.base (List.length l)
  ((x :: l).reverse).get  ⟨l.length, p1 ⟩ =
  List.get (l.reverse ++ [x]) ⟨l.length, p2⟩ :=
  by
  intro p1 p2
  have := @test16 (List Nat) (fun X => Fin X.length)
    (x :: l).reverse ⟨l.length, p1⟩
    (fun b d => ((x :: l).reverse).get  ⟨l.length, p1⟩ = List.get b d)
    rfl (l.reverse ++ [x])
    (List.reverse_cons x l)
  sorry


noncomputable -- 16 is for foward, 17 for backward
def test17  {α : Sort _} {β : α → Sort _}  {a : α} {c : β a}
  {motive : (b : α) → (d : β b) → Sort _}
  {b : α} (ta : a = b) -- this should come from thm
  (ha :
    let P : β a = β b := by rw [ta]
    let d := cast P c
    motive b d
    )-- so this will be the new goal
    :
    motive a c := by
      let P : β a = β b := by rw [ta]
      let d := cast P c
      apply @test7 α β b d motive ha a c ta.symm
       (by apply cast_heq)


noncomputable
def test18 {α : Sort _} {β γ: α → Sort _} {δ : (a : α) → β a → γ a → Sort _}
  {a : α} {b : β a} {c : γ a} {d : δ a b c}
  {motive : (w : α) → (x : β w) → (y : γ w) → (z : δ w x y) →  Sort _} (H : motive a b c d)
  {e : α} {f : β e} {g : γ e} {h : δ e f g}
  (ta : a = e) (tb : HEq b f) (tc : HEq c g) (td : HEq d h) : motive e f g h :=
    by -- is how convert does it
    revert f g h
    rw [← ta]
    intro f g h e1
    replace e1 := eq_of_heq e1
    revert g h
    apply @Eq.rec (β a) b (fun f _ => {g : γ a} → {h : δ a f g} → HEq c g → HEq d h → motive a f g h) _ _ e1
    intro g h e2
    replace e2 := eq_of_heq e2
    revert h
    apply @Eq.rec (γ a) c (fun g _ => {h : δ a b g} → HEq d h → motive a b g h) _ _ e2
    intro h e3
    replace e3 := eq_of_heq e3
    rw [← e3]
    exact H

#check cast_eq

example (F : (n : Nat) → Fin n) (G : (x : Fin 42) → Nat) (h : G (F 42) = 37) : True := by
  have eq : 42 = 2*21 := rfl
  have e2 : Fin 42 = Fin (2*21) := by rw [eq]
  have final : G (cast e2.symm (F (2*21))) = 37 := by
    --have tmp : G (cast rfl (F 42)) = 37 := by rw [cast_eq] ; exact h
    -- ↓ works directly, but can it be systeatized ?
    apply @test7 Nat (fun n => Fin 42 = Fin n) 42 rfl
      (fun x y => G (cast y.symm (F x)) = 37) h -- tmp unnecessary
      (2*21) e2 eq (heq_of_eq (proof_irrel rfl e2))
  apply True.intro

noncomputable
def test19  {γ α : Sort _} {β : α → Sort _} (x : γ)  {a : α} {c : β a}
  {motive : (y : γ) → (b : α) → (d : β b) → Sort _}
  (ha : motive x a c)
  (y : γ) {b : α} {d : β b} (tx : x = y) (ta : a = b) (tc : HEq c d) : motive y b d :=
    have wow : (⟨x,⟨a,c⟩⟩ : @PSigma γ (fun _ => PSigma β)) = ⟨y,⟨b,d⟩⟩ :=
      @PSigma.ext γ (fun _ => PSigma β) ⟨x,⟨a,c⟩⟩ ⟨y,⟨b,d⟩⟩
        tx (by apply heq_of_eq ; exact @PSigma.ext α β ⟨a,c⟩ ⟨b,d⟩ ta tc)
    @Eq.ndrec (@PSigma γ (fun _ => PSigma β)) ⟨x,⟨a,c⟩⟩ (fun z => motive z.1 z.2.1 z.2.2) ha ⟨y,⟨b,d⟩⟩ wow

--#exit

example (F : (n : Nat) → Fin n) (h : (F 42) = 37) (test_eq : Nat = Int) : True := by
  -- example of a rewrite in binder type that should propagate to other hyps
  -- will never occur in practice ...
  let F' : (n : Int) → Fin (cast test_eq.symm n) := fun n => F (cast test_eq.symm n)
  have tmp1 (n : Nat) : cast test_eq.symm (cast test_eq n) = n := by
      rw [cast_cast,cast_eq]
  have tmp2 (n : Nat) : Fin (cast test_eq.symm (cast test_eq n)) = Fin n := by
      rw [tmp1]
  have : F' (cast test_eq 42) = (cast (tmp2 42).symm 37) := by
    dsimp [F']
    apply @test7 Nat (fun t => Fin 42 = Fin t) 42 rfl
      (fun y d => F y = (cast d (37 : Fin 42))) (by exact h) --possibly with cast_eq
      (cast test_eq.symm (cast test_eq 42)) (tmp2 _).symm
      (tmp1 42).symm (proof_irrel_heq _ _)
  apply True.intro


def List.sum (L : List α) (f : α → Nat) : Nat :=
  L.foldl (fun s x => s + f x) 0

example (l : List Nat) (h : l.sum (fun n => 2*n + 1) = 37) : l.sum (fun n => n+n + 1) = 37:= by
  --rw [Nat.two_mul] at h -- fails ; simp_rw should work → check how for sampling of states !!!
  have : (fun n => 2*n + 1) = (fun n => n+n + 1) := by
    apply funext
    intro x
    rw [Nat.two_mul]
  rw [this] at h
  exact h

#check funext


#check propext


theorem test20 {α : Sort _}  (β γ : α → Sort _) (P : (α → Sort _) → Prop) (h : ∀ a : α, β a = γ a)
  --(f : ∀ a : α, β a) (g : ∀ a : α, γ a) (H : ∀ a : α, (f a) = cast (h a).symm (g a))
  (hp : P β) : P γ := by
  have : β = γ := by
    apply funext ; exact h
  rw [← this] ; exact hp

theorem test21 {α : Sort _} {δ : α → Sort _}  (β γ : (a : α) → δ a) (P : ((a : α) → δ a) → Prop) (h : ∀ a : α, β a = γ a)
  --(f : ∀ a : α, β a) (g : ∀ a : α, γ a) (H : ∀ a : α, (f a) = cast (h a).symm (g a))
  (hp : P β) : P γ := by
  have : β = γ := by
    apply funext ; exact h
  rw [← this] ; exact hp



theorem test22 {α : Sort _} (β γ : α → Sort _) (h : ∀ a : α, β a = γ a) : (∀ a : α, β a) = (∀ a : α, γ a) :=
  by
  apply test20 β γ (fun δ => (∀ a : α, β a) = (∀ a : α, δ a)) h rfl

def funT (α : Sort _) := α → α

example (h : funT (∀ n : Nat, Fin (2*n)) = Nat) : funT (∀ n : Nat, Fin (n+n)) = Nat := by
  have : (∀ n : Nat, Fin (2*n)) = (∀ n : Nat, Fin (n+n)) := by
    apply test22
    intro aha
    rw [Nat.two_mul]
  rw [← this] ; exact h -- yay


noncomputable
def castTest {α : Sort _} (β γ : α → Sort _) (h : ∀ a : α, β a = γ a) (f : ∀ a : α, β a) : (∀ a : α, γ a) :=
  fun a => cast (h a) (f a)


noncomputable
def test23 {α : Sort _} {β γ: α → Sort _} {δ : (a : α) → β a → γ a → Sort _}
  {a : α} {b : β a} {c : γ a} {d : δ a b c}
  {motive : (w : α) → (x : β w) → (y : γ w) → (z : δ w x y) →  Sort _} (H : motive a b c d)
  {e : α} {f : β e} {g : γ e} {h : δ e f g}
  (ta : a = e) (tb : HEq b f) (tc : HEq c g) (td : HEq d h) : motive e f g h :=
    by -- is how convert does it
    revert f g h
    rw [← ta]
    intro f g h e1
    replace e1 := eq_of_heq e1
    revert g h
    apply @Eq.rec (β a) b (fun f _ => {g : γ a} → {h : δ a f g} → HEq c g → HEq d h → motive a f g h) _ _ e1
    intro g h e2
    replace e2 := eq_of_heq e2
    revert h
    apply @Eq.rec (γ a) c (fun g _ => {h : δ a b g} → HEq d h → motive a b g h) _ _ e2
    intro h e3
    replace e3 := eq_of_heq e3
    rw [← e3]
    exact H


/-
So if pattern is found under binders,

-/

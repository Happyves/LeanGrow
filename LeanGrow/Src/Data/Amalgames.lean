

/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

-- # Prod

structure Prod3 (α β γ : Type _) where
  fst : α
  snd : β
  thd : γ
deriving BEq, Inhabited, Repr


structure Prod4 (α β γ δ : Type _) where
  fst : α
  snd : β
  thd : γ
  frd : δ
deriving BEq, Inhabited, Repr


structure Prod5 (α β γ δ ι : Type _) where
  fst : α
  snd : β
  thd : γ
  frd : δ
  fth : ι
deriving BEq, Inhabited, Repr

structure Prod6 (α β γ δ ι t1: Type _) where
  fst : α
  snd : β
  thd : γ
  frd : δ
  fth : ι
  six : t1
deriving BEq, Inhabited, Repr

structure Prod7 (α β γ δ ι t1 t2 : Type _) where
  fst : α
  snd : β
  thd : γ
  frd : δ
  fth : ι
  six : t1
  svn : t2
deriving BEq, Inhabited, Repr

structure Prod8 (α β γ δ ι t1 t2 t3 : Type _) where
  fst : α
  snd : β
  thd : γ
  frd : δ
  fth : ι
  six : t1
  svn : t2
  eig : t3
deriving BEq, Inhabited, Repr

structure Prod9 (α β γ δ ι t1 t2 t3 t4 : Type _) where
  fst : α
  snd : β
  thd : γ
  frd : δ
  fth : ι
  six : t1
  svn : t2
  eig : t3
  nin : t4
deriving BEq, Inhabited, Repr

structure Prod10 (α β γ δ ι t1 t2 t3 t4 t5 : Type _) where
  fst : α
  snd : β
  thd : γ
  frd : δ
  fth : ι
  six : t1
  svn : t2
  eig : t3
  nin : t4
  ten : t5
deriving BEq, Inhabited, Repr


structure Prod11 (α β γ δ ι t1 t2 t3 t4 t5 t6 : Type _) where
  fst : α
  snd : β
  thd : γ
  frd : δ
  fth : ι
  six : t1
  svn : t2
  eig : t3
  nin : t4
  ten : t5
  ele : t6
deriving BEq, Inhabited, Repr



-- # OptionProd


inductive OptionProd (α β: Type _) where
| none | some (_ : α) (_ : β)
deriving BEq, Inhabited, Repr

def OptionProd.toOptionofProd {α β: Type _} : OptionProd α β → Option (α × β)
| .none => .none
| .some (a : α) (b: β) => .some (a,b)

def OptionProd.ofOptionofProd {α β: Type _} : Option (α × β) → OptionProd α β
| .none => .none
| .some (a,b) => .some (a : α) (b: β)

inductive OptionProd3 (α β γ: Type _) where
| none | some (_ : α) (_ : β) (_ : γ)
deriving BEq, Inhabited, Repr

inductive OptionProd4 (α β γ δ : Type _) where
| none | some (_ : α) (_ : β) (_ : γ) (_ : δ)
deriving BEq, Inhabited, Repr

inductive OptionProd5 (α β γ δ ι : Type _) where
| none | some (_ : α) (_ : β) (_ : γ) (_ : δ) (_ : ι)
deriving BEq, Inhabited, Repr

inductive OptionProd6 (α β γ δ ι κ: Type _) where
| none | some (_ : α) (_ : β) (_ : γ) (_ : δ) (_ : ι) (_ : κ)
deriving BEq, Inhabited, Repr




-- # ListProd

-- ## Types

inductive ListProd (α β: Sort _) where
| nil | cons (_ : α) (_ : β) (_ : ListProd α β)
deriving Inhabited

inductive ListProd3 (α β γ : Sort _) where
| nil | cons (_ : α) (_ : β) (_ : γ) (_ : ListProd3 α β γ)
deriving Inhabited

inductive ListProd4 (α β γ δ : Sort _) where
| nil | cons (_ : α) (_ : β) (_ : γ) (_ : δ) (_ : ListProd4 α β γ δ)
deriving Inhabited

inductive ListProd5 (α β γ δ ι : Sort _) where
| nil | cons (_ : α) (_ : β) (_ : γ) (_ : δ) (_ : ι) (_ : ListProd5 α β γ δ ι)
deriving Inhabited

inductive ListProd6 (α β γ δ ι κ : Sort _) where
| nil | cons (_ : α) (_ : β) (_ : γ) (_ : δ) (_ : ι) (_ : κ) (_ : ListProd6 α β γ δ ι κ)
deriving Inhabited


-- ## Printing

instance {α β: Sort _} [BEq α] [BEq β] : BEq (ListProd α β) :=
  let rec go : ListProd α β → ListProd α β → Bool
    | .nil , .nil => true
    | .cons a b nx1, .cons A B nx2 => a == A && b == B && (go nx1 nx2)
    | _, _ => false
  ⟨go⟩

def ListProd.toListOfProd {α β: Sort _} : ListProd α β →  List (α × β)
  | .nil => []
  | .cons a b nx => (a,b) :: nx.toListOfProd

def ListProd.ofListOfProd {α β: Sort _} : List (α × β) → ListProd α β
  | .nil => .nil
  | .cons (a, b) nx => .cons a b <| ListProd.ofListOfProd nx

instance {α β: Sort _} [Repr α] [Repr β] : Repr (ListProd α β) :=
  ⟨fun x y => reprPrec x.toListOfProd y⟩

instance {α β : Sort _} [ToString α] [ToString β] : ToString (ListProd α β) where
  toString := fun x => toString x.toListOfProd

def ListProd3.toListOfProd {α β γ : Sort _} (L : ListProd3 α β γ) : List (α × β × γ) :=
  let rec go (sf : List (α × β × γ)) : ListProd3 α β γ → List (α × β × γ)
    | .nil => sf
    | .cons k v t more => go ((k,v,t) :: sf) more
  go [] L

instance {α β γ : Sort _} [Repr α] [Repr β] [Repr γ] : Repr (ListProd3 α β γ) where
  reprPrec := fun x y => reprPrec x.toListOfProd y

instance {α β γ : Sort _} [ToString α] [ToString β] [ToString γ] : ToString (ListProd3 α β γ) where
  toString := fun x => toString x.toListOfProd

def ListProd4.toListOfProd {α β γ δ : Sort _} (L : ListProd4 α β γ δ) : List (α × β × γ × δ) :=
  let rec go (sf : List (α × β × γ × δ)) : ListProd4 α β γ δ → List (α × β × γ × δ)
    | .nil => sf
    | .cons k v t f more => go ((k,v,t,f) :: sf) more
  go [] L

instance {α β γ δ : Sort _} [Repr α] [Repr β] [Repr γ] [Repr δ] : Repr (ListProd4 α β γ δ) where
  reprPrec := fun x y => reprPrec x.toListOfProd y

instance {α β γ δ : Sort _} [ToString α] [ToString β] [ToString γ] [ToString δ] : ToString (ListProd4 α β γ δ) where
  toString := fun x => toString x.toListOfProd

-- ## isEmpty

def ListProd.isEmpty {α β: Sort _} : ListProd α β → Bool
  | .nil => true
  | _ => false

def ListProd3.isEmpty {α β γ : Sort _} : ListProd3 α β γ → Bool
  | .nil => true
  | _ => false

-- ## append

def ListProd.append {α β: Sort _} : (xs ys : ListProd α β) → ListProd α β
  | .nil,    bs => bs
  | .cons a A as, bs => .cons a A <| ListProd.append as bs

def ListProd3.append {α β γ : Sort _} : (xs ys : ListProd3 α β γ) → ListProd3 α β γ
  | .nil,    bs => bs
  | .cons x y z as, bs => .cons x y z<| ListProd3.append as bs

def ListProd4.append {α β γ δ : Sort _} : (xs ys : ListProd4 α β γ δ) → ListProd4 α β γ δ
  | .nil,    bs => bs
  | .cons x y z w as, bs => .cons x y z w <| ListProd4.append as bs

def ListProd5.append {α β γ δ ι : Sort _} : (xs ys : ListProd5 α β γ δ ι) → ListProd5 α β γ δ ι
  | .nil,    bs => bs
  | .cons x y z w v as, bs => .cons x y z w v <| ListProd5.append as bs

def ListProd6.append {α β γ δ ι κ : Sort _} : (xs ys : ListProd6 α β γ δ ι κ) → ListProd6 α β γ δ ι κ
  | .nil,    bs => bs
  | .cons x y z w v u as, bs => .cons x y z w v u <| ListProd6.append as bs


-- ## Fold

@[specialize]
def ListProd.foldl {α β γ : Sort _} (L : ListProd α β) (ini : γ) (f : α → β → γ → γ) : γ :=
  let rec @[specialize] go (sf : γ) : ListProd α β → γ
    | .nil => sf
    | .cons k v more => go (f k v sf) more
  go ini L

@[specialize]
def ListProd.foldlM {m} [Monad m] {α β γ : Sort _} (L : ListProd α β) (ini : γ) (f : α → β → γ → m γ) : m γ :=
  let rec @[specialize] go (sf : γ) : ListProd α β → m γ
    | .nil => return sf
    | .cons k v more => do go (← f k v sf) more
  go ini L

@[specialize]
def ListProd.foldlMcps {m} [Monad m] {α β γ δ : Sort _} (L : ListProd α β) (ini : γ)
  (f : α → β → γ → (γ → m δ) → m δ) (k : γ → m δ) : m δ :=
  let rec @[specialize] go (sf : γ) : ListProd α β → m δ
    | .nil => k sf
    | .cons k v more => f k v sf <| fun res => go res more
  go ini L

@[specialize]
def List.foldlMcps {m} [Monad m] {α γ δ : Sort _} (L : List α) (ini : γ)
  (f : α → γ → (γ → m δ) → m δ) (k : γ → m δ) : m δ :=
  let rec @[specialize] go (sf : γ) : List α → m δ
    | .nil => k sf
    | .cons k  more => f k  sf <| fun res => go res more
  go ini L

@[specialize]
def ListProd3.foldl {α β δ γ : Sort _} (L : ListProd3 α β δ) (ini : γ) (f : α → β → δ → γ → γ) : γ :=
  let rec @[specialize] go (sf : γ) : ListProd3 α β δ → γ
    | .nil => sf
    | .cons k v t more => go (f k v t sf) more
  go ini L

@[specialize]
def ListProd3.foldlM {m} [Monad m] {α β δ γ : Sort _} (L : ListProd3 α β δ) (ini : γ) (f : α → β → δ → γ → m γ) : m γ :=
  let rec @[specialize] go (sf : γ) : ListProd3 α β δ → m γ
    | .nil => return sf
    | .cons k v x more => do go (← f k v x sf) more
  go ini L

@[specialize]
def ListProd3.foldlMcps {m} [Monad m] {α β ι γ δ : Sort _} (L : ListProd3 α β ι) (ini : γ)
  (f : α → β → ι → γ → (γ → m δ) → m δ) (k : γ → m δ) : m δ :=
  let rec @[specialize] go (sf : γ) : ListProd3 α β ι → m δ
    | .nil => k sf
    | .cons k v x more => f k v x sf <| fun res => go res more
  go ini L

@[specialize]
def ListProd4.foldl {α β δ γ ι: Sort _} (L : ListProd4 α β δ ι) (ini : γ) (f : α → β → δ → ι → γ → γ) : γ :=
  let rec @[specialize] go (sf : γ) : ListProd4 α β δ ι → γ
    | .nil => sf
    | .cons k v t m more => go (f k v t m sf) more
  go ini L

@[specialize]
def ListProd4.foldlM {m} [Monad m] {α β δ γ ι : Sort _} (L : ListProd4 α β δ ι) (ini : γ) (f : α → β → δ → ι → γ → m γ) : m γ :=
  let rec @[specialize] go (sf : γ) : ListProd4 α β δ ι → m γ
    | .nil => return sf
    | .cons k v x y more => do go (← f k v x y sf) more
  go ini L

@[specialize]
def ListProd4.foldlMcps {m} [Monad m] {α β ι γ δ κ : Sort _} (L : ListProd4 α β ι κ) (ini : γ)
  (f : α → β → ι → κ → γ → (γ → m δ) → m δ) (k : γ → m δ) : m δ :=
  let rec @[specialize] go (sf : γ) : ListProd4 α β ι κ  → m δ
    | .nil => k sf
    | .cons k v x y more => f k v x y sf <| fun res => go res more
  go ini L


@[specialize]
def ListProd5.foldl {α β δ γ ι κ: Sort _} (L : ListProd5 α β δ ι κ) (ini : γ) (f : α → β → δ → ι → κ → γ → γ) : γ :=
  let rec @[specialize] go (sf : γ) : ListProd5 α β δ ι κ → γ
    | .nil => sf
    | .cons k v t m x more => go (f k v t m x sf) more
  go ini L

@[specialize]
def ListProd5.foldlM {m} [Monad m] {α β δ γ ι κ : Sort _} (L : ListProd5 α β δ ι κ) (ini : γ) (f : α → β → δ → ι → κ → γ → m γ) : m γ :=
  let rec @[specialize] go (sf : γ) : ListProd5 α β δ ι κ → m γ
    | .nil => return sf
    | .cons k v x y z more => do go (← f k v x y z sf) more
  go ini L

@[specialize]
def ListProd5.foldlMcps {m} [Monad m] {α β ι γ δ κ ρ : Sort _} (L : ListProd5 α β ι κ ρ) (ini : γ)
  (f : α → β → ι → κ → ρ → γ → (γ → m δ) → m δ) (k : γ → m δ) : m δ :=
  let rec @[specialize] go (sf : γ) : ListProd5 α β ι κ ρ  → m δ
    | .nil => k sf
    | .cons k v x y z more => f k v x y z sf <| fun res => go res more
  go ini L


@[specialize]
def ListProd6.foldl {α β δ γ ι κ ρ : Sort _} (L : ListProd6 α β δ ι κ ρ) (ini : γ) (f : α → β → δ → ι → κ → ρ → γ → γ) : γ :=
  let rec @[specialize] go (sf : γ) : ListProd6 α β δ ι κ ρ → γ
    | .nil => sf
    | .cons k v t m x y more => go (f k v t m x y sf) more
  go ini L

@[specialize]
def ListProd6.foldlM {m} [Monad m] {α β δ γ ι κ ρ : Sort _} (L : ListProd6 α β δ ι κ ρ) (ini : γ) (f : α → β → δ → ι → κ → ρ → γ → m γ) : m γ :=
  let rec @[specialize] go (sf : γ) : ListProd6 α β δ ι κ ρ → m γ
    | .nil => return sf
    | .cons k v x y z w more => do go (← f k v x y z w sf) more
  go ini L

@[specialize]
def ListProd6.foldlMcps {m} [Monad m] {α β ι γ δ κ ρ ω : Sort _} (L : ListProd6 α β ι κ ρ ω) (ini : γ)
  (f : α → β → ι → κ → ρ → ω → γ → (γ → m δ) → m δ) (k : γ → m δ) : m δ :=
  let rec @[specialize] go (sf : γ) : ListProd6 α β ι κ ρ ω  → m δ
    | .nil => k sf
    | .cons k v x y z w more => f k v x y z w sf <| fun res => go res more
  go ini L



-- ## Find


@[specialize]
def ListProd.find? {α β : Sort _} (L : ListProd α β) (f : α → β → Bool) : OptionProd α β :=
  match L with
  | .nil => .none
  | .cons a b more => if f a b then .some a b else more.find? f

@[specialize]
def ListProd.findM? {m} [Monad m] {α β : Type _} (L : ListProd α β) (f : α → β → m Bool) : m ( OptionProd α β) := do
  match L with
  | .nil => return .none
  | .cons a b more => if ← f a b then return .some a b else more.findM? f

@[specialize]
def ListProd.findIdx? {α β : Sort _} (L : ListProd α β) (f : α → β → Bool) (start : Nat) : Option Nat :=
  match L with
  | .nil => .none
  | .cons a b more => if f a b then .some start else more.findIdx? f (start+1)


@[specialize]
def ListProd3.find? {α β ι : Sort _} (L : ListProd3 α β ι) (f : α → β → ι → Bool) : OptionProd3 α β ι :=
  match L with
  | .nil => .none
  | .cons a b c more => if f a b c then .some a b c else more.find? f

@[specialize]
def ListProd3.findM? {m} [Monad m] {α β ι : Type _} (L : ListProd3 α β ι) (f : α → β → ι → m Bool) : m (OptionProd3 α β ι) :=
  match L with
  | .nil => return .none
  | .cons a b c more => do if ← f a b c then return .some a b c else more.findM? f

@[specialize]
def ListProd4.find? {α β ι κ : Sort _} (L : ListProd4 α β ι κ) (f : α → β → ι → κ → Bool) : OptionProd4 α β ι κ :=
  match L with
  | .nil => .none
  | .cons a b c d more => if f a b c d then .some a b c d else more.find? f

@[specialize]
def ListProd4.findM? {m} [Monad m] {α β ι κ : Type _} (L : ListProd4 α β ι κ) (f : α → β → ι → κ → m Bool) : m (OptionProd4 α β ι κ) :=
  match L with
  | .nil => return .none
  | .cons a b c d more => do if ← f a b c d then return .some a b c d else more.findM? f



-- ## Map


@[specialize]
def ListProd.mapTR {α β γ δ : Sort _} (L : ListProd α β) (f : α → β → (γ × δ)) : ListProd γ δ :=
  let rec @[specialize] go (done : ListProd γ δ) : ListProd α β → ListProd γ δ
    | .nil => done
    | .cons a b more => let (ra,rb) := f a b ; go (.cons ra rb done) more
  go .nil L

@[specialize]
def ListProd.map {α β γ δ : Sort _} (L : ListProd α β) (f : α → β → (γ × δ)) : ListProd γ δ :=
  let rec @[specialize] go : ListProd α β → ListProd γ δ
    | .nil => .nil
    | .cons a b more => let (ra,rb) := f a b ; .cons ra rb (go more)
  go L


@[specialize]
def ListProd3.map {α β γ δ ι κ : Sort _} (L : ListProd3 α β γ) (f : α → β → γ → (δ × ι × κ)) : ListProd3 δ ι κ :=
  let rec @[specialize] go : ListProd3 α β γ → ListProd3 δ ι κ
    | .nil => .nil
    | .cons a b c more => let (ra,rb,rc) := f a b c ; .cons ra rb rc (go more)
  go L

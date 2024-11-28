

import LeanGrow.F.Utils.ExprTrieRWez.Unify

open Lean


/-
Goal is to get `(empty : γ) (merge : β → γ → γ) (max : γ → Option (δ × Nat))`
from `SetTrie.split_greedy_exact_hitting_set`, for example.


-/

structure sCExprTrie (α : Type _) where
  size : Nat
  trie : CExprTrie α
deriving Inhabited, Repr, BEq

def sCExprTrie.empty : sCExprTrie α := ⟨0, CExprTrie.empty⟩

def CExprTrie.getIndices_atBranch (done : List α) : List (CExprTrie.Branch α) → List α
  | [] => done
  | nx :: more =>
      match nx with
      | .ofFailed => CExprTrie.getIndices_atBranch done more
      | .ofApp _ _ ind _ _ _ => CExprTrie.getIndices_atBranch (ind ++ done) more
      | .ofLam _ _ ind _ _ _ => CExprTrie.getIndices_atBranch (ind ++ done) more
      | .ofForall _ _ ind _ _ _ => CExprTrie.getIndices_atBranch (ind ++ done) more
      | .ofLet _ _ _ ind _ _ _ _ => CExprTrie.getIndices_atBranch (ind ++ done) more
      | .ofProj _ _ _ ind _ _ => CExprTrie.getIndices_atBranch (ind ++ done) more
      | .ofBvar _ ind _ => CExprTrie.getIndices_atBranch (ind ++ done) more
      | .ofLNode _ _ ind _ => CExprTrie.getIndices_atBranch (ind ++ done) more
      | .ofLit _ ind _ => CExprTrie.getIndices_atBranch (ind ++ done) more
      | .ofGNode _ ind _ => CExprTrie.getIndices_atBranch (ind ++ done) more
      | .ofConst _ _ ind _ => CExprTrie.getIndices_atBranch (ind ++ done) more
      | .ofSort _ ind _ => CExprTrie.getIndices_atBranch (ind ++ done) more


/-- unordrered ! -/
def CExprTrie.getIndices (T : CExprTrie α) : List α :=
  let ltop := CExprTrie.getAtLink T 0
  CExprTrie.getIndices_atBranch [] ltop




-- These will reverse the branch order, which could be a problem if we impose and order on these CExprTries
def CExprTrie.BranchUpdateAppM [BEq α] (r : α → α → Prop) [DecidableRel r]
    (idx : List α) (Ref : Nat) (fl al: List Nat)
    (done : List (CExprTrie.Branch α)):
    List (CExprTrie.Branch α) → List (CExprTrie.Branch α) × Option (Nat × Nat)
    | [] => (done, .none)
    | x :: l =>
        match x with
        | .ofApp lf la I fB aB ref => (((.ofApp lf la (List.orderedUnion r idx I) (fl ++ fB) (al ++ aB) (ref + Ref)) :: done) ++ l, .some (lf,la))
        | _ => CExprTrie.BranchUpdateAppM r idx Ref fl al (x :: done) l


def CExprTrie.BranchUpdateLamM [BEq α] (r : α → α → Prop) [DecidableRel r]
    (idx : List α) (Ref : Nat) (fl al: List Nat)
    (done : List (CExprTrie.Branch α)):
    List (CExprTrie.Branch α) → List (CExprTrie.Branch α) × Option (Nat × Nat)
    | [] => (done, .none)
    | x :: l =>
        match x with
        | .ofLam lf la I fB aB ref => (((.ofLam lf la (List.orderedUnion r idx I) (fl ++ fB) (al ++ aB) (ref + Ref)) :: done) ++ l, .some (lf,la))
        | _ => CExprTrie.BranchUpdateLamM r idx Ref fl al (x :: done) l

def CExprTrie.BranchUpdateForallM [BEq α] (r : α → α → Prop) [DecidableRel r]
    (idx : List α) (Ref : Nat) (fl al: List Nat)
    (done : List (CExprTrie.Branch α)):
    List (CExprTrie.Branch α) → List (CExprTrie.Branch α) × Option (Nat × Nat)
    | [] => (done, .none)
    | x :: l =>
        match x with
        | .ofForall lf la I fB aB ref => (((.ofForall lf la (List.orderedUnion r idx I) (fl ++ fB) (al ++ aB) (ref + Ref)) :: done) ++ l, .some (lf,la))
        | _ => CExprTrie.BranchUpdateForallM r idx Ref fl al (x :: done) l


def CExprTrie.BranchUpdateLetM [BEq α] (r : α → α → Prop) [DecidableRel r]
    (idx : List α) (Ref : Nat) (fl al zl: List Nat)
    (done : List (CExprTrie.Branch α)):
    List (CExprTrie.Branch α) → List (CExprTrie.Branch α) × Option (Nat × Nat × Nat)
    | [] => (done, .none)
    | x :: l =>
        match x with
        | .ofLet lf la lz I fB aB zB ref => (((.ofLet lf la lz (List.orderedUnion r idx I) (fl ++ fB) (al ++ aB) (zl ++ zB) (ref + Ref)) :: done) ++ l, .some (lf,la,lz))
        | _ => CExprTrie.BranchUpdateLetM r idx Ref fl al zl (x :: done) l

def CExprTrie.BranchUpdateProjM [BEq α] (r : α → α → Prop) [DecidableRel r]
    (N : Name) (In : Nat) (idx : List α) (Ref : Nat) (fl: List Nat)
    (done : List (CExprTrie.Branch α)):
    List (CExprTrie.Branch α) → List (CExprTrie.Branch α) × Option (Nat)
    | [] => (done, .none)
    | x :: l =>
        match x with
        | .ofProj n i lf I fB ref =>
              if n == N && i == In
              then (((.ofProj n i lf (List.orderedUnion r idx I) (fl ++ fB) (ref + Ref)) :: done) ++ l, .some (lf))
              else CExprTrie.BranchUpdateProjM r N In idx Ref fl (x :: done) l
        | _ => CExprTrie.BranchUpdateProjM r N In idx Ref fl (x :: done) l




def CExprTrie.modifyAsLeaf_LitM [BEq α] (l : Literal) (idx : List α) (Ref : Nat) (r : α → α → Prop) [DecidableRel r]  : List (CExprTrie.Branch α) → List (CExprTrie.Branch α)
| [] => [.ofLit l idx Ref]
| x :: xs =>
    match x with
    | .ofLit L ind ref =>
        if L == l
        then (.ofLit L (List.orderedUnion r idx ind) (Ref + ref)) :: xs
        else (.ofLit L ind ref) :: (CExprTrie.modifyAsLeaf_LitM l idx Ref r xs)
    | _ => x :: (CExprTrie.modifyAsLeaf_LitM l idx Ref r xs)



def CExprTrie.modifyAsLeaf_lNodeM [BEq α]  (l : Nat) (tag : Option Nat) (idx : List α) (Ref : Nat) (r : α → α → Prop) [DecidableRel r] : List (CExprTrie.Branch α) → List (CExprTrie.Branch α)
| [] => [.ofLNode l tag idx Ref]
| x :: xs =>
    match x with
    | .ofLNode L t ind ref =>
        if L == l && t == tag
        then (.ofLNode L t (List.orderedUnion r idx ind) (Ref + ref)) :: xs
        else (.ofLNode L t ind ref) :: (CExprTrie.modifyAsLeaf_lNodeM l tag idx Ref r xs)
    | _ => x :: (CExprTrie.modifyAsLeaf_lNodeM l tag idx Ref r xs)


def CExprTrie.modifyAsLeaf_gNodeM [BEq α]  (l : Nat) (idx : List α) (Ref : Nat) (r : α → α → Prop) [DecidableRel r] : List (CExprTrie.Branch α) → List (CExprTrie.Branch α)
| [] => [.ofGNode l idx Ref]
| x :: xs =>
    match x with
    | .ofGNode L ind ref =>
        if L == l
        then (.ofGNode L (List.orderedUnion r idx ind) (Ref + ref)) :: xs
        else (.ofGNode L ind ref) :: (CExprTrie.modifyAsLeaf_gNodeM l idx Ref r xs)
    | _ => x :: (CExprTrie.modifyAsLeaf_gNodeM l idx Ref r xs)




def CExprTrie.modifyAsLeaf_BvarM [BEq α]  (l : Nat) (idx : List α) (Ref : Nat) (r : α → α → Prop) [DecidableRel r] : List (CExprTrie.Branch α) → List (CExprTrie.Branch α)
| [] => [.ofBvar l idx Ref]
| x :: xs =>
    match x with
    | .ofBvar L ind ref =>
        if L == l
        then (.ofBvar L (List.orderedUnion r idx ind) (Ref + ref)) :: xs
        else (.ofBvar L ind ref) :: (CExprTrie.modifyAsLeaf_BvarM l idx Ref r xs)
    | _ => x :: (CExprTrie.modifyAsLeaf_BvarM l idx Ref r xs)

def CExprTrie.modifyAsLeaf_SortM [BEq α]  (l : Level) (idx : List α) (Ref : Nat) (r : α → α → Prop) [DecidableRel r] : List (CExprTrie.Branch α) → List (CExprTrie.Branch α)
| [] => [.ofSort l idx Ref]
| x :: xs =>
    match x with
    | .ofSort L ind ref =>
        if L == l
        then (.ofSort L (List.orderedUnion r idx ind) (Ref + ref)) :: xs
        else (.ofSort L ind ref) :: (CExprTrie.modifyAsLeaf_SortM l idx Ref r xs)
    | _ => x :: (CExprTrie.modifyAsLeaf_SortM l idx Ref r xs)

def CExprTrie.modifyAsLeaf_ConstM [BEq α] (n : Name) (ll : List Level) (idx : List α) (Ref : Nat) (r : α → α → Prop) [DecidableRel r] : List (CExprTrie.Branch α) → List (CExprTrie.Branch α)
| [] => [.ofConst n ll idx Ref]
| x :: xs =>
    match x with
    | .ofConst L LL ind ref =>
        if L == n && LL == ll
        then (.ofConst L LL (List.orderedUnion r idx ind) (Ref + ref)) :: xs
        else (.ofConst L LL ind ref) :: (CExprTrie.modifyAsLeaf_ConstM n ll idx Ref r xs)
    | _ => x :: (CExprTrie.modifyAsLeaf_ConstM n ll idx Ref r xs)



/--
Offset warning:
Assumes input trie to be labeled by an interval of Nats starting at 1.
-/
def sCExprTrie.merge_count  [BEq α] (r : α → α → Prop) [DecidableRel r] (offset : α → Nat → α)
  (T : CExprTrie α) (sT : sCExprTrie α): sCExprTrie α :=
  let new_off := (CExprTrie.getIndices T).length + sT.size

  let rec inner (new : List (CExprTrie.Branch α)) (sofar : List (CExprTrie.Branch α)) (todos : List (Nat × Nat)) : List (CExprTrie.Branch α) → (List (CExprTrie.Branch α) × List (CExprTrie.Branch α) × List (Nat × Nat))
    | [] => (new,sofar,todos)
    | nx :: more =>
        match nx with
        | .ofApp lf la I fB aB ref =>
            let (nlb,td) := CExprTrie.BranchUpdateAppM r I ref fB aB [] sofar
            match td with
            | .some (fl, al) => inner new nlb ((lf,fl) :: (la,al) :: todos) more
            | .none => inner (nx ::new) nlb todos more
        | .ofLam lf la I fB aB ref =>
            let (nlb,td) := CExprTrie.BranchUpdateLamM r I ref fB aB [] sofar
            match td with
            | .some (fl, al) => inner new nlb ((lf,fl) :: (la,al) :: todos) more
            | .none => inner (nx ::new) nlb todos more
        | .ofForall lf la I fB aB ref =>
            let (nlb,td) := CExprTrie.BranchUpdateForallM r I ref fB aB [] sofar
            match td with
            | .some (fl, al) => inner new nlb ((lf,fl) :: (la,al) :: todos) more
            | .none => inner (nx ::new) nlb todos more
        | .ofProj n i lf I fB ref =>
            let (nlb,td) := CExprTrie.BranchUpdateProjM r n i I ref fB [] sofar
            match td with
            | .some (fl) => inner new nlb ((lf,fl) :: todos) more
            | .none => inner (nx ::new) nlb todos more
        | .ofLet lf la lz I fB aB zB ref =>
            let (nlb,td) := CExprTrie.BranchUpdateLetM r I ref fB aB zB [] sofar
            match td with
            | .some (fl, al, zl) => inner new nlb ((lf,fl) :: (la,al) :: (lz,zl) :: todos) more
            | .none => inner (nx ::new) nlb todos more
        | .ofFailed => inner (new) sofar todos more
        | .ofLit l I ref => inner new (CExprTrie.modifyAsLeaf_LitM l I ref r sofar) todos more
        | .ofBvar i I ref => inner new (CExprTrie.modifyAsLeaf_BvarM i I ref r sofar) todos more
        | .ofGNode i I ref => inner new (CExprTrie.modifyAsLeaf_gNodeM i I ref r sofar) todos more
        | .ofLNode i t I ref => inner new (CExprTrie.modifyAsLeaf_lNodeM i t I ref r sofar) todos more
        | .ofConst n l I ref => inner new (CExprTrie.modifyAsLeaf_ConstM n l I ref r sofar) todos more
        | .ofSort i I ref => inner new (CExprTrie.modifyAsLeaf_SortM i I ref r sofar) todos more

  let rec go (sofar : CExprTrie α) : List (Nat × Nat) → CExprTrie α
    | [] => sofar
    | (tl, stl) :: more =>
        let B := CExprTrie.getAtLink T tl
        let sB := CExprTrie.getAtLink sT.trie stl
        let (new,nsB,todos) := inner [] sB [] B
        sorry

  sorry

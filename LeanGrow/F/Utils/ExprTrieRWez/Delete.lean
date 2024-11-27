
import LeanGrow.F.Utils.ExprTrieRWez.Build

open Lean

def CExprTrie.BranchUpdateAppD [BEq α] (r : α → α → Prop) [DecidableRel r]
    (idx : α)
    (done : List (CExprTrie.Branch α)):
    List (CExprTrie.Branch α) → List (CExprTrie.Branch α) × Option (Nat × Nat)
    | [] => (done, .none)
    | x :: l =>
        match x with
        | .ofApp lf la I fB aB ref =>
            if ref == 1
            then (done ++ l, .some (lf,la))
            else (((.ofApp lf la (List.orderedEraseOrLeave r idx I) (fB) (aB) (ref - 1)) :: done) ++ l, .some (lf,la))
        | _ => CExprTrie.BranchUpdateAppD r idx  (x :: done) l


def CExprTrie.BranchUpdateLamD [BEq α] (r : α → α → Prop) [DecidableRel r]
    (idx : α)
    (done : List (CExprTrie.Branch α)):
    List (CExprTrie.Branch α) → List (CExprTrie.Branch α) × Option (Nat × Nat)
    | [] => (done, .none)
    | x :: l =>
        match x with
        | .ofLam lf la I fB aB ref =>
            if ref == 1
            then (done ++ l, .some (lf,la))
            else (((.ofLam lf la (List.orderedEraseOrLeave r idx I) (fB) ( aB) (ref - 1)) :: done) ++ l, .some (lf,la))
        | _ => CExprTrie.BranchUpdateLamD r idx (x :: done) l


def CExprTrie.BranchUpdateForallD [BEq α] (r : α → α → Prop) [DecidableRel r]
    (idx : α)
    (done : List (CExprTrie.Branch α)):
    List (CExprTrie.Branch α) → List (CExprTrie.Branch α) × Option (Nat × Nat)
    | [] => (done, .none)
    | x :: l =>
        match x with
        | .ofForall lf la I fB aB ref =>
            if ref == 1
            then (done ++ l, .some (lf,la))
            else (((.ofForall lf la (List.orderedEraseOrLeave r idx I) (fB) (aB) (ref - 1)) :: done) ++ l, .some (lf,la))
        | _ => CExprTrie.BranchUpdateForallD r idx (x :: done) l


def CExprTrie.BranchUpdateLetD [BEq α] (r : α → α → Prop) [DecidableRel r]
    (idx : α)
    (done : List (CExprTrie.Branch α)):
    List (CExprTrie.Branch α) → List (CExprTrie.Branch α) × Option (Nat × Nat × Nat)
    | [] => (done, .none)
    | x :: l =>
        match x with
        | .ofLet lf la lz I fB aB zB ref =>
            if ref == 1
            then (done ++ l, .some (lf,la,lz))
            else (((.ofLet lf la lz (List.orderedEraseOrLeave r idx I) ( fB) (aB) (zB) (ref - 1)) :: done) ++ l, .some (lf,la,lz))
        | _ => CExprTrie.BranchUpdateLetD r idx  (x :: done) l


def CExprTrie.BranchUpdateProjD [BEq α] (r : α → α → Prop) [DecidableRel r]
    (idx : α)
    (done : List (CExprTrie.Branch α)):
    List (CExprTrie.Branch α) → List (CExprTrie.Branch α) × Option (Nat)
    | [] => (done, .none)
    | x :: l =>
        match x with
        | .ofProj n i le I B ref =>
            if ref == 1
            then (done ++ l, .some (le))
            else (((.ofProj n i le (List.orderedEraseOrLeave r idx I) (B) (ref - 1)) :: done) ++ l, .some le)
        | _ => CExprTrie.BranchUpdateProjD r idx (x :: done) l



def CExprTrie.modifyAsLeaf_Lit_D [BEq α] (l : Literal) (idx : α) (r : α → α → Prop) [DecidableRel r]  : List (CExprTrie.Branch α) → List (CExprTrie.Branch α)
| [] => []
| x :: xs =>
    match x with
    | .ofLit L ind ref =>
        if L == l
        then
            if ref == 1
            then xs -- assumes present only once
            else (.ofLit L (List.orderedEraseOrLeave r idx ind) (ref - 1)) :: xs
        else (.ofLit L ind ref) :: (CExprTrie.modifyAsLeaf_Lit_D l idx r xs)
    | _ => x :: (CExprTrie.modifyAsLeaf_Lit_D l idx r xs)


def CExprTrie.modifyAsLeaf_Bvar_D [BEq α] (l : Nat) (idx : α) (r : α → α → Prop) [DecidableRel r]  : List (CExprTrie.Branch α) → List (CExprTrie.Branch α)
| [] => []
| x :: xs =>
    match x with
    | .ofBvar L ind ref =>
        if L == l
        then
            if ref == 1
            then xs
            else (.ofBvar L (List.orderedEraseOrLeave r idx ind) (ref - 1)) :: xs
        else (.ofBvar L ind ref) :: (CExprTrie.modifyAsLeaf_Bvar_D l idx r xs)
    | _ => x :: (CExprTrie.modifyAsLeaf_Bvar_D l idx r xs)




def CExprTrie.modifyAsLeaf_lNode_D [BEq α] (l : Nat) (tag : Option Nat) (idx : α) (r : α → α → Prop) [DecidableRel r]  : List (CExprTrie.Branch α) → List (CExprTrie.Branch α)
| [] => []
| x :: xs =>
    match x with
    | .ofLNode L t ind ref =>
        if L == l && t == tag
        then
            if ref == 1
            then xs
            else (.ofLNode L t (List.orderedEraseOrLeave r idx ind) (ref - 1)) :: xs
        else (.ofLNode L t ind ref) :: (CExprTrie.modifyAsLeaf_lNode_D l tag idx r xs)
    | _ => x :: (CExprTrie.modifyAsLeaf_lNode_D l tag idx r xs)


def CExprTrie.modifyAsLeaf_gNode_D [BEq α] (l : Nat) (idx : α) (r : α → α → Prop) [DecidableRel r]  : List (CExprTrie.Branch α) → List (CExprTrie.Branch α)
| [] => []
| x :: xs =>
    match x with
    | .ofGNode L ind ref =>
        if L == l
        then
            if ref == 1
            then xs
            else (.ofGNode L (List.orderedEraseOrLeave r idx ind) (ref - 1)) :: xs
        else (.ofGNode L ind ref) :: (CExprTrie.modifyAsLeaf_gNode_D l idx r xs)
    | _ => x :: (CExprTrie.modifyAsLeaf_gNode_D l idx r xs)


def CExprTrie.modifyAsLeaf_Sort_D [BEq α] (l : Level) (idx : α) (r : α → α → Prop) [DecidableRel r]  : List (CExprTrie.Branch α) → List (CExprTrie.Branch α)
| [] => []
| x :: xs =>
    match x with
    | .ofSort L ind ref =>
        if L == l
        then
            if ref == 1
            then xs
            else (.ofSort L (List.orderedEraseOrLeave r idx ind) (ref - 1)) :: xs
        else (.ofSort L ind ref) :: (CExprTrie.modifyAsLeaf_Sort_D l idx r xs)
    | _ => x :: (CExprTrie.modifyAsLeaf_Sort_D l idx r xs)


def CExprTrie.modifyAsLeaf_Const_D [BEq α] (n : Name) (l : List Level) (idx : α) (r : α → α → Prop) [DecidableRel r]  : List (CExprTrie.Branch α) → List (CExprTrie.Branch α)
| [] => []
| x :: xs =>
    match x with
    | .ofConst N L ind ref =>
        if N == n && L == l
        then
            if ref == 1
            then xs
            else (.ofConst N L (List.orderedEraseOrLeave r idx ind) (ref - 1)) :: xs
        else (.ofConst N L ind ref) :: (CExprTrie.modifyAsLeaf_Const_D n l idx r xs)
    | _ => x :: (CExprTrie.modifyAsLeaf_Const_D n l idx r xs)




def CExprTrie.delete_at [BEq α] (T : CExprTrie α) (start : Nat) (idx : α) (ce : CExpr) (r : α → α → Prop) [DecidableRel r] : CExprTrie α :=
  let rec go (T : CExprTrie α ) (idx : α) (link : Nat) : CExpr → (CExprTrie α)
    | .failed => T
    | .app f a =>
            let lb := CExprTrie.getAtLink T link
            let (nlb,links?) := CExprTrie.BranchUpdateAppD r idx [] lb
            match links? with
            | .some (lf,la) =>
                  let T1 := CExprTrie.modifyAtLink T link (fun _ => nlb)
                  let T2 := go T1 idx lf f
                  go T2 idx la a
            | _ =>
                  CExprTrie.modifyAtLink T link (fun _ => nlb)
    | .lam _ f a _ =>
            let lb := CExprTrie.getAtLink T link
            let (nlb,links?) := CExprTrie.BranchUpdateLamD r idx [] lb
            match links? with
            | .some (lf,la) =>
                  let T1 := CExprTrie.modifyAtLink T link (fun _ => nlb)
                  let T2 := go T1 idx lf f
                  go T2 idx la a
            | _ =>
                  CExprTrie.modifyAtLink T link (fun _ => nlb)
    | .forallE _ f a _ =>
            let lb := CExprTrie.getAtLink T link
            let (nlb,links?) := CExprTrie.BranchUpdateForallD r idx [] lb
            match links? with
            | .some (lf,la) =>
                  let T1 := CExprTrie.modifyAtLink T link (fun _ => nlb)
                  let T2 := go T1 idx lf f
                  go T2 idx la a
            | _ =>
                  CExprTrie.modifyAtLink T link (fun _ => nlb)
    | .letE _ f a z _ =>
            let lb := CExprTrie.getAtLink T link
            let (nlb,links?) := CExprTrie.BranchUpdateLetD r idx [] lb
            match links? with
            | .some (lf,la,lz) =>
                  let T1 := CExprTrie.modifyAtLink T link (fun _ => nlb)
                  let T2 := go T1 idx lf f
                  let T3 := go T2 idx la a
                  go T3 idx lz z
            | _ =>
                  CExprTrie.modifyAtLink T link (fun _ => nlb)
    | .proj _ _ e =>
            let lb := CExprTrie.getAtLink T link
            let (nlb,links?) := CExprTrie.BranchUpdateProjD r idx [] lb
            match links? with
            | .some (lf) =>
                  let T1 := CExprTrie.modifyAtLink T link (fun _ => nlb)
                  go T1 idx lf e
            | _ =>
                  CExprTrie.modifyAtLink T link (fun _ => nlb)
    | .lit l =>
            let lb := CExprTrie.getAtLink T link
            let nlb := CExprTrie.modifyAsLeaf_Lit_D l idx r lb
            (CExprTrie.modifyAtLink T link (fun _ => nlb))
    | .lnode l _ t =>
            let lb := CExprTrie.getAtLink T link
            let nlb := CExprTrie.modifyAsLeaf_lNode_D l t idx r lb
            (CExprTrie.modifyAtLink T link (fun _ => nlb))
    | .gnode l _ =>
            let lb := CExprTrie.getAtLink T link
            let nlb := CExprTrie.modifyAsLeaf_gNode_D l idx r lb
            (CExprTrie.modifyAtLink T link (fun _ => nlb))
    | .bvar l =>
            let lb := CExprTrie.getAtLink T link
            let nlb := CExprTrie.modifyAsLeaf_Bvar_D l idx r lb
            (CExprTrie.modifyAtLink T link (fun _ => nlb))
    | .sort l =>
            let lb := CExprTrie.getAtLink T link
            let nlb := CExprTrie.modifyAsLeaf_Sort_D l idx r lb
            (CExprTrie.modifyAtLink T link (fun _ => nlb))
    | .const n l =>
            let lb := CExprTrie.getAtLink T link
            let nlb := CExprTrie.modifyAsLeaf_Const_D n l idx r lb
            (CExprTrie.modifyAtLink T link (fun _ => nlb))
  (go T idx start ce)


def CExprTrie.delete [BEq α] (T : CExprTrie α) (idx : α) (ce : CExpr) (r : α → α → Prop) [DecidableRel r] : CExprTrie α :=
    CExprTrie.delete_at T 0 idx ce r


/-
Problems/todos:

- We should keep empty branches for the following reason : when we use
  `CExprTrie.insert_at` r its derivatives, the counter for adding new branches
  is set the the size of the tree, aka. the length of the list. If we deleted
  empty branches in `delete`, this would decrease the size and we may create
  new branches with already existing pointer-indices durring `insert`


-/


#eval CExprTrie.delete (CExprTrie.ofList (· ≤ ·) test_list) 4 (.app (.app (.const `a []) (.const `b [])) (.const `d [])) (· ≤ ·)

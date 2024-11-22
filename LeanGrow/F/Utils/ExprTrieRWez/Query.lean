import LeanGrow.F.Utils.ExprTrieRWez.Build

open Lean


def CExprTrie.getIndices_Lit (l : Literal) : List (CExprTrie.Branch α) → List α
| [] => []
| x :: xs =>
    match x with
    | .ofLit L ind =>
        if L == l
        then ind
        else (CExprTrie.getIndices_Lit l  xs)
    | _ => (CExprTrie.getIndices_Lit l  xs)

def CExprTrie.getIndices_lNode (l : Nat) (t : Option Nat) : List (CExprTrie.Branch α) → List α
| [] => []
| x :: xs =>
    match x with
    | .ofLNode L tag ind =>
        if L == l && t == tag
        then ind
        else (CExprTrie.getIndices_lNode l t xs)
    | _ => (CExprTrie.getIndices_lNode l t xs)



def CExprTrie.getIndices_gNode (l : Nat) : List (CExprTrie.Branch α) → List α
| [] => []
| x :: xs =>
    match x with
    | .ofGNode L ind =>
        if L == l
        then ind
        else (CExprTrie.getIndices_gNode l xs)
    | _ => (CExprTrie.getIndices_gNode l xs)




def CExprTrie.getIndices_Bvar (l : Nat) : List (CExprTrie.Branch α) → List α
| [] => []
| x :: xs =>
    match x with
    | .ofBvar L ind =>
        if L == l
        then ind
        else (CExprTrie.getIndices_Bvar l xs)
    | _ => (CExprTrie.getIndices_Bvar l xs)


def CExprTrie.getIndices_Sort (l : Level) : List (CExprTrie.Branch α) → List α
| [] => []
| x :: xs =>
    match x with
    | .ofSort L ind =>
        if L == l
        then ind
        else (CExprTrie.getIndices_Sort l xs)
    | _ => (CExprTrie.getIndices_Sort l xs)


def CExprTrie.getIndices_Const (l : Name) : List (CExprTrie.Branch α) → List α
| [] => []
| x :: xs =>
    match x with
    | .ofConst L ind =>
        if L == l
        then ind
        else (CExprTrie.getIndices_Const l xs)
    | _ => (CExprTrie.getIndices_Const l xs)


partial def CExprTrie.find_candidates? [BEq α] (T : CExprTrie α) (ce : CExpr) (r : α → α → Prop) [DecidableRel r] : List (List α) :=
  let rec go (done : List (List α)) : List (CExpr × Nat) → List (List α)
    | [] => done
    | (nx, link) :: more =>
        match nx with
        | .failed => []
        | .app f a =>
            let lb := CExprTrie.getAtLink T link
            let links? := CExprTrie.Branch_getAppLinks? lb
            match links? with
            | .some (lf,la) => go done ((f, lf) :: (a, la) :: more)
            | _ => []
-- **TODO** replace here and everywhere by `go (match links? with | .some _ => done | []) (match links? with | .some (lf,la) => ((f, lf) :: (a, la) :: more) | []) ` so as to make it tail recursive
        | .lam _ f a _ =>
            let lb := CExprTrie.getAtLink T link
            let links? := CExprTrie.Branch_getLamLinks? lb
            match links? with
            | .some (lf,la) => go done ((f, lf) :: (a, la) :: more)
            | _ => []
        | .forallE _ f a _ =>
            let lb := CExprTrie.getAtLink T link
            let links? := CExprTrie.Branch_getForallLinks? lb
            match links? with
            | .some (lf,la) => go done ((f, lf) :: (a, la) :: more)
            | _ => []
        | .letE _ f a z _ =>
            let lb := CExprTrie.getAtLink T link
            let links? := CExprTrie.Branch_getLetLinks? lb
            match links? with
            | .some (lf,la,lz) => go done ((f, lf) :: (a, la) :: (z, lz) :: more)
            | _ => []
        | .proj _ _ e =>
            let lb := CExprTrie.getAtLink T link
            let links? := CExprTrie.Branch_getProjLinks? lb
            match links? with
            | .some (le) => go done ((e, le) :: more)
            | _ => []
        | .lit l =>
            let lb := CExprTrie.getAtLink T link
            let nlb := CExprTrie.getIndices_Lit l lb
            go (nlb :: done) more
        | .lnode l _ t =>
            let lb := CExprTrie.getAtLink T link
            let nlb := CExprTrie.getIndices_lNode l t lb
            go (nlb :: done) more
        | .gnode l _ =>
            let lb := CExprTrie.getAtLink T link
            let nlb := CExprTrie.getIndices_gNode l lb
            go (nlb :: done) more
        | .bvar l =>
            let lb := CExprTrie.getAtLink T link
            let nlb := CExprTrie.getIndices_Bvar l lb
            go (nlb :: done) more
        | .sort l =>
            let lb := CExprTrie.getAtLink T link
            let nlb := CExprTrie.getIndices_Sort l lb
            go (nlb :: done) more
        | .const l _ =>
            let lb := CExprTrie.getAtLink T link
            let nlb := CExprTrie.getIndices_Const l lb
            go (nlb :: done) more
  go [] [(ce,0)]



-- #eval CExprTrie.find_candidates? (CExprTrie.ofList (· ≤ ·) test_list) (.app (.app (.const `a []) (.const `e [])) (.const `c [])) (· ≤ ·)


def CExprTrie.find? [BEq α] (T : CExprTrie α) (ce : CExpr) (r : α → α → Prop) [DecidableRel r] : List α :=
  let cand := CExprTrie.find_candidates? T ce r
  match cand with
  | [] => []
  | h :: t => t.foldl (fun x y => List.orderedIntersect r x y ) h


-- #eval CExprTrie.find? (CExprTrie.ofList (· ≤ ·) test_list) (.app (.app (.const `a []) (.const `e [])) (.const `c [])) (· ≤ ·)

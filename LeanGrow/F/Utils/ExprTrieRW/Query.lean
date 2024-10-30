import LeanGrow.F.Utils.ExprTrieRW.Build

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




def updateTodos (on : CExpr) (dirs : List rwDirs) (cache : List (Nat × CExpr × List α × List rwDirs)) : List (CExprTrie.Branch α) → List (Nat × CExpr × List α × List rwDirs)
    | [] => cache
    | x :: xs =>
        match x with
        | .ofRW id ind => updateTodos on dirs ((id, on, ind, dirs) :: cache) xs
        | _ => updateTodos on dirs cache xs



partial def CExprTrie.find_candidates? [BEq α] (T : CExprTrie α) (ce : CExpr) (r : α → α → Prop) [DecidableRel r] : List (List α) × List (Nat × CExpr × List α × List rwDirs) :=
  let rec go (done : List (List α)) (todos : List (Nat × CExpr × List α × List rwDirs)) : List (CExpr × Nat × List rwDirs) → List (List α) × List (Nat × CExpr × List α × List rwDirs)
    | [] => (done, todos)
    | (nx, link, dirs) :: more =>
        match nx with
        | .failed => ([], [])
        | .app f a =>
            let lb := CExprTrie.getAtLink T link
            let rws := updateTodos (.app f a) dirs [] lb
            let rws_ind := rws.map (fun x => x.2.2.1)
            let links? := CExprTrie.Branch_getAppLinks? lb
            match links? with
            | .some (lf,la) => go (rws_ind ++ done) (rws ++ todos) ((f, lf, .left :: dirs) :: (a, la, .right :: dirs) :: more)
            | _ => ([], [])
-- **TODO** replace here and everywhere by `go (match links? with | .some _ => done | []) (match links? with | .some (lf,la) => ((f, lf) :: (a, la) :: more) | []) ` so as to make it tail recursive
        | .lam n f a i =>
            let lb := CExprTrie.getAtLink T link
            let rws := updateTodos (.lam n f a i) dirs [] lb
            let rws_ind := rws.map (fun x => x.2.2.1)
            let links? := CExprTrie.Branch_getLamLinks? lb
            match links? with
            | .some (lf,la) => go (rws_ind ++ done) (rws ++ todos) ((f, lf, .left :: dirs) :: (a, la, .right :: dirs) :: more)
            | _ => ([], [])
        | .forallE n f a i =>
            let lb := CExprTrie.getAtLink T link
            let rws := updateTodos (.forallE n f a i) dirs [] lb
            let rws_ind := rws.map (fun x => x.2.2.1)
            let links? := CExprTrie.Branch_getForallLinks? lb
            match links? with
            | .some (lf,la) => go (rws_ind ++ done) (rws ++ todos) ((f, lf, .left :: dirs) :: (a, la, .right :: dirs) :: more)
            | _ => ([], [])
        | .letE n f a z i =>
            let lb := CExprTrie.getAtLink T link
            let rws := updateTodos (.letE n f a z i) dirs [] lb
            let rws_ind := rws.map (fun x => x.2.2.1)
            let links? := CExprTrie.Branch_getLetLinks? lb
            match links? with
            | .some (lf,la,lz) => go (rws_ind ++ done) (rws ++ todos) ((f, lf, .left :: dirs) :: (a, la, .mid :: dirs) :: (z, lz, .right :: dirs) :: more)
            | _ => ([], [])
        | .proj n i e =>
            let lb := CExprTrie.getAtLink T link
            let rws := updateTodos (.proj n i e) dirs [] lb
            let rws_ind := rws.map (fun x => x.2.2.1)
            let links? := CExprTrie.Branch_getProjLinks? lb
            match links? with
            | .some (le) => go (rws_ind ++ done) (rws ++ todos) ((e, le, .left :: dirs) :: more)
            | _ => ([], [])
        | .lit l =>
            let lb := CExprTrie.getAtLink T link
            let rws := updateTodos (.lit l) dirs [] lb
            let rws_ind := rws.map (fun x => x.2.2.1)
            let nlb := CExprTrie.getIndices_Lit l lb
            go (nlb :: (rws_ind ++ done)) (rws ++ todos) more
        | .lnode l o t =>
            let lb := CExprTrie.getAtLink T link
            let rws := updateTodos (.lnode l o t) dirs [] lb
            let rws_ind := rws.map (fun x => x.2.2.1)
            let nlb := CExprTrie.getIndices_lNode l t lb
            go (nlb :: (rws_ind ++ done)) (rws ++ todos) more
        | .gnode l o =>
            let lb := CExprTrie.getAtLink T link
            let rws := updateTodos (.gnode l o) dirs [] lb
            let rws_ind := rws.map (fun x => x.2.2.1)
            let nlb := CExprTrie.getIndices_gNode l lb
            go (nlb :: (rws_ind ++ done)) (rws ++ todos) more
        | .bvar l =>
            let lb := CExprTrie.getAtLink T link
            let rws := updateTodos (.bvar l) dirs [] lb
            let rws_ind := rws.map (fun x => x.2.2.1)
            let nlb := CExprTrie.getIndices_Bvar l lb
            go (nlb :: (rws_ind ++ done)) (rws ++ todos) more
        | .sort l =>
            let lb := CExprTrie.getAtLink T link
            let rws := updateTodos (.sort l) dirs [] lb
            let rws_ind := rws.map (fun x => x.2.2.1)
            let nlb := CExprTrie.getIndices_Sort l lb
            go (nlb :: (rws_ind ++ done)) (rws ++ todos) more
        | .const l m =>
            let lb := CExprTrie.getAtLink T link
            let rws := updateTodos (.const l m) dirs [] lb
            let rws_ind := rws.map (fun x => x.2.2.1)
            let nlb := CExprTrie.getIndices_Const l lb
            go (nlb :: (rws_ind ++ done)) (rws ++ todos) more
  go [] [] [(ce,0,[])]



-- #eval CExprTrie.find_candidates? (CExprTrie.ofList (· ≤ ·) test_list) (.app (.app (.const `a []) (.const `e [])) (.const `c [])) (· ≤ ·)


def CExprTrie.find_step [BEq α] (T : CExprTrie α) (ce : CExpr) (r : α → α → Prop) [DecidableRel r] : List α × List (Nat × CExpr × List α × List rwDirs) :=
  let (cand_safe, cand_rw) := CExprTrie.find_candidates? T ce r
  let prune :=
    match (cand_safe) with
    | [] => []
    | h :: t => t.foldl (fun x y => List.orderedIntersect r x y ) h
  (prune, (cand_rw.map (fun (n,e,ind, dir) => (n,e, List.orderedIntersect r prune ind, dir) )).filter (fun x => !x.2.2.1.isEmpty))


-- #eval CExprTrie.find? (CExprTrie.ofList (· ≤ ·) test_list) (.app (.app (.const `a []) (.const `e [])) (.const `c [])) (· ≤ ·)


#check Eq.rec

/-
**Notes**

- Situation for find candidates: imagine we have rw classes {x,y} and {z,w} and exprs `1 : x+1=42` and `2 : z+1=42`.
  then we should, when quering the expression trie we should not intersect all indices, else we get empty
  intersection. Say, if we queried for `y+1=42`, we'd first get two rw-classes to investigate, where the common
  list would be [1,2], and the indices at the rw-nodes [1] and [2], respectively.

- at this stage, if since we don't delete initial occurences of patterns, we could have the following, in the context of ↑
  if we query `x+1=42`, the common list would be [1] (because there is a single complete match),
  so that at rws we get [1] and [], the latter gets deleted as its empty

- the rw indices should also be among the regular ones ; for example, if we have rw classes {x,y} and {z,w} and expression
  `1 : x+z=42` ; f we didn't add them, the list of non-rw inidces would be empty for a query of `x+z=42`, for example.

-/


inductive RWblueprint (α : Type _) where
| exactMatch (classId : Option Nat) (indices : List α)
| node (classId : Option Nat) (indices : List α) (dirs : List (Nat × List α × List rwDirs)) (chi : List (RWblueprint α))
deriving Inhabited, BEq, Repr


def CExprTrie.find [BEq α] (r : α → α → Prop) [DecidableRel r] (ce : CExpr) (Top : CExprTrie α) (RW_classes : List (Nat × CExprTrie α)) : Option (RWblueprint α) :=
    let (first, fst_rws) := CExprTrie.find_step Top ce r
    match first with
    | [] => .none
    | _ =>
        match fst_rws with
        | [] => .some (.exactMatch .none [])
        | _ =>

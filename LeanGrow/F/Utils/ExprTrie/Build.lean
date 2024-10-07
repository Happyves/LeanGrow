
import LeanGrow.F.Utils.ExprTrie.Types
import LeanGrow.F.Utils.List

open Lean



def CExprTrie.empty {α : Type _} : CExprTrie α  := [(0,[])]


def CExprTrie.size : CExprTrie α → Nat := List.length

def CExprTrie.modifyAtLink (T : CExprTrie α ) (link : Nat) (modify : List (CExprTrie.Branch α)  → List (CExprTrie.Branch α )) : CExprTrie α :=
  List.findModify (fun p => p.1 == link) (fun (l,b) => (l, modify b)) T


def CExprTrie.modifyAtLink_withEffects [Inhabited α] (T : CExprTrie α) (link : Nat) (modify : List (CExprTrie.Branch α) → α × List (CExprTrie.Branch α)) : α × CExprTrie α :=
  let rec help : List (Nat × List (CExprTrie.Branch α)) → α × CExprTrie α
  | [] => (default, [])
  | (t, lb) :: L =>
        if t == link
        then
          let (res, new) := (modify lb)
          (res, (t,new) :: L)
        else
          let (res, new) := help L
          (res, (t, lb) :: new)
  help T

def CExprTrie.getAtLink (T : CExprTrie α) (link : Nat) :  List (CExprTrie.Branch α) :=
  match List.find? (fun p => p.1 == link) T with
  | .some lb => lb.2
  | _ => []



def CExprTrie.Branch_getAppLinks? : List (CExprTrie.Branch α) → Option (Nat × Nat)
| [] => .none
| x :: l =>
    match x with
    | .ofApp lf la => .some (lf,la)
    | _ => CExprTrie.Branch_getAppLinks? l


def CExprTrie.Branch_getLamLinks? : List (CExprTrie.Branch α) → Option (Nat × Nat)
| [] => .none
| x :: l =>
    match x with
    | .ofLam _ lf la _ => .some (lf,la)
    | _ => CExprTrie.Branch_getLamLinks? l

def CExprTrie.Branch_getForallLinks? : List (CExprTrie.Branch α) → Option (Nat × Nat)
| [] => .none
| x :: l =>
    match x with
    | .ofForall _ lf la _ => .some (lf,la)
    | _ => CExprTrie.Branch_getForallLinks? l

def CExprTrie.Branch_getLetLinks? : List (CExprTrie.Branch α) → Option (Nat × Nat × Nat)
| [] => .none
| x :: l =>
    match x with
    | .ofLet _ lf la lz _ => .some (lf,la,lz)
    | _ => CExprTrie.Branch_getLetLinks? l


def CExprTrie.Branch_getProjLinks? : List (CExprTrie.Branch α) → Option (Nat)
| [] => .none
| x :: l =>
    match x with
    | .ofProj _ _ l => .some l
    | _ => CExprTrie.Branch_getProjLinks? l

def CExprTrie.modifyAsLeaf_Lit [BEq α] (l : Literal) (idx : α) (r : α → α → Prop) [DecidableRel r]  : List (CExprTrie.Branch α) → List (CExprTrie.Branch α)
| [] => [.ofLit l [idx]]
| x :: xs =>
    match x with
    | .ofLit L ind =>
        if L == l
        then (.ofLit L (List.orderedInsertOrLeave r idx ind)) :: xs
        else (.ofLit L ind) :: (CExprTrie.modifyAsLeaf_Lit l idx r xs)
    | _ => x :: (CExprTrie.modifyAsLeaf_Lit l idx r xs)



def CExprTrie.modifyAsLeaf_Node [BEq α]  (l : Nat) (idx : α) (r : α → α → Prop) [DecidableRel r] : List (CExprTrie.Branch α) → List (CExprTrie.Branch α)
| [] => [.ofNode l [idx]]
| x :: xs =>
    match x with
    | .ofNode L ind =>
        if L == l
        then (.ofNode L (List.orderedInsertOrLeave r idx ind)) :: xs
        else (.ofNode L ind) :: (CExprTrie.modifyAsLeaf_Node l idx r xs)
    | _ => x :: (CExprTrie.modifyAsLeaf_Node l idx r xs)


def CExprTrie.modifyAsLeaf_Bvar [BEq α]  (l : Nat) (idx : α) (r : α → α → Prop) [DecidableRel r] : List (CExprTrie.Branch α) → List (CExprTrie.Branch α)
| [] => [.ofBvar l [idx]]
| x :: xs =>
    match x with
    | .ofBvar L ind =>
        if L == l
        then (.ofBvar L (List.orderedInsertOrLeave r idx ind)) :: xs
        else (.ofBvar L ind) :: (CExprTrie.modifyAsLeaf_Bvar l idx r xs)
    | _ => x :: (CExprTrie.modifyAsLeaf_Bvar l idx r xs)

def CExprTrie.modifyAsLeaf_Sort [BEq α]  (l : Level) (idx : α) (r : α → α → Prop) [DecidableRel r] : List (CExprTrie.Branch α) → List (CExprTrie.Branch α)
| [] => [.ofSort l [idx]]
| x :: xs =>
    match x with
    | .ofSort L ind =>
        if L == l
        then (.ofSort L (List.orderedInsertOrLeave r idx ind)) :: xs
        else (.ofSort L ind) :: (CExprTrie.modifyAsLeaf_Sort l idx r xs)
    | _ => x :: (CExprTrie.modifyAsLeaf_Sort l idx r xs)

def CExprTrie.modifyAsLeaf_Const [BEq α] (n : Name) (idx : α) (r : α → α → Prop) [DecidableRel r] : List (CExprTrie.Branch α) → List (CExprTrie.Branch α)
| [] => [.ofConst n [idx]]
| x :: xs =>
    match x with
    | .ofConst L ind =>
        if L == n
        then (.ofConst L (List.orderedInsertOrLeave r idx ind)) :: xs
        else (.ofConst L ind) :: (CExprTrie.modifyAsLeaf_Const n idx r xs)
    | _ => x :: (CExprTrie.modifyAsLeaf_Const n idx r xs)




-- TODO: make more efficient
def CExprTrie.insert [BEq α] (T : CExprTrie α) (idx : α) (ce : CExpr) (r : α → α → Prop) [DecidableRel r] : CExprTrie α :=
  let rec go (T : CExprTrie α ) (idx : α) (link count : Nat) : CExpr → (Nat × CExprTrie α)
    | .failed => (count, T)
    | .app f a =>
            let lb := CExprTrie.getAtLink T link
            let links? := CExprTrie.Branch_getAppLinks? lb
            match links? with
            | .some (lf,la) =>
                  let (swf,twf) := go T idx lf count f
                  go twf idx la swf a
            | _ =>
                  let nlb := (.ofApp (count) (count+1)) :: lb
                  let nT1 := CExprTrie.modifyAtLink T link (fun _ => nlb)
                  let (ns, nT2) := go ((count, []) :: nT1) idx count (count+2) f
                  go (((count+1), []) :: nT2) idx (count+1) ns a
    | .lam n f a i =>
            let lb := CExprTrie.getAtLink T link
            let links? := CExprTrie.Branch_getLamLinks? lb
            match links? with
            | .some (lf,la) =>
                  let (swf,twf) := go T idx lf count f
                  go twf idx la swf a
            | _ =>
                  let nlb := (.ofLam n (count) (count+1) i) :: lb
                  let nT1 := CExprTrie.modifyAtLink T link (fun _ => nlb)
                  let (ns, nT2) := go ((count, []) :: nT1) idx count (count+2) f
                  go (((count+1), []) :: nT2) idx (count+1) ns a
    | .forallE n f a i =>
            let lb := CExprTrie.getAtLink T link
            let links? := CExprTrie.Branch_getForallLinks? lb
            match links? with
            | .some (lf,la) =>
                  let (swf,twf) := go T idx lf count f
                  go twf idx la swf a
            | _ =>
                  let nlb := (.ofForall n (count) (count+1) i) :: lb
                  let nT1 := CExprTrie.modifyAtLink T link (fun _ => nlb)
                  let (ns, nT2) := go ((count, []) :: nT1) idx count (count+2) f
                  go (((count+1), []) :: nT2) idx (count+1) ns a
    | .letE n f a z i =>
            let lb := CExprTrie.getAtLink T link
            let links? := CExprTrie.Branch_getLetLinks? lb
            match links? with
            | .some (lf,la,lz) =>
                  let (swf,twf) := go T idx lf count f
                  let (swa,twa) := go twf idx la swf a
                  go twa idx lz swa z
            | _ =>
                  let nlb := (.ofLet n (count) (count+1) (count+2) i) :: lb
                  let nT1 := CExprTrie.modifyAtLink T link (fun _ => nlb)
                  let (ns1, nT2) := go ((count, []) :: nT1) idx count (count+3) f
                  let (ns2, nT3) := go ((count+1, []) :: nT2) idx (count+1) ns1 a
                  go ((count+2, []) :: nT3) idx (count+2) ns2 z
    | .proj n i e =>
            let lb := CExprTrie.getAtLink T link
            let links? := CExprTrie.Branch_getProjLinks? lb
            match links? with
            | .some l => go T idx l count e
            | _ =>
                  let nlb := (.ofProj n i (count)) :: lb
                  let nT1 := CExprTrie.modifyAtLink T link (fun _ => nlb)
                  go ((count, []) :: nT1) idx count (count+1) e
    | .lit l =>
            let lb := CExprTrie.getAtLink T link
            let nlb := CExprTrie.modifyAsLeaf_Lit l idx r lb
            (count, CExprTrie.modifyAtLink T link (fun _ => nlb))
    | .node l _ =>
            let lb := CExprTrie.getAtLink T link
            let nlb := CExprTrie.modifyAsLeaf_Node l idx r lb
            (count, CExprTrie.modifyAtLink T link (fun _ => nlb))
    | .bvar l =>
            let lb := CExprTrie.getAtLink T link
            let nlb := CExprTrie.modifyAsLeaf_Bvar l idx r lb
            (count, CExprTrie.modifyAtLink T link (fun _ => nlb))
    | .sort l =>
            let lb := CExprTrie.getAtLink T link
            let nlb := CExprTrie.modifyAsLeaf_Sort l idx r lb
            (count, CExprTrie.modifyAtLink T link (fun _ => nlb))
    | .const l _ =>
            let lb := CExprTrie.getAtLink T link
            let nlb := CExprTrie.modifyAsLeaf_Const l idx r lb
            (count, CExprTrie.modifyAtLink T link (fun _ => nlb))
  (go T idx 0 T.size ce).2


def CExprTrie.ofList [BEq α] (r : α → α → Prop) [DecidableRel r] (L : List (α × CExpr)) : CExprTrie α :=
  L.foldl (fun T (idx,ce) => CExprTrie.insert T idx ce r) CExprTrie.empty


def test_list : List (Nat × CExpr) :=
  [(1, .app (.app (.const `a []) (.const `b [])) (.const `c [])),
   (4, .app (.app (.const `a []) (.const `b [])) (.const `d [])),
   (42, .app (.app (.const `a []) (.const `e [])) (.const `c [])),
   (37, .forallE `dummy (.const `x []) (.const `y []) .default)
  ]

-- #eval CExprTrie.ofList (· ≤ ·) test_list




def CExprTrie.getIndices_Lit (l : Literal) : List (CExprTrie.Branch α) → List α
| [] => []
| x :: xs =>
    match x with
    | .ofLit L ind =>
        if L == l
        then ind
        else (CExprTrie.getIndices_Lit l  xs)
    | _ => (CExprTrie.getIndices_Lit l  xs)

def CExprTrie.getIndices_Node (l : Nat) : List (CExprTrie.Branch α) → List α
| [] => []
| x :: xs =>
    match x with
    | .ofNode L ind =>
        if L == l
        then ind
        else (CExprTrie.getIndices_Node l xs)
    | _ => (CExprTrie.getIndices_Node l xs)


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
        | .node l _ =>
            let lb := CExprTrie.getAtLink T link
            let nlb := CExprTrie.getIndices_Node l lb
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


def CExprTrie.find? [BEq α] (T : CExprTrie α) (ce : CExpr) (r : α → α → Prop) [DecidableRel r] : Option α :=
  let cand := CExprTrie.find_candidates? T ce r
  match cand with
  | [] => .none
  | h :: t =>
      let inter := t.foldl (fun x y => List.orderedIntersect r x y ) h
      inter.head?


-- #eval CExprTrie.find? (CExprTrie.ofList (· ≤ ·) test_list) (.app (.app (.const `a []) (.const `e [])) (.const `c [])) (· ≤ ·)


-- TODO : make more efficient
partial def CExprTrie.buildAtLink [BEq α] (T : CExprTrie α) (link : Nat) (r : α → α → Prop) [DecidableRel r] : List (CExpr × List α) :=
  let lb := CExprTrie.getAtLink T link
  let rec go : CExprTrie.Branch α → List (CExpr × List α)
    | .ofFailed => []
    | .ofApp lf la =>
          let fs := CExprTrie.buildAtLink T lf r
          let as := CExprTrie.buildAtLink T la r
          (fs.foldl (fun x y =>
            (as.foldl (fun X Y =>
              let inter := List.orderedIntersect r y.2 Y.2
              match inter with
              | [] => X
              | _ => (.app y.1 Y.1, inter) :: X
              )
              []) :: x
            )
            []).join
    | .ofLam n lf la i =>
          let fs := CExprTrie.buildAtLink T lf r
          let as := CExprTrie.buildAtLink T la r
          (fs.foldl (fun x y =>
            (as.foldl (fun X Y =>
              let inter := List.orderedIntersect r y.2 Y.2
              match inter with
              | [] => X
              | _ => (.lam n y.1 Y.1 i, inter) :: X
              )
              []) :: x
            )
            []).join
    | .ofForall n lf la i =>
          let fs := CExprTrie.buildAtLink T lf r
          let as := CExprTrie.buildAtLink T la r
          (fs.foldl (fun x y =>
            (as.foldl (fun X Y =>
              let inter := List.orderedIntersect r y.2 Y.2
              match inter with
              | [] => X
              | _ => (.lam n y.1 Y.1 i, inter) :: X
              )
              []) :: x
            )
            []).join
    | .ofLet n lf la lz i =>
          let fs := CExprTrie.buildAtLink T lf r
          let as := CExprTrie.buildAtLink T la r
          let zs := CExprTrie.buildAtLink T lz r
          (fs.foldl (fun x y =>
            (as.foldl (fun X Y =>
              (zs.foldl (fun z Z =>
                let interim := List.orderedIntersect r y.2 Y.2
                let inter := List.orderedIntersect r Z.2 interim
                match inter with
                | [] => z
                | _ => (.letE n y.1 Y.1 Z.1 i, inter) :: z
                )
              []) :: X
              )
              []).join :: x
            )
            []).join
    | .ofProj n i le =>
          let es := CExprTrie.buildAtLink T le r
          es.map (fun (ce,inter) => (.proj n i ce,inter))
    |.ofLit l ind => [(.lit l, ind)]
    |.ofNode l ind => [(.node l (.ofBvar 42), ind)] --fix
    |.ofBvar l ind => [(.bvar l , ind)]
    |.ofSort l ind => [(.sort l , ind)]
    |.ofConst l ind => [(.const l [], ind)] -- fix
  (lb.foldl (fun x y => (go y) :: x) []).join


#eval CExprTrie.buildAtLink (CExprTrie.ofList (· ≤ ·) test_list) 0 (· ≤ ·)

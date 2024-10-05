
import LeanGrow.F.Utils.ExprTrie.Types
import LeanGrow.F.Utils.List

open Lean



def CExprTrie.empty : CExprTrie := [(0,[])]


def CExprTrie.size : CExprTrie → Nat := List.length

def CExprTrie.modifyAtLink (T : CExprTrie) (link : Nat) (modify : List CExprTrie.Branch → List CExprTrie.Branch) : CExprTrie :=
  List.findModify (fun p => p.1 == link) (fun (l,b) => (l, modify b)) T


def CExprTrie.modifyAtLink_withEffects [Inhabited α] (T : CExprTrie) (link : Nat) (modify : List CExprTrie.Branch → α × List CExprTrie.Branch) : α × CExprTrie :=
  let rec help : List (Nat × List CExprTrie.Branch) → α × CExprTrie
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

def CExprTrie.getAtLink (T : CExprTrie) (link : Nat) :  List CExprTrie.Branch :=
  match List.find? (fun p => p.1 == link) T with
  | .some lb => lb.2
  | _ => []



def CExprTrie.Branch_getAppLinks? : List CExprTrie.Branch → Option (Nat × Nat)
| [] => .none
| x :: l =>
    match x with
    | .ofApp lf la => .some (lf,la)
    | _ => CExprTrie.Branch_getAppLinks? l


def CExprTrie.Branch_getLamLinks? : List CExprTrie.Branch → Option (Nat × Nat)
| [] => .none
| x :: l =>
    match x with
    | .ofLam _ lf la _ => .some (lf,la)
    | _ => CExprTrie.Branch_getLamLinks? l

def CExprTrie.Branch_getForallLinks? : List CExprTrie.Branch → Option (Nat × Nat)
| [] => .none
| x :: l =>
    match x with
    | .ofForall _ lf la _ => .some (lf,la)
    | _ => CExprTrie.Branch_getForallLinks? l

def CExprTrie.Branch_getLetLinks? : List CExprTrie.Branch → Option (Nat × Nat × Nat)
| [] => .none
| x :: l =>
    match x with
    | .ofLet _ lf la lz _ => .some (lf,la,lz)
    | _ => CExprTrie.Branch_getLetLinks? l


def CExprTrie.Branch_getProjLinks? : List CExprTrie.Branch → Option (Nat)
| [] => .none
| x :: l =>
    match x with
    | .ofProj _ _ l => .some l
    | _ => CExprTrie.Branch_getProjLinks? l

def CExprTrie.modifyAsLeaf_Lit (l : Literal) (idx : Nat)  : List CExprTrie.Branch → List CExprTrie.Branch
| [] => [.ofLit l [idx]]
| x :: xs =>
    match x with
    | .ofLit L ind =>
        if L == l
        then (.ofLit L (List.orderedInsertOrLeave (· ≤ ·) idx ind)) :: xs
        else (.ofLit L ind) :: (CExprTrie.modifyAsLeaf_Lit l idx xs)
    | _ => x :: (CExprTrie.modifyAsLeaf_Lit l idx xs)



def CExprTrie.modifyAsLeaf_Node (l : Nat) (idx : Nat)  : List CExprTrie.Branch → List CExprTrie.Branch
| [] => [.ofNode l [idx]]
| x :: xs =>
    match x with
    | .ofNode L ind =>
        if L == l
        then (.ofNode L (List.orderedInsertOrLeave (· ≤ ·) idx ind)) :: xs
        else (.ofNode L ind) :: (CExprTrie.modifyAsLeaf_Node l idx xs)
    | _ => x :: (CExprTrie.modifyAsLeaf_Node l idx xs)


def CExprTrie.modifyAsLeaf_Bvar (l : Nat) (idx : Nat)  : List CExprTrie.Branch → List CExprTrie.Branch
| [] => [.ofBvar l [idx]]
| x :: xs =>
    match x with
    | .ofBvar L ind =>
        if L == l
        then (.ofBvar L (List.orderedInsertOrLeave (· ≤ ·) idx ind)) :: xs
        else (.ofBvar L ind) :: (CExprTrie.modifyAsLeaf_Bvar l idx xs)
    | _ => x :: (CExprTrie.modifyAsLeaf_Bvar l idx xs)

def CExprTrie.modifyAsLeaf_Sort (l : Level) (idx : Nat)  : List CExprTrie.Branch → List CExprTrie.Branch
| [] => [.ofSort l [idx]]
| x :: xs =>
    match x with
    | .ofSort L ind =>
        if L == l
        then (.ofSort L (List.orderedInsertOrLeave (· ≤ ·) idx ind)) :: xs
        else (.ofSort L ind) :: (CExprTrie.modifyAsLeaf_Sort l idx xs)
    | _ => x :: (CExprTrie.modifyAsLeaf_Sort l idx xs)

def CExprTrie.modifyAsLeaf_Const (n : Name) (idx : Nat)  : List CExprTrie.Branch → List CExprTrie.Branch
| [] => [.ofConst n [idx]]
| x :: xs =>
    match x with
    | .ofConst L ind =>
        if L == n
        then (.ofConst L (List.orderedInsertOrLeave (· ≤ ·) idx ind)) :: xs
        else (.ofConst L ind) :: (CExprTrie.modifyAsLeaf_Const n idx xs)
    | _ => x :: (CExprTrie.modifyAsLeaf_Const n idx xs)






def CExprTrie.insert (T : CExprTrie) (idx : Nat) (ce : CExpr) : CExprTrie :=
  let rec go (T : CExprTrie) (idx link count : Nat) : CExpr → (Nat × CExprTrie)
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
            let nlb := CExprTrie.modifyAsLeaf_Lit l idx lb
            (count, CExprTrie.modifyAtLink T link (fun _ => nlb))
    | .node l _ =>
            let lb := CExprTrie.getAtLink T link
            let nlb := CExprTrie.modifyAsLeaf_Node l idx lb
            (count, CExprTrie.modifyAtLink T link (fun _ => nlb))
    | .bvar l =>
            let lb := CExprTrie.getAtLink T link
            let nlb := CExprTrie.modifyAsLeaf_Bvar l idx lb
            (count, CExprTrie.modifyAtLink T link (fun _ => nlb))
    | .sort l =>
            let lb := CExprTrie.getAtLink T link
            let nlb := CExprTrie.modifyAsLeaf_Sort l idx lb
            (count, CExprTrie.modifyAtLink T link (fun _ => nlb))
    | .const l _ =>
            let lb := CExprTrie.getAtLink T link
            let nlb := CExprTrie.modifyAsLeaf_Const l idx lb
            (count, CExprTrie.modifyAtLink T link (fun _ => nlb))
  (go T idx 0 T.size ce).2


def CExprTrie.ofList (L : List (Nat × CExpr)) : CExprTrie :=
  L.foldl (fun T (idx,ce) => CExprTrie.insert T idx ce) CExprTrie.empty


def test_list : List (Nat × CExpr) :=
  [(1, .app (.app (.const `a []) (.const `b [])) (.const `c [])),
   (4, .app (.app (.const `a []) (.const `b [])) (.const `d [])),
   (42, .app (.app (.const `a []) (.const `e [])) (.const `c [])),
  ]

#eval CExprTrie.ofList  test_list

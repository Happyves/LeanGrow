
import LeanGrow.F.Utils.ExprTrieRWez.Types
import LeanGrow.F.Utils.List
import LeanGrow.F.Utils.Tracing

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
    | .ofApp lf la _ _ _ => .some (lf,la)
    | _ => CExprTrie.Branch_getAppLinks? l


def CExprTrie.Branch_getLamLinks? : List (CExprTrie.Branch α) → Option (Nat × Nat)
| [] => .none
| x :: l =>
    match x with
    | .ofLam lf la _ _ _ => .some (lf,la)
    | _ => CExprTrie.Branch_getLamLinks? l

def CExprTrie.Branch_getForallLinks? : List (CExprTrie.Branch α) → Option (Nat × Nat)
| [] => .none
| x :: l =>
    match x with
    | .ofForall lf la _ _ _ => .some (lf,la)
    | _ => CExprTrie.Branch_getForallLinks? l

def CExprTrie.Branch_getLetLinks? : List (CExprTrie.Branch α) → Option (Nat × Nat × Nat)
| [] => .none
| x :: l =>
    match x with
    | .ofLet lf la lz _ _ _ _=> .some (lf,la,lz)
    | _ => CExprTrie.Branch_getLetLinks? l


def CExprTrie.Branch_getProjLinks? : List (CExprTrie.Branch α) → Option (Nat)
| [] => .none
| x :: l =>
    match x with
    | .ofProj _ _ l _ _ => .some l
    | _ => CExprTrie.Branch_getProjLinks? l


-- These will reverse the branch order, which could be a problem if we impose and order on these CExprTries
def CExprTrie.BranchUpdateApp [BEq α] (r : α → α → Prop) [DecidableRel r]
    (idx : α) (fl al: List Nat)
    (done : List (CExprTrie.Branch α)):
    List (CExprTrie.Branch α) → List (CExprTrie.Branch α)
    | [] => done
    | x :: l =>
        match x with
        | .ofApp lf la I fB aB => CExprTrie.BranchUpdateApp r idx fl al ((.ofApp lf la (List.orderedInsertOrLeave r idx I) (fl ++ fB) (al ++ aB)) :: done) l
        | _ => CExprTrie.BranchUpdateApp r idx fl al (x :: done) l

def CExprTrie.BranchUpdateLam [BEq α] (r : α → α → Prop) [DecidableRel r]
    (idx : α) (fl al: List Nat)
    (done : List (CExprTrie.Branch α)):
    List (CExprTrie.Branch α) → List (CExprTrie.Branch α)
    | [] => done
    | x :: l =>
        match x with
        | .ofLam lf la I fB aB => CExprTrie.BranchUpdateLam r idx fl al ((.ofLam lf la (List.orderedInsertOrLeave r idx I) (fl ++ fB) (al ++ aB)) :: done) l
        | _ => CExprTrie.BranchUpdateLam r idx fl al (x :: done) l

def CExprTrie.BranchUpdateForall [BEq α] (r : α → α → Prop) [DecidableRel r]
    (idx : α) (fl al: List Nat)
    (done : List (CExprTrie.Branch α)):
    List (CExprTrie.Branch α) → List (CExprTrie.Branch α)
    | [] => done
    | x :: l =>
        match x with
        | .ofForall lf la I fB aB => CExprTrie.BranchUpdateForall r idx fl al ((.ofForall lf la (List.orderedInsertOrLeave r idx I) (fl ++ fB) (al ++ aB)) :: done) l
        | _ => CExprTrie.BranchUpdateForall r idx fl al (x :: done) l

def CExprTrie.BranchUpdateLet [BEq α] (r : α → α → Prop) [DecidableRel r]
    (idx : α) (fl al zl: List Nat)
    (done : List (CExprTrie.Branch α)):
    List (CExprTrie.Branch α) → List (CExprTrie.Branch α)
    | [] => done
    | x :: l =>
        match x with
        | .ofLet lf la lz I fB aB zB => CExprTrie.BranchUpdateLet r idx fl al zl ((.ofLet lf la lz (List.orderedInsertOrLeave r idx I) (fl ++ fB) (al ++ aB) (zl ++ zB)) :: done) l
        | _ => CExprTrie.BranchUpdateLet r idx fl al zl (x :: done) l



def CExprTrie.BranchUpdateProj [BEq α] (r : α → α → Prop) [DecidableRel r]
    (idx : α) (fl: List Nat)
    (done : List (CExprTrie.Branch α)):
    List (CExprTrie.Branch α) → List (CExprTrie.Branch α)
    | [] => done
    | x :: l =>
        match x with
        | .ofProj n i lf I fB => CExprTrie.BranchUpdateProj r idx fl ((.ofProj n i lf (List.orderedInsertOrLeave r idx I) (fl ++ fB)) :: done) l
        | _ => CExprTrie.BranchUpdateProj r idx fl (x :: done) l




def CExprTrie.modifyAsLeaf_Lit [BEq α] (l : Literal) (idx : α) (r : α → α → Prop) [DecidableRel r]  : List (CExprTrie.Branch α) → List (CExprTrie.Branch α)
| [] => [.ofLit l [idx]]
| x :: xs =>
    match x with
    | .ofLit L ind =>
        if L == l
        then (.ofLit L (List.orderedInsertOrLeave r idx ind)) :: xs
        else (.ofLit L ind) :: (CExprTrie.modifyAsLeaf_Lit l idx r xs)
    | _ => x :: (CExprTrie.modifyAsLeaf_Lit l idx r xs)



def CExprTrie.modifyAsLeaf_lNode [BEq α]  (l : Nat) (tag : Option Nat) (idx : α) (r : α → α → Prop) [DecidableRel r] : List (CExprTrie.Branch α) → List (CExprTrie.Branch α)
| [] => [.ofLNode l tag [idx]]
| x :: xs =>
    match x with
    | .ofLNode L t ind =>
        if L == l && t == tag
        then (.ofLNode L t (List.orderedInsertOrLeave r idx ind)) :: xs
        else (.ofLNode L t ind) :: (CExprTrie.modifyAsLeaf_lNode l tag idx r xs)
    | _ => x :: (CExprTrie.modifyAsLeaf_lNode l tag idx r xs)


def CExprTrie.modifyAsLeaf_gNode [BEq α]  (l : Nat) (idx : α) (r : α → α → Prop) [DecidableRel r] : List (CExprTrie.Branch α) → List (CExprTrie.Branch α)
| [] => [.ofGNode l [idx]]
| x :: xs =>
    match x with
    | .ofGNode L ind =>
        if L == l
        then (.ofGNode L (List.orderedInsertOrLeave r idx ind)) :: xs
        else (.ofGNode L ind) :: (CExprTrie.modifyAsLeaf_gNode l idx r xs)
    | _ => x :: (CExprTrie.modifyAsLeaf_gNode l idx r xs)




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
  let rec go (T : CExprTrie α ) (idx : α) (link count : Nat) : CExpr → (Nat × List Nat × CExprTrie α)
    | .failed => (count, [], T)
    | .app f a =>
            let lb := CExprTrie.getAtLink T link
            let (links?) := CExprTrie.Branch_getAppLinks? lb
            match links? with
            | .some (lf,la) =>
                  let (swf,nf,twf) := go T idx lf count f
                  let (swa,na,twa) := go twf idx la swf a
                  let nlb := CExprTrie.BranchUpdateApp r idx nf na [] lb
                  (swa, nf ++ na, CExprTrie.modifyAtLink twa link (fun _ => nlb))
            | _ =>
                  let (ns1, n1, nT1) := go ((count, []) :: T) idx count (count+2) f
                  let (ns2, n2, nT2) := go (((count+1), []) :: nT1) idx (count+1) ns1 a
                  let nlb := (.ofApp (count) (count+1) [idx] n1 n2) :: lb
                  (ns2, (count) :: (count+1) :: (n1 ++ n2), CExprTrie.modifyAtLink nT2 link (fun _ => nlb))
    | .lam _ f a _ =>
            let lb := CExprTrie.getAtLink T link
            let links? := CExprTrie.Branch_getLamLinks?  lb
            match links? with
            | .some (lf,la) =>
                  let (swf,nf,twf) := go T idx lf count f
                  let (swa,na,twa) := go twf idx la swf a
                  let nlb := CExprTrie.BranchUpdateLam r idx nf na [] lb
                  (swa, (count) :: (count+1) :: (nf ++ na), CExprTrie.modifyAtLink twa link (fun _ => nlb))
            | _ =>
                  let (ns1, n1, nT1) := go ((count, []) :: T) idx count (count+2) f
                  let (ns2, n2, nT2) := go (((count+1), []) :: nT1) idx (count+1) ns1 a
                  let nlb := (.ofLam (count) (count+1) [idx] n1 n2) :: lb
                  (ns2, (count) :: (count+1) :: (n1 ++ n2), CExprTrie.modifyAtLink nT2 link (fun _ => nlb))
    | .forallE _ f a _ =>
            let lb := CExprTrie.getAtLink T link
            let links? := CExprTrie.Branch_getForallLinks?  lb
            match links? with
            | .some (lf,la) =>
                  let (swf,nf,twf) := go T idx lf count f
                  let (swa,na,twa) := go twf idx la swf a
                  let nlb := CExprTrie.BranchUpdateForall r idx nf na [] lb
                  (swa, (count) :: (count+1) :: (nf ++ na), CExprTrie.modifyAtLink twa link (fun _ => nlb))
            | _ =>
                  let (ns1, n1, nT1) := go ((count, []) :: T) idx count (count+2) f
                  let (ns2, n2, nT2) := go (((count+1), []) :: nT1) idx (count+1) ns1 a
                  let nlb := (.ofForall (count) (count+1) [idx] n1 n2) :: lb
                  (ns2, (count) :: (count+1) :: (n1 ++ n2), CExprTrie.modifyAtLink nT2 link (fun _ => nlb))
    | .letE _ f a z _ =>
            let lb := CExprTrie.getAtLink T link
            let links? := CExprTrie.Branch_getLetLinks?  lb
            match links? with
            | .some (lf,la,lz) =>
                  let (swf,nf,twf) := go T idx lf count f
                  let (swa,na,twa) := go twf idx la swf a
                  let (swz,nz,twz) := go twa idx lz swa z
                  let nlb := CExprTrie.BranchUpdateLet r idx nf na nz [] lb
                  (swz, (count) :: (count+1) :: (count+2) :: (nf ++ na ++ nz), CExprTrie.modifyAtLink twz link (fun _ => nlb))
            | _ =>
                  let (ns1, n1, nT1) := go ((count, []) :: T) idx count (count+3) f
                  let (ns2, n2, nT2) := go (((count+1), []) :: nT1) idx (count+1) ns1 a
                  let (ns3, n3, nT3) := go (((count+2), []) :: nT2) idx (count+2) ns2 z
                  let nlb := (.ofLet (count) (count+1) (count+2) [idx] n1 n2 n3) :: lb
                  (ns3, (count) :: (count+1) :: (count+2) :: (n1 ++ n2 ++ n3), CExprTrie.modifyAtLink nT3 link (fun _ => nlb))
    | .proj n i e =>
            let lb := CExprTrie.getAtLink T link
            let links? := CExprTrie.Branch_getProjLinks?  lb
            match links? with
            | .some l =>
                  let (swf,nf,twf) := go T idx l count e
                  let nlb := CExprTrie.BranchUpdateProj r idx nf [] lb
                  (swf, count :: nf, CExprTrie.modifyAtLink twf link (fun _ => nlb))
            | _ =>
                  let (ns1, n1, nT1) := go ((count, []) :: T) idx count (count+1) e
                  let nlb := (.ofProj n i (count) [idx] n1) :: lb
                  (ns1, count :: n1, CExprTrie.modifyAtLink nT1 link (fun _ => nlb))
    | .lit l =>
            let lb := CExprTrie.getAtLink T link
            let nlb := CExprTrie.modifyAsLeaf_Lit l idx r lb
            (count, [] , CExprTrie.modifyAtLink T link (fun _ => nlb))
    | .lnode l _ t =>
            let lb := CExprTrie.getAtLink T link
            let nlb := CExprTrie.modifyAsLeaf_lNode l t idx r lb
            (count, [] , CExprTrie.modifyAtLink T link (fun _ => nlb))
    | .gnode l _ =>
            let lb := CExprTrie.getAtLink T link
            let nlb := CExprTrie.modifyAsLeaf_gNode l idx r lb
            (count, [] , CExprTrie.modifyAtLink T link (fun _ => nlb))
    | .bvar l =>
            let lb := CExprTrie.getAtLink T link
            let nlb := CExprTrie.modifyAsLeaf_Bvar l idx r lb
            (count, [] , CExprTrie.modifyAtLink T link (fun _ => nlb))
    | .sort l =>
            let lb := CExprTrie.getAtLink T link
            let nlb := CExprTrie.modifyAsLeaf_Sort l idx r lb
            (count, [] , CExprTrie.modifyAtLink T link (fun _ => nlb))
    | .const l _ =>
            let lb := CExprTrie.getAtLink T link
            let nlb := CExprTrie.modifyAsLeaf_Const l idx r lb
            (count, [] , CExprTrie.modifyAtLink T link (fun _ => nlb))
  (go T idx 0 T.size ce).2.2





def CExprTrie.ofList [BEq α] (r : α → α → Prop) [DecidableRel r] (L : List (α × CExpr)) : CExprTrie α :=
  L.foldl (fun T (idx,ce) => CExprTrie.insert T idx ce r) CExprTrie.empty


def test_list : List (Nat × CExpr) :=
  [(1, .app (.app (.const `a []) (.const `b [])) (.const `c [])),
   (4, .app (.app (.const `a []) (.const `b [])) (.const `d [])),
   (42, .app (.app (.const `a []) (.const `e [])) (.const `c [])),
   (37, .forallE `dummy (.const `x []) (.const `y []) .default)
  ]

#eval CExprTrie.ofList (· ≤ ·) test_list

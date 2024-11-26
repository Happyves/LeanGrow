
import LeanGrow.F.Utils.ExprTrieRWez.Types
import LeanGrow.F.Utils.List
import LeanGrow.F.Utils.Tracing

open Lean

def CExprTrie.BranchUpdateAppD [BEq α] (r : α → α → Prop) [DecidableRel r]
    (idx : α) (fl al: List Nat)
    (done : List (CExprTrie.Branch α)):
    List (CExprTrie.Branch α) → List (CExprTrie.Branch α)
    | [] => done
    | x :: l =>
        match x with
        | .ofApp lf la I fB aB ref =>
            if ref == 1
            then CExprTrie.BranchUpdateAppD r idx fl al done l
            else CExprTrie.BranchUpdateAppD r idx fl al ((.ofApp lf la (List.orderedInsertOrLeave r idx I) (fl ++ fB) (al ++ aB) (ref - 1)) :: done) l
        | _ => CExprTrie.BranchUpdateAppD r idx fl al (x :: done) l


def CExprTrie.BranchUpdateLamD [BEq α] (r : α → α → Prop) [DecidableRel r]
    (idx : α) (fl al: List Nat)
    (done : List (CExprTrie.Branch α)):
    List (CExprTrie.Branch α) → List (CExprTrie.Branch α)
    | [] => done
    | x :: l =>
        match x with
        | .ofLam lf la I fB aB ref =>
            if ref == 1
            then CExprTrie.BranchUpdateLamD r idx fl al done l
            else CExprTrie.BranchUpdateLamD r idx fl al ((.ofLam lf la (List.orderedInsertOrLeave r idx I) (fl ++ fB) (al ++ aB) (ref - 1)) :: done) l
        | _ => CExprTrie.BranchUpdateLamD r idx fl al (x :: done) l


def CExprTrie.BranchUpdateForallD [BEq α] (r : α → α → Prop) [DecidableRel r]
    (idx : α) (fl al: List Nat)
    (done : List (CExprTrie.Branch α)):
    List (CExprTrie.Branch α) → List (CExprTrie.Branch α)
    | [] => done
    | x :: l =>
        match x with
        | .ofForall lf la I fB aB ref =>
            if ref == 1
            then CExprTrie.BranchUpdateForallD r idx fl al done l
            else CExprTrie.BranchUpdateForallD r idx fl al ((.ofForall lf la (List.orderedInsertOrLeave r idx I) (fl ++ fB) (al ++ aB) (ref - 1)) :: done) l
        | _ => CExprTrie.BranchUpdateForallD r idx fl al (x :: done) l


def CExprTrie.BranchUpdateLetD [BEq α] (r : α → α → Prop) [DecidableRel r]
    (idx : α) (fl al zl: List Nat)
    (done : List (CExprTrie.Branch α)):
    List (CExprTrie.Branch α) → List (CExprTrie.Branch α)
    | [] => done
    | x :: l =>
        match x with
        | .ofLet lf la lz I fB aB zB ref =>
            if ref == 1
            then CExprTrie.BranchUpdateLetD r idx fl al zl done l
            else CExprTrie.BranchUpdateLetD r idx fl al zl ((.ofLet lf la lz (List.orderedInsertOrLeave r idx I) (fl ++ fB) (al ++ aB) (zl ++ zB) (ref - 1)) :: done) l
        | _ => CExprTrie.BranchUpdateLetD r idx fl al zl (x :: done) l


def CExprTrie.BranchUpdateProjD [BEq α] (r : α → α → Prop) [DecidableRel r]
    (idx : α) (fl : List Nat)
    (done : List (CExprTrie.Branch α)):
    List (CExprTrie.Branch α) → List (CExprTrie.Branch α)
    | [] => done
    | x :: l =>
        match x with
        | .ofProj n i le I B ref =>
            if ref == 1
            then CExprTrie.BranchUpdateProjD r idx fl done l
            else CExprTrie.BranchUpdateProjD r idx fl ((.ofProj n i le (List.orderedInsertOrLeave r idx I) (fl ++ B) (ref - 1)) :: done) l
        | _ => CExprTrie.BranchUpdateProjD r idx fl (x :: done) l



def CExprTrie.modifyAsLeaf_Lit_D [BEq α] (l : Literal) (idx : α) (r : α → α → Prop) [DecidableRel r]  : List (CExprTrie.Branch α) → List (CExprTrie.Branch α)
| [] => []
| x :: xs =>
    match x with
    | .ofLit L ind ref =>
        if L == l
        then (.ofLit L (List.orderedInsertOrLeave r idx ind) (Nat.succ ref)) :: xs
        else (.ofLit L ind ref) :: (CExprTrie.modifyAsLeaf_Lit l idx r xs)
    | _ => x :: (CExprTrie.modifyAsLeaf_Lit l idx r xs)

-- BIG TODO : delete index in index-dirs too !!!

#exit


def CExprTrie.delete_at [BEq α] (T : CExprTrie α) (start : Nat) (idx : α) (ce : CExpr) (r : α → α → Prop) [DecidableRel r] : CExprTrie α :=
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
                  let nlb := (.ofApp (count) (count+1) [idx] n1 n2 1) :: lb
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
                  let nlb := (.ofLam (count) (count+1) [idx] n1 n2 1) :: lb
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
                  let nlb := (.ofForall (count) (count+1) [idx] n1 n2 1) :: lb
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
                  let nlb := (.ofLet (count) (count+1) (count+2) [idx] n1 n2 n3 1) :: lb
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
                  let nlb := (.ofProj n i (count) [idx] n1 1) :: lb
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
    | .const n l =>
            let lb := CExprTrie.getAtLink T link
            let nlb := CExprTrie.modifyAsLeaf_Const n l idx r lb
            (count, [] , CExprTrie.modifyAtLink T link (fun _ => nlb))
  (go T idx start T.size ce).2.2

#exit

def CExprTrie.insert [BEq α] (T : CExprTrie α) (idx : α) (ce : CExpr) (r : α → α → Prop) [DecidableRel r] : CExprTrie α :=
    CExprTrie.insert_at T 0 idx ce r

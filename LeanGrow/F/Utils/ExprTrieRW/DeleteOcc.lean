
import LeanGrow.F.Utils.ExprTrieRW.Query


open Lean


-- This content is a temporary solution
-- Deletion should be handled more efficiently if I add a reference counting system of sorts to the structure


def List.erasePred (p : α → Bool) (l : List α) : List α :=
  let rec go (keep : List α) : List α → List α
    | [] => keep
    | x :: xs => if p x then go keep xs else go (x :: keep) xs
  go [] l

/-- Very  unsafe, as it deletes branches that may be neede to represent other expressions then the one to delete-/
partial def CExprTrie.deleteCExprAtLink [BEq α] [Repr α] (r : α → α → Prop) [DecidableRel r] (ce : CExpr) (T : CExprTrie α) (link : Nat) : CExprTrie α :=
  let rec go (T : CExprTrie α) : List (CExpr × Nat) → CExprTrie α
    | [] => T
    | (nx, link) :: more =>
        match nx with
        | .failed => []
        | .app f a =>
            let lb := CExprTrie.getAtLink T link
            let links? := CExprTrie.Branch_getAppLinks? lb
            match links? with
            | .some (lf,la) =>
                let newT := CExprTrie.modifyAtLink T link (fun _ => lb.erasePred (fun x => match x with | .ofApp _ _ => true | _ => false))
                go newT ((f, lf) :: (a,la) :: more)
            | _ => T
        | .lam _ f a _ =>
            let lb := CExprTrie.getAtLink T link
            let links? := CExprTrie.Branch_getLamLinks? lb
            match links? with
            | .some (lf,la) =>
                let newT := CExprTrie.modifyAtLink T link (fun _ => lb.erasePred (fun x => match x with | .ofLam _ _ _ _  => true | _ => false))
                go newT ((f, lf) :: (a,la) :: more)
            | _ => T
        | .forallE _ f a _ =>
            let lb := CExprTrie.getAtLink T link
            let links? := CExprTrie.Branch_getForallLinks? lb
            match links? with
            | .some (lf,la) =>
                let newT := CExprTrie.modifyAtLink T link (fun _ => lb.erasePred (fun x => match x with | .ofForall _ _ _ _ => true | _ => false))
                go newT ((f, lf) :: (a,la) :: more)
            | _ => T
        | .letE _ f a z _ =>
            let lb := CExprTrie.getAtLink T link
            let links? := CExprTrie.Branch_getLetLinks? lb
            match links? with
            | .some (lf,la, lz) =>
                let newT := CExprTrie.modifyAtLink T link (fun _ => lb.erasePred (fun x => match x with | .ofLet _ _ _ _ _ => true | _ => false))
                go newT ((f, lf) :: (a,la) :: (z,lz) :: more)
            | _ => T
        | .proj _ _ f =>
            let lb := CExprTrie.getAtLink T link
            let links? := CExprTrie.Branch_getProjLinks? lb
            match links? with
            | .some (lf) =>
                let newT := CExprTrie.modifyAtLink T link (fun _ => lb.erasePred (fun x => match x with | .ofProj _ _ _ => true | _ => false))
                go newT ((f, lf) :: more)
            | _ => T
        | .lit l =>
            let lb := CExprTrie.getAtLink T link
            let newT := CExprTrie.modifyAtLink T link (fun _ => lb.erasePred (fun x => match x with | .ofLit L _ => l == L | _ => false))
            go newT more
        | .lnode l _ t =>
            let lb := CExprTrie.getAtLink T link
            let newT := CExprTrie.modifyAtLink T link (fun _ => lb.erasePred (fun x => match x with | .ofLNode L tr _ => (l == L) && (t == tr) | _ => false))
            go newT more
        | .gnode l _ =>
            let lb := CExprTrie.getAtLink T link
            let newT := CExprTrie.modifyAtLink T link (fun _ => lb.erasePred (fun x => match x with | .ofGNode L _ => l == L | _ => false))
            go newT more
        | .bvar l =>
            let lb := CExprTrie.getAtLink T link
            let newT := CExprTrie.modifyAtLink T link (fun _ => lb.erasePred (fun x => match x with | .ofBvar L _ => l == L | _ => false))
            go newT more
        | .sort l =>
            let lb := CExprTrie.getAtLink T link
            let newT := CExprTrie.modifyAtLink T link (fun _ => lb.erasePred (fun x => match x with | .ofSort L _ => l == L | _ => false))
            go newT more
        | .const l _ =>
            let lb := CExprTrie.getAtLink T link
            let newT := CExprTrie.modifyAtLink T link (fun _ => lb.erasePred (fun x => match x with | .ofConst L _ => l == L | _ => false))
            go newT more
  go T [(ce, link)]


partial def CExprTrie.mitigatedDeleteCExprAtLink [BEq α] [Repr α] (r : α → α → Prop) [DecidableRel r] (ce : CExpr) (T : CExprTrie α) (link : Nat) : CExprTrie α :=
  let rec go (T : CExprTrie α) : List (CExpr × Nat) → CExprTrie α
    | [] => T
    | (nx, link) :: more =>
        match nx with
        | .failed => []
        | .app f a =>
            let lb := CExprTrie.getAtLink T link
            let links? := CExprTrie.Branch_getAppLinks? lb
            match links? with
            | .some (lf,la) =>
                go T ((f, lf) :: (a,la) :: more)
            | _ => T
        | .lam _ f a _ =>
            let lb := CExprTrie.getAtLink T link
            let links? := CExprTrie.Branch_getLamLinks? lb
            match links? with
            | .some (lf,la) =>
                go T ((f, lf) :: (a,la) :: more)
            | _ => T
        | .forallE _ f a _ =>
            let lb := CExprTrie.getAtLink T link
            let links? := CExprTrie.Branch_getForallLinks? lb
            match links? with
            | .some (lf,la) =>
                go T ((f, lf) :: (a,la) :: more)
            | _ => T
        | .letE _ f a z _ =>
            let lb := CExprTrie.getAtLink T link
            let links? := CExprTrie.Branch_getLetLinks? lb
            match links? with
            | .some (lf,la, lz) =>
                go T ((f, lf) :: (a,la) :: (z,lz) :: more)
            | _ => T
        | .proj _ _ f =>
            let lb := CExprTrie.getAtLink T link
            let links? := CExprTrie.Branch_getProjLinks? lb
            match links? with
            | .some (lf) =>
                go T ((f, lf) :: more)
            | _ => T
        | .lit l =>
            let lb := CExprTrie.getAtLink T link
            let newT := CExprTrie.modifyAtLink T link (fun _ => lb.erasePred (fun x => match x with | .ofLit L _ => l == L | _ => false))
            go newT more
        | .lnode l _ t =>
            let lb := CExprTrie.getAtLink T link
            let newT := CExprTrie.modifyAtLink T link (fun _ => lb.erasePred (fun x => match x with | .ofLNode L tr _ => (l == L) && (t == tr) | _ => false))
            go newT more
        | .gnode l _ =>
            let lb := CExprTrie.getAtLink T link
            let newT := CExprTrie.modifyAtLink T link (fun _ => lb.erasePred (fun x => match x with | .ofGNode L _ => l == L | _ => false))
            go newT more
        | .bvar l =>
            let lb := CExprTrie.getAtLink T link
            let newT := CExprTrie.modifyAtLink T link (fun _ => lb.erasePred (fun x => match x with | .ofBvar L _ => l == L | _ => false))
            go newT more
        | .sort l =>
            let lb := CExprTrie.getAtLink T link
            let newT := CExprTrie.modifyAtLink T link (fun _ => lb.erasePred (fun x => match x with | .ofSort L _ => l == L | _ => false))
            go newT more
        | .const l _ =>
            let lb := CExprTrie.getAtLink T link
            let newT := CExprTrie.modifyAtLink T link (fun _ => lb.erasePred (fun x => match x with | .ofConst L _ => l == L | _ => false))
            go newT more
  go T [(ce, link)]

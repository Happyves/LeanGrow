
import LeanGrow.F.Utils.ExprTrieRWez.Unify

open Lean


partial def CExprTrie.find_occurences_candidates [BEq α] (T : CExprTrie α) (ce : CExpr) (r : α → α → Prop) [DecidableRel r] (start : Nat) : List (List α) :=
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
-- **TODO** refer to the refactor in `Query`
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
        | .const n l =>
            let lb := CExprTrie.getAtLink T link
            let nlb := CExprTrie.getIndices_Const n l lb
            go (nlb :: done) more
  go [] [(ce,start)]



def CExprTrie.find_occurences [BEq α] (T : CExprTrie α) (ce : CExpr) (r : α → α → Prop) [DecidableRel r] : List (Nat × List α) :=
    let rec go (done : List (Nat × List α)) : List (Nat × List (CExprTrie.Branch α)) → List (Nat × List α)
        | [] => done
        | (link, br) :: rest =>
            let cand_here := CExprTrie.find_occurences_candidates ((link, br) :: rest) ce r link
            let inter :=
                match cand_here with
                | [] => []
                | h :: t => t.foldl (fun x y => List.orderedIntersect r x y ) h
            match inter with
            | [] => go done rest
            | _ => go ((link, inter) :: done) rest
    go [] (List.reverse T)

#eval CExprTrie.find_occurences (CExprTrie.ofList (· ≤ ·) test_list) (.app (.const `a []) (.const `b [])) (· ≤ ·)


def CExprTrie.unify_occurences [BEq α] [Repr α] (T : CExprTrie α) (ce : CExpr) (r : α → α → Prop) [DecidableRel r] : List (Nat × List (α × List (Nat × CExpr))) :=
    let rec go (done : List (Nat × List (α × List (Nat × CExpr)))) : List (Nat × List (CExprTrie.Branch α)) → List (Nat × List (α × List (Nat × CExpr)))
        | [] => done
        | (link, br) :: rest =>
            let cand_here := CExprTrie.unify_reconstruct r (CExprTrie.unify_candidates ((link, br) :: rest) r link ce)
            match cand_here with
            | [] => go done rest
            | _ => go ((link, cand_here) :: done) rest
    go [] (List.reverse T)



#eval CExprTrie.unify_occurences (CExprTrie.ofList (· ≤ ·) test_list) (.app (.const `a []) (.lnode 1 (.ofBvar 42) .none)) (· ≤ ·)
#eval CExprTrie.unify_occurences (CExprTrie.ofList (· ≤ ·) test_list) (.app (.lnode 0 (.ofBvar 42) .none) (.const `d [])) (· ≤ ·)
#eval CExprTrie.unify_occurences (CExprTrie.ofList (· ≤ ·) test_list) (.app (.lnode 0 (.ofBvar 42) .none) (.lnode 1 (.ofBvar 42) .none)) (· ≤ ·)


import LeanGrow.F.Utils.ExprTrieRW.Query

open Lean

-- is CExprTrie.find_candidates? but we start at an offset
partial def CExprTrie.find_occurences_candidates [BEq α] (T : CExprTrie α) (ce : CExpr) (r : α → α → Prop) [DecidableRel r] (start : Nat) : List (List α) × List (Nat × CExpr × List α × List rwDirs) :=
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
            go (List.listConsIfNonempty nlb (rws_ind ++ done)) (rws ++ todos) more
        | .lnode l o t =>
            let lb := CExprTrie.getAtLink T link
            let rws := updateTodos (.lnode l o t) dirs [] lb
            let rws_ind := rws.map (fun x => x.2.2.1)
            let nlb := CExprTrie.getIndices_lNode l t lb
            go (List.listConsIfNonempty nlb (rws_ind ++ done)) (rws ++ todos) more
        | .gnode l o =>
            let lb := CExprTrie.getAtLink T link
            let rws := updateTodos (.gnode l o) dirs [] lb
            let rws_ind := rws.map (fun x => x.2.2.1)
            let nlb := CExprTrie.getIndices_gNode l lb
            go (List.listConsIfNonempty nlb (rws_ind ++ done)) (rws ++ todos) more
        | .bvar l =>
            let lb := CExprTrie.getAtLink T link
            let rws := updateTodos (.bvar l) dirs [] lb
            let rws_ind := rws.map (fun x => x.2.2.1)
            let nlb := CExprTrie.getIndices_Bvar l lb
            go (List.listConsIfNonempty nlb (rws_ind ++ done)) (rws ++ todos) more
        | .sort l =>
            let lb := CExprTrie.getAtLink T link
            let rws := updateTodos (.sort l) dirs [] lb
            let rws_ind := rws.map (fun x => x.2.2.1)
            let nlb := CExprTrie.getIndices_Sort l lb
            go (List.listConsIfNonempty nlb (rws_ind ++ done)) (rws ++ todos) more
        | .const l m =>
            let lb := CExprTrie.getAtLink T link
            let rws := updateTodos (.const l m) dirs [] lb
            let rws_ind := rws.map (fun x => x.2.2.1)
            let nlb := CExprTrie.getIndices_Const l lb
            go (List.listConsIfNonempty nlb (rws_ind ++ done)) (rws ++ todos) more
  go [] [] [(ce,start,[])]




def CExprTrie.find_occurences [BEq α] (T : CExprTrie α) (ce : CExpr) (r : α → α → Prop) [DecidableRel r] : List (Nat × List α × List (Nat × CExpr × List α × List rwDirs)) :=
    let rec go (done : List (Nat × List α × List (Nat × CExpr × List α × List rwDirs))) : List (Nat × List (CExprTrie.Branch α)) → List (Nat × List α × List (Nat × CExpr × List α × List rwDirs))
        | [] => done
        | (link, br) :: rest =>
            let (cand_here_std, cand_here_rw) := CExprTrie.find_occurences_candidates ((link, br) :: rest) ce r link
            let prune :=
                match cand_here_std with
                | [] => []
                | h :: t => t.foldl (fun x y => List.orderedIntersect r x y ) h
            let actual := (cand_here_rw.map (fun (n,e,ind, dir) => (n,e, List.orderedIntersect r prune ind, dir))).filter (fun x => !x.2.2.1.isEmpty)
            match prune with
            | [] => go done rest
            | _ => go ((link, prune, actual) :: done) rest
    go [] (List.reverse T)

-- #eval CExprTrie.find_occurences (CExprTrie.ofList (· ≤ ·) test_list) (.app (.const `a []) (.const `b [])) (· ≤ ·)

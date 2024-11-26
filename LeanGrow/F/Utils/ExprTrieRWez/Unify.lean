
import LeanGrow.F.Utils.ExprTrieRWez.Query

open Lean





-- TODO : make more efficient
partial def CExprTrie.buildAtLink [BEq α] [Repr α] (T : CExprTrie α) (link : Nat) (r : α → α → Prop) [DecidableRel r] : List (CExpr × List α) :=
  with_lTrace TraceFlags.off in
  let lb := CExprTrie.getAtLink T link
  let rec go : CExprTrie.Branch α → List (CExpr × List α)
    | .ofFailed => []
    | .ofApp lf la _ _ _ _ =>
          let fs := CExprTrie.buildAtLink T lf r
          let as := CExprTrie.buildAtLink T la r
          let res :=
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
          lTrace TraceFlags.zero & s!"Building apps:\n{repr res}\n\n" & res
    | .ofLam lf la _ _ _ _ =>
          let fs := CExprTrie.buildAtLink T lf r
          let as := CExprTrie.buildAtLink T la r
          let res :=
            (fs.foldl (fun x y =>
              (as.foldl (fun X Y =>
                let inter := List.orderedIntersect r y.2 Y.2
                match inter with
                | [] => X
                | _ => (.lam `dummy y.1 Y.1 .default, inter) :: X
                  -- wonder whether this can cause problems...
                  -- We should ignore name and Binderinfo everywhere too
                )
                []) :: x
              )
              []).join
          lTrace TraceFlags.zero & s!"Building lams:\n{repr res}\n\n" & res
    | .ofForall lf la _ _ _ _ =>
          let fs := CExprTrie.buildAtLink T lf r
          let as := CExprTrie.buildAtLink T la r
          let res :=
            (fs.foldl (fun x y =>
              (as.foldl (fun X Y =>
                let inter := List.orderedIntersect r y.2 Y.2
                match inter with
                | [] => X
                | _ => (.forallE `dummy y.1 Y.1 .default, inter) :: X
                )
                []) :: x
              )
              []).join
            lTrace TraceFlags.zero & s!"Building foalls:\n{repr res}\n\n" & res
    | .ofLet lf la lz _ _ _ _ _ =>
          let fs := CExprTrie.buildAtLink T lf r
          let as := CExprTrie.buildAtLink T la r
          let zs := CExprTrie.buildAtLink T lz r
          let res :=
            (fs.foldl (fun x y =>
              (as.foldl (fun X Y =>
                (zs.foldl (fun z Z =>
                  let interim := List.orderedIntersect r y.2 Y.2
                  let inter := List.orderedIntersect r Z.2 interim
                  match inter with
                  | [] => z
                  | _ => (.letE `dummy y.1 Y.1 Z.1 true, inter) :: z
                  )
                []) :: X
                )
                []).join :: x
              )
              []).join
          lTrace TraceFlags.zero & s!"Building lets:\n{repr res}\n\n" & res
    | .ofProj n i le _ _ _ =>
          let es := CExprTrie.buildAtLink T le r
          let res := es.map (fun (ce,inter) => (.proj n i ce,inter))
          lTrace TraceFlags.zero & s!"Building proj:\n{repr res}\n\n" & res
    |.ofLit l ind _ =>
          let res := [(.lit l, ind)]
          lTrace TraceFlags.zero & s!"Building lit:\n{repr res}\n\n" & res
    |.ofLNode l t ind _ =>
          let res := [(.lnode l (.ofBvar 42) t, ind)] --fix
          lTrace TraceFlags.zero & s!"Building lit:\n{repr res}\n\n" & res
    |.ofGNode l ind _ =>
          let res := [(.gnode l (.ofBvar 42), ind)] --fix
          lTrace TraceFlags.zero & s!"Building lit:\n{repr res}\n\n" & res
    |.ofBvar l ind _ =>
          let res := [(.bvar l , ind)]
          lTrace TraceFlags.zero & s!"Building lit:\n{repr res}\n\n" & res
    |.ofSort l ind _ =>
          let res := [(.sort l , ind)]
          lTrace TraceFlags.zero & s!"Building lit:\n{repr res}\n\n" & res
    |.ofConst n l ind _ =>
          let res := [(.const n l, ind)]
          lTrace TraceFlags.zero & s!"Building lit:\n{repr res}\n\n" & res
  (lb.foldl (fun x y => (go y) :: x) []).join



def done_prune [BEq α] [Repr α] (r : α → α → Prop) [DecidableRel r]
  (ind : List α) (done : List (Nat × List (CExpr × List α))) : List (Nat × List (CExpr × List α)) :=
  let rec process_inner (final : List (CExpr × List α)) : List (CExpr × List α) → List (CExpr × List α)
    | [] => final
    | (n,l) :: more =>
        match List.orderedIntersect r ind l with
        | [] => process_inner (final) more
        | I => process_inner ((n,I) :: final) more
  let rec process_outer (final : List (Nat × List (CExpr × List α))) : List (Nat × List (CExpr × List α)) → List (Nat × List (CExpr × List α))
    | [] => final
    | (n,l) :: more =>
        match process_inner [] l with
        | [] => process_outer final more
        | res => process_outer ((n,res) :: final) more
  process_outer [] done


-- #eval CExprTrie.buildAtLink (CExprTrie.ofList (· ≤ ·) test_list) 0 (· ≤ ·)

/-- Assumes `ce` is an expression from a thm, hence has only lnodes-/
partial def CExprTrie.unify_candidates [BEq α] [Repr α] (T : CExprTrie α) (r : α → α → Prop) [DecidableRel r] (start : Nat) (ce : CExpr) : List (Nat × List (CExpr × List α)) :=
  let rec go (done : List (Nat × List (CExpr × List α))) : List (CExpr × Nat) → List (Nat × List (CExpr × List α))
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
            match nlb with
            | [] => []
            | _ => go (done_prune r nlb done) more
        | .lnode l _ .none => -- tag .none means it does't originate from backward propagation
            let builds := CExprTrie.buildAtLink T link r
            go ((l, builds) :: done) more
        | .lnode l _ t =>
            let lb := CExprTrie.getAtLink T link
            let nlb := CExprTrie.getIndices_lNode l t lb
            match nlb with
            | [] => []
            | _ => go (done_prune r nlb done) more
        | .gnode l _ =>
            let lb := CExprTrie.getAtLink T link
            let nlb := CExprTrie.getIndices_gNode l lb
            match nlb with
            | [] => []
            | _ => go (done_prune r nlb done) more
        | .bvar l =>
            let lb := CExprTrie.getAtLink T link
            let nlb := CExprTrie.getIndices_Bvar l lb
            match nlb with
            | [] => []
            | _ => go (done_prune r nlb done) more
        | .sort l =>
            let lb := CExprTrie.getAtLink T link
            let nlb := CExprTrie.getIndices_Sort l lb
            match nlb with
            | [] => []
            | _ => go (done_prune r nlb done) more
        | .const n l =>
            let lb := CExprTrie.getAtLink T link
            let nlb := CExprTrie.getIndices_Const n l lb
            match nlb with
            | [] => []
            | _ => go (done_prune r nlb done) more
  go [] [(ce,start)]




-- #eval CExprTrie.unify_candidates (CExprTrie.ofList (· ≤ ·) test_list) (· ≤ ·) (.app (.node 0 (.ofBvar 42)) (.node 1 (.ofBvar 42)))

-- #eval CExprTrie.uniunify_candidatesfy (CExprTrie.ofList (· ≤ ·) test_list) (· ≤ ·) (.forallE `dummy (.node 0 (.ofBvar 42)) (.node 1 (.ofBvar 42)) .default)

-- #eval CExprTrie.unify_candidates (CExprTrie.ofList (· ≤ ·) test_list) (· ≤ ·) (.node 0 (.ofBvar 42))

-- #eval CExprTrie.unify_candidates (CExprTrie.ofList (· ≤ ·) test_list) (· ≤ ·) (.const `nope [])

/-
TODO:

To reconstruct unification candidates, proceed as follows:
go over list & over indices ; for each, index maintain an apriori embedding (ad new one when new index encountered) ;
that embedding will store assignements of node indices to CExpre (use arrays ??) ;

In the example of the first eval above, start by building an apriori unification with 4, where 1 would be `d`.
Then build two apriori unification with 1 and 42, where 1 would be `d`.
Then modify the a priori embeddings at 1 and 4 where we set 0 to `a b`.
And so one. If conflicts arise, give up on the embedding at the index entirely ...

-/

def CExprTrie.unify_reconstruct [BEq α] [Repr α] (r : α → α → Prop) [DecidableRel r] (candidates : List (Nat × List (CExpr × List α))) : List (α × List (Nat × CExpr)) :=
    let rec go (node_idx : Nat) (sofar : List (α × List (Nat × CExpr))) : List (CExpr × List α) → List (α × List (Nat × CExpr))
        | [] => sofar
        | (assign, ind) :: rest =>
                let step := ind.foldl (fun out i => List.findModifyAdd (fun x => x.1 == i) (fun (idx, matchInfo) => (idx, (node_idx,assign) :: matchInfo)) (i, [(node_idx,assign)]) out) sofar
                go node_idx step rest
    candidates.foldl (fun out (node_idx, assign_data) => go node_idx out assign_data) []


#eval CExprTrie.unify_reconstruct (· ≤ ·) (CExprTrie.unify_candidates (CExprTrie.ofList (· ≤ ·) test_list) (· ≤ ·) 0 (.app (.lnode 0 (.ofBvar 42) .none) (.lnode 1 (.ofBvar 42) .none)))
#eval CExprTrie.unify_reconstruct (· ≤ ·) (CExprTrie.unify_candidates (CExprTrie.ofList (· ≤ ·) test_list) (· ≤ ·) 0 (.app (.lnode 0 (.ofBvar 42) .none) (.const `d [])))
#eval (CExprTrie.unify_candidates (CExprTrie.ofList (· ≤ ·) test_list) (· ≤ ·) 0 (.app (.lnode 0 (.ofBvar 42) .none) (.const `d [])))

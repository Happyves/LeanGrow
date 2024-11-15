
import LeanGrow.F.Utils.ExprTrieRW.Query
import LeanGrow.F.Utils.ExprTrieRW.RWclasses

open Lean


/-

Should proceed as in `Query.lean`. The difference will be at untagged lnodes.
To build a try with RW branches, we should, when encountering an RW branch, build
the CExprTrie of the class (which may itself contain RW branches).
There may be exponential growths in the number of terms considered here, but it is a necessity.

We should add a format for construction. This isn't the RWblueprint, as we're not matching the
untaged lnode to an expression, but a build-blueprint. In the non-rw context, we ended up with
a list of pair of indices of terms of the trie, together with a list representing the correspondece
of the pos-index of the lnode and the cexpr we may replace it with in the context of unification.
Now instead of a cexpr to replace the lnode with, we should have a list of CExpr, together with
some format on how they were obtained from rewrites. This should also be recorded in the
embedding data, as we'll need it when assembling the terms (note that we should build only
in the end, once we know which rewrites were actually needed in the proof)
-/


-- TODO : make more efficient
partial def CExprTrie.buildAtLink [BEq α] [Repr α] (T : CExprTrie α) (link : Nat) (r : α → α → Prop) [DecidableRel r]
  (classes : List (Nat × RWClassData)) : List (CExpr × List α) :=
  with_lTrace TraceFlags.off in
  let lb := CExprTrie.getAtLink T link
  let rec go : CExprTrie.Branch α → List (CExpr × List α)
    | .ofFailed => []
    | .ofApp lf la =>
          let fs := CExprTrie.buildAtLink T lf r classes
          let as := CExprTrie.buildAtLink T la r classes
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
    | .ofLam n lf la i =>
          let fs := CExprTrie.buildAtLink T lf r classes
          let as := CExprTrie.buildAtLink T la r classes
          let res :=
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
          lTrace TraceFlags.zero & s!"Building lams:\n{repr res}\n\n" & res
    | .ofForall n lf la i =>
          let fs := CExprTrie.buildAtLink T lf r classes
          let as := CExprTrie.buildAtLink T la r classes
          let res :=
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
            lTrace TraceFlags.zero & s!"Building foalls:\n{repr res}\n\n" & res
    | .ofLet n lf la lz i =>
          let fs := CExprTrie.buildAtLink T lf r classes
          let as := CExprTrie.buildAtLink T la r classes
          let zs := CExprTrie.buildAtLink T lz r classes
          let res :=
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
          lTrace TraceFlags.zero & s!"Building lets:\n{repr res}\n\n" & res
    | .ofProj n i le =>
          let es := CExprTrie.buildAtLink T le r classes
          let res := es.map (fun (ce,inter) => (.proj n i ce,inter))
          lTrace TraceFlags.zero & s!"Building proj:\n{repr res}\n\n" & res
    |.ofLit l ind =>
          let res := [(.lit l, ind)]
          lTrace TraceFlags.zero & s!"Building lit:\n{repr res}\n\n" & res
    |.ofLNode l t ind =>
          let res := [(.lnode l (.ofBvar 42) t, ind)] --fix
          lTrace TraceFlags.zero & s!"Building lit:\n{repr res}\n\n" & res
    |.ofGNode l ind =>
          let res := [(.gnode l (.ofBvar 42), ind)] --fix
          lTrace TraceFlags.zero & s!"Building lit:\n{repr res}\n\n" & res
    |.ofBvar l ind =>
          let res := [(.bvar l , ind)]
          lTrace TraceFlags.zero & s!"Building lit:\n{repr res}\n\n" & res
    |.ofSort l ind =>
          let res := [(.sort l , ind)]
          lTrace TraceFlags.zero & s!"Building lit:\n{repr res}\n\n" & res
    |.ofConst l ind =>
          let res := [(.const l [], ind)]
          lTrace TraceFlags.zero & s!"Building lit:\n{repr res}\n\n" & res
    |.ofRW cI _ ind =>
          match classes.find? (fun x => x.1 == cI) with
          | .none => []
          | .some (_, cData) =>
              --cData.class_cexprs.map (fun (_,cex) => (cex, ind))
              -- except that rw classes may contain rw nodes in their trees ...
              let built := CExprTrie.buildAtLink cData.class_trie 0 (· ≤ ·) classes
              built.map (fun (cex, _) => (cex, ind))
  (lb.foldl (fun x y => (go y) :: x) []).join



#exit

-- #eval CExprTrie.buildAtLink (CExprTrie.ofList (· ≤ ·) test_list) 0 (· ≤ ·)

/-- Assumes `ce` is an expression from a thm, hence has only lnodes-/
partial def CExprTrie.unify_candidates [BEq α] [Repr α] (T : CExprTrie α) (r : α → α → Prop) [DecidableRel r] (ce : CExpr) : List (Nat × List (CExpr × List α)) :=
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
            | _ => go (done) more
        | .lnode l _ .none => -- tag .none means it does't originate from backward propagation
            let builds := CExprTrie.buildAtLink T link r
            go ((l, builds) :: done) more
        | .lnode l _ t =>
            let lb := CExprTrie.getAtLink T link
            let nlb := CExprTrie.getIndices_lNode l t lb
            match nlb with
            | [] => []
            | _ => go (done) more
        | .gnode l _ =>
            let lb := CExprTrie.getAtLink T link
            let nlb := CExprTrie.getIndices_gNode l lb
            match nlb with
            | [] => []
            | _ => go (done) more
        | .bvar l =>
            let lb := CExprTrie.getAtLink T link
            let nlb := CExprTrie.getIndices_Bvar l lb
            match nlb with
            | [] => []
            | _ => go (done) more
        | .sort l =>
            let lb := CExprTrie.getAtLink T link
            let nlb := CExprTrie.getIndices_Sort l lb
            match nlb with
            | [] => []
            | _ => go (done) more
        | .const l _ =>
            let lb := CExprTrie.getAtLink T link
            let nlb := CExprTrie.getIndices_Const l lb
            match nlb with
            | [] => []
            | _ => go (done) more
  go [] [(ce,0)]




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


-- #eval CExprTrie.unify_reconstruct (· ≤ ·) (CExprTrie.unify_candidates (CExprTrie.ofList (· ≤ ·) test_list) (· ≤ ·) (.app (.lnode 0 (.ofBvar 42) .none) (.lnode 1 (.ofBvar 42) .none)))

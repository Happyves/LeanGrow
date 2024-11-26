
import LeanGrow.F.Utils.ExprTrieRWez.Unify
import LeanGrow.F.Data.CExpr.API

#check 1


open Lean

partial def CExprTrie.buildAtLink_wTrarget [BEq α] [Repr α] (target : α) (T : CExprTrie α) (link : Nat) (r : α → α → Prop) [DecidableRel r] : CExpr :=
  with_lTrace TraceFlags.off in
  let lb := CExprTrie.getAtLink T link
  let rec go : CExprTrie.Branch α → CExpr
    | .ofFailed => .failed
    | .ofApp lf la ind _ _ _ =>
          if List.orderedContains r target ind
          then
            let fs := CExprTrie.buildAtLink_wTrarget target T lf r
            let as := CExprTrie.buildAtLink_wTrarget target T la r
            .app fs as
          else
            .failed
    | .ofLam lf la ind _ _ _ =>
          if List.orderedContains r target ind
          then
            let fs := CExprTrie.buildAtLink_wTrarget target T lf r
            let as := CExprTrie.buildAtLink_wTrarget target T la r
            .lam `dummy fs as .default
          else
            .failed
    | .ofForall lf la ind _ _ _ =>
          if List.orderedContains r target ind
          then
            let fs := CExprTrie.buildAtLink_wTrarget target T lf r
            let as := CExprTrie.buildAtLink_wTrarget target T la r
            .forallE `dummy fs as .default
          else
            .failed
    | .ofLet lf la lz ind _ _ _ _ =>
          if List.orderedContains r target ind
          then
            let fs := CExprTrie.buildAtLink_wTrarget target T lf r
            let as := CExprTrie.buildAtLink_wTrarget target T la r
            let zs := CExprTrie.buildAtLink_wTrarget target T lz r
            .letE `dummy fs as zs true
          else
            .failed
    | .ofProj n i le ind _ _ =>
          if List.orderedContains r target ind
          then
            let es := CExprTrie.buildAtLink_wTrarget target T le r
            .proj n i es
          else
            .failed
    |.ofLit l ind _ =>
          if List.orderedContains r target ind then (.lit l) else .failed
    |.ofLNode l t ind _ =>
          if List.orderedContains r target ind then (.lnode l (.ofBvar 42) t) else .failed
    |.ofGNode l ind _ =>
          if List.orderedContains r target ind then (.gnode l (.ofBvar 42)) else .failed
    |.ofBvar l ind _ =>
          if List.orderedContains r target ind then (.bvar l) else .failed
    |.ofSort l ind _ =>
          if List.orderedContains r target ind then (.sort l ) else .failed
    |.ofConst n l ind _ =>
          if List.orderedContains r target ind then (.const n l) else .failed
  ((lb.foldl (fun x y => (go y) :: x) []).filter (fun x => x != .failed)).headD .failed

#eval CExprTrie.buildAtLink_wTrarget 4 (CExprTrie.ofList (· ≤ ·) test_list) 1 (· ≤ ·)
#eval CExprTrie.buildAtLink_wTrarget 4 (CExprTrie.ofList (· ≤ ·) test_list) 0 (· ≤ ·)



-- def CExprTrie.Branch_getIndices [BEq α] (r : α → α → Prop) [DecidableRel r]
--   (lb : List (CExprTrie.Branch α)) : List α :=
--   let rec getem (done : List (List α)) : List (CExprTrie.Branch α) → List (List α)
--     | [] => done
--     | b :: more =>
--         match b with
--         | .ofApp _ _ ind _ _  => getem (ind :: done) more
--         | .ofProj _ _ _ ind _ => getem (ind :: done) more
--         | .ofLam _ _ ind _ _ => getem (ind :: done) more
--         | .ofForall _ _ ind _ _ => getem (ind :: done) more
--         | .ofLet _ _ _ ind _ _ _ => getem (ind :: done) more
--         | .ofLit _ ind => getem (ind :: done) more
--         | .ofLNode _ _ ind => getem (ind :: done) more
--         | .ofGNode _ ind => getem (ind :: done) more
--         | .ofBvar _ ind => getem (ind :: done) more
--         | .ofSort _ ind => getem (ind :: done) more
--         | .ofConst _ _ ind => getem (ind :: done) more
--         | .ofFailed => getem (done) more
--   List.orderedJoin r [] (getem [] lb)


def CExprTrie.Branch_findTarget [BEq α] (target : α) (r : α → α → Prop) [DecidableRel r]
  (lb : List (CExprTrie.Branch α)) : CExprTrie.Branch α :=
  let rec getem : List (CExprTrie.Branch α) → CExprTrie.Branch α
    | [] => .ofFailed
    | b :: more =>
        match b with
        | .ofApp _ _ ind _ _ _ => if List.orderedContains r target ind then b else getem more
        | .ofProj _ _ _ ind _ _ => if List.orderedContains r target ind then b else getem more
        | .ofLam _ _ ind _ _ _=> if List.orderedContains r target ind then b else getem more
        | .ofForall _ _ ind _ _ _ => if List.orderedContains r target ind then b else getem more
        | .ofLet _ _ _ ind _ _ _ _ => if List.orderedContains r target ind then b else getem more
        | .ofLit _ ind _ => if List.orderedContains r target ind then b else getem more
        | .ofLNode _ _ ind _ => if List.orderedContains r target ind then b else getem more
        | .ofGNode _ ind _ => if List.orderedContains r target ind then b else getem more
        | .ofBvar _ ind _ => if List.orderedContains r target ind then b else getem more
        | .ofSort _ ind _ => if List.orderedContains r target ind then b else getem more
        | .ofConst _ _ ind _ => if List.orderedContains r target ind then b else getem more
        | .ofFailed => getem more
  getem lb


partial def CExprTrie.factor_with [BEq α] (T : CExprTrie α) (tidx : Nat) (cidx : α)
  (r : α → α → Prop) [DecidableRel r] (insert : Nat → CExpr) : CExpr :=
    let rec go (depth : Nat) (link : Nat) : CExpr :=
      if link == tidx
      then
        insert depth
      else
        let lb := CExprTrie.getAtLink T link
        match CExprTrie.Branch_findTarget cidx r lb with
        | .ofApp  lf la _ _ _ _ =>
            let f := go depth lf
            let a := go depth la
            .app f a
        | .ofProj n i le _ _ _ =>
            let e := go depth le
            .proj n i e
        | .ofLam lf la _ _ _ _ =>
            let f := go depth lf
            let a := go (depth+1) la
            .lam `dummy f a .default
        | .ofForall lf la _ _ _ _ =>
            let f := go depth lf
            let a := go (depth+1) la
            .forallE `dummy f a .default
        | .ofLet lf la lz _ _ _ _ _ =>
            let f := go depth lf
            let a := go depth la
            let z := go (depth+1) lz
            .letE `dummy f a z true
        | .ofLit l _ _ => .lit l
        | .ofLNode x y _ _ => .lnode x (.ofBvar 42) y
        | .ofGNode x _ _ => .gnode x (.ofBvar 42)
        | .ofBvar x _ _ => .bvar x
        | .ofSort x _ _ => .sort x
        | .ofConst n l _ _ => .const n l
        | .ofFailed => .failed
    go 0 0

-- so tree index indices were useless, but α-index directions are usefull

def CExprTrie.factor [BEq α] (T : CExprTrie α) (tidx : Nat) (cidx : α)
  (r : α → α → Prop) [DecidableRel r] : CExpr :=
  (CExprTrie.factor_with T tidx cidx r (fun d => .bvar d))

def CExprTrie.buildRWtype [BEq α] (T : CExprTrie α) (tidx : Nat) (cidx : α)
  (r : α → α → Prop) [DecidableRel r] (replacement : CExpr) : CExpr :=
  CExprTrie.factor_with T tidx cidx r (fun _ => replacement)



#eval CExprTrie.factor (CExprTrie.ofList (· ≤ ·) test_list) 4 4 (· ≤ ·)
#eval CExprTrie.factor (CExprTrie.ofList (· ≤ ·) test_list) 3 4 (· ≤ ·)
#eval CExprTrie.factor (CExprTrie.ofList (· ≤ ·) test_list) 2 4 (· ≤ ·)
#eval CExprTrie.factor (CExprTrie.ofList (· ≤ ·) test_list) 1 4 (· ≤ ·)
#eval CExprTrie.factor (CExprTrie.ofList (· ≤ ·) test_list) 0 4 (· ≤ ·)

-- increadibly slow though ...

set_option pp.all true in
#check Eq.ndrec

/-

As of now, an index should refer to 3 things:

- the term : initially, the index points to the gnode of that index originating from the query;
  in forward steps, the index will point to a thm application ; in rewrite steps, it will point
  to the rewrite term. Note that we don't have to build terms until the very end, when a proof
  was found, so we should do this for better perfromance. We do however have to keep track on how
  to assemble terms once we're done.

- the type : will be, for thm-applications, the result/head with embedded lnodes replaced by gnodes
  or constants or expressions with both, and for rewrites simply the expression with the rewritten
  subexpression (ie. use `CExprTrie.insert_at` in the tree, and build teh expression with `CExprTrie.buildRWtype`,
  actually, megre these to one function, so as to avoiding traversing twice ??!! ; or don't since we planned
  on building terms after proof-search was done ?)

- the type's type and universe level : necessary for rewriting ; when adding an index via rewrites,
  we use those from the original expression, as equality requires them to be the same ; for thm-applicaitons
  we must make a call to inferType, however.

Also, when we process eq-thms, we should gather the type of the equality ; this can be a constant, or a
variable (that will become an lnode) ; in the first case, we can also infer its type to get the universe level,
and in the second the level will be an lnode too, or a constant...

-/


partial def CExprTrie.buildRWterm [BEq α] (T : CExprTrie α) (tidx : Nat) (cidx : α) (r : α → α → Prop) [DecidableRel r]
  (eq_type : CExpr) -- from thm-preprocessed-or-embedding-data
  (eq_uni top_uni : Level) (init_top init new : CExpr) --refer to, wrt. `Eq.ndrec`, `m` `a` `b` respectively
  (eq_thm : CExpr) : CExpr :=
  let motive : CExpr := .lam `dummy eq_type (CExprTrie.factor T tidx cidx r) .default
  CExpr.mkApp (.const `Eq.ndrec [top_uni,eq_uni]) [eq_type,init,motive,init_top,new,eq_thm]

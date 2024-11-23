
import LeanGrow.F.Utils.ExprTrieRWez.Unify


#check 1


partial def CExprTrie.buildAtLink_wTrarget [BEq α] [Repr α] (target : α) (T : CExprTrie α) (link : Nat) (r : α → α → Prop) [DecidableRel r] : CExpr :=
  with_lTrace TraceFlags.off in
  let lb := CExprTrie.getAtLink T link
  let rec go : CExprTrie.Branch α → CExpr
    | .ofFailed => .failed
    | .ofApp lf la ind _ _ =>
          if List.orderedContains r target ind
          then
            let fs := CExprTrie.buildAtLink_wTrarget target T lf r
            let as := CExprTrie.buildAtLink_wTrarget target T la r
            .app fs as
          else
            .failed
    | .ofLam lf la ind _ _ =>
          if List.orderedContains r target ind
          then
            let fs := CExprTrie.buildAtLink_wTrarget target T lf r
            let as := CExprTrie.buildAtLink_wTrarget target T la r
            .lam `dummy fs as .default
          else
            .failed
    | .ofForall lf la ind _ _ =>
          if List.orderedContains r target ind
          then
            let fs := CExprTrie.buildAtLink_wTrarget target T lf r
            let as := CExprTrie.buildAtLink_wTrarget target T la r
            .forallE `dummy fs as .default
          else
            .failed
    | .ofLet lf la lz ind _ _ _ =>
          if List.orderedContains r target ind
          then
            let fs := CExprTrie.buildAtLink_wTrarget target T lf r
            let as := CExprTrie.buildAtLink_wTrarget target T la r
            let zs := CExprTrie.buildAtLink_wTrarget target T lz r
            .letE `dummy fs as zs true
          else
            .failed
    | .ofProj n i le ind _ =>
          if List.orderedContains r target ind
          then
            let es := CExprTrie.buildAtLink_wTrarget target T le r
            .proj n i es
          else
            .failed
    |.ofLit l ind =>
          if List.orderedContains r target ind then (.lit l) else .failed
    |.ofLNode l t ind =>
          if List.orderedContains r target ind then (.lnode l (.ofBvar 42) t) else .failed
    |.ofGNode l ind =>
          if List.orderedContains r target ind then (.gnode l (.ofBvar 42)) else .failed
    |.ofBvar l ind =>
          if List.orderedContains r target ind then (.bvar l) else .failed
    |.ofSort l ind =>
          if List.orderedContains r target ind then (.sort l ) else .failed
    |.ofConst n l ind =>
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
        | .ofApp _ _ ind _ _  => if List.orderedContains r target ind then b else getem more
        | .ofProj _ _ _ ind _ => if List.orderedContains r target ind then b else getem more
        | .ofLam _ _ ind _ _ => if List.orderedContains r target ind then b else getem more
        | .ofForall _ _ ind _ _ => if List.orderedContains r target ind then b else getem more
        | .ofLet _ _ _ ind _ _ _ => if List.orderedContains r target ind then b else getem more
        | .ofLit _ ind => if List.orderedContains r target ind then b else getem more
        | .ofLNode _ _ ind => if List.orderedContains r target ind then b else getem more
        | .ofGNode _ ind => if List.orderedContains r target ind then b else getem more
        | .ofBvar _ ind => if List.orderedContains r target ind then b else getem more
        | .ofSort _ ind => if List.orderedContains r target ind then b else getem more
        | .ofConst _ _ ind => if List.orderedContains r target ind then b else getem more
        | .ofFailed => getem more
  getem lb


partial def CExprTrie.factor [BEq α] (T : CExprTrie α) (tidx : Nat) (cidx : α)
  (r : α → α → Prop) [DecidableRel r] : CExpr :=
    let rec go (depth : Nat) (link : Nat) : CExpr :=
      if link == tidx
      then
        .bvar depth
      else
        let lb := CExprTrie.getAtLink T link
        match CExprTrie.Branch_findTarget cidx r lb with
        | .ofApp  lf la _ _ _  =>
            let f := go depth lf
            let a := go depth la
            .app f a
        | .ofProj n i le _ _ =>
            let e := go depth le
            .proj n i e
        | .ofLam lf la _ _ _ =>
            let f := go depth lf
            let a := go (depth+1) la
            .lam `dummy f a .default
        | .ofForall lf la _ _ _ =>
            let f := go depth lf
            let a := go (depth+1) la
            .forallE `dummy f a .default
        | .ofLet lf la lz _ _ _ _ =>
            let f := go depth lf
            let a := go depth la
            let z := go (depth+1) lz
            .letE `dummy f a z true
        | .ofLit l _ => .lit l
        | .ofLNode x y _ => .lnode x (.ofBvar 42) y
        | .ofGNode x _ => .gnode x (.ofBvar 42)
        | .ofBvar x _ => .bvar x
        | .ofSort x _ => .sort x
        | .ofConst n l _ => .const n l
        | .ofFailed => .failed
    go 0 0

-- so tree index indices were useless, but α-index directions are usefull


#eval CExprTrie.factor (CExprTrie.ofList (· ≤ ·) test_list) 4 4 (· ≤ ·)
#eval CExprTrie.factor (CExprTrie.ofList (· ≤ ·) test_list) 3 4 (· ≤ ·)
#eval CExprTrie.factor (CExprTrie.ofList (· ≤ ·) test_list) 2 4 (· ≤ ·)
#eval CExprTrie.factor (CExprTrie.ofList (· ≤ ·) test_list) 1 4 (· ≤ ·)
#eval CExprTrie.factor (CExprTrie.ofList (· ≤ ·) test_list) 0 4 (· ≤ ·)

-- increadibly slow though ...

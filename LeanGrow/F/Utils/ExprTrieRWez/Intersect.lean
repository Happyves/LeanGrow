

import LeanGrow.F.Utils.ExprTrieRWez.Query


open Lean

-- Could be used to check if any forward-types match backward-goal-types,
-- if the latter are stored in a trie. This should be even more efficient
-- if we impose an order on branches.


private def merge (L R : List (List Nat × List Nat)) : List (List Nat × List Nat) :=
  let rec comp (done : List (List Nat × List Nat)) (l r : List Nat) : List (List Nat × List Nat) → List (List Nat × List Nat)
    | [] => done
    | nx :: more =>
        match List.orderedIntersect (· ≤ ·) nx.1 l, List.orderedIntersect (· ≤ ·) nx.2 r with
        | [], _ => comp done l r more
        | _, [] => comp done l r more
        | x, y =>  comp ((x,y) :: done) l r more
  let rec go (done : List (List Nat × List Nat)) : List (List Nat × List Nat) → List (List Nat × List Nat)
    | [] => done
    | nx :: more => go ((comp [] nx.1 nx.2 R) ++ done) more
  go [] L




private inductive callType where
| one (l L : Nat)
| two (l r L R: Nat)
| three (a b c A B C: Nat)
deriving Inhabited, Repr, BEq


partial def CExprTrie.intersect (L R : CExprTrie Nat) : List (List Nat × List Nat) :=
  let rec candidates (br : List (CExprTrie.Branch Nat)) (done_ind : List (List Nat × List Nat)) (done_call : List callType) : List (CExprTrie.Branch Nat) → (List (List Nat × List Nat) × List callType)
    | [] => (done_ind, done_call)
    | nx :: more =>
        match nx with
        | .ofApp l r _ _ _ _ =>
            let links? := CExprTrie.Branch_getAppLinks? br
            match links? with
            | .some (lf,la) => candidates br done_ind ((.two l r lf la) :: done_call) more
            | _ => candidates br done_ind (done_call) more
        | .ofLam l r _ _ _ _ =>
            let links? := CExprTrie.Branch_getLamLinks? br
            match links? with
            | .some (lf,la) => candidates br done_ind ((.two l r lf la) :: done_call) more
            | _ => candidates br done_ind (done_call) more
        | .ofForall l r _ _ _ _ =>
            let links? := CExprTrie.Branch_getForallLinks? br
            match links? with
            | .some (lf,la) => candidates br done_ind ((.two l r lf la) :: done_call) more
            | _ => candidates br done_ind (done_call) more
        | .ofLet l r z _ _ _ _ _ =>
            let links? := CExprTrie.Branch_getLetLinks? br
            match links? with
            | .some (lf,la, lz) => candidates br done_ind ((.three l r z lf la lz) :: done_call) more
            | _ => candidates br done_ind (done_call) more
        | .ofProj n i l _ _ _ =>
            let links? := CExprTrie.Branch_getProjLinks? n i br
            match links? with
            | .some (lf) => candidates br done_ind ((.one l lf) :: done_call) more
            | _ => candidates br done_ind (done_call) more
        | .ofLit l ind _ =>
            let nlb := CExprTrie.getIndices_Lit l br
            match nlb with
            | [] => candidates br done_ind (done_call) more
            | _ => candidates br ((ind, nlb) :: done_ind) (done_call) more
        | .ofLNode i t ind _ =>
            let nlb := CExprTrie.getIndices_lNode i t br
            match nlb with
            | [] => candidates br done_ind (done_call) more
            | _ => candidates br ((ind, nlb) :: done_ind) (done_call) more
        | .ofGNode l ind _ =>
            let nlb := CExprTrie.getIndices_gNode l br
            match nlb with
            | [] => candidates br done_ind (done_call) more
            | _ => candidates br ((ind, nlb) :: done_ind) (done_call) more
        | .ofBvar l ind _ =>
            let nlb := CExprTrie.getIndices_Bvar l br
            match nlb with
            | [] => candidates br done_ind (done_call) more
            | _ => candidates br ((ind, nlb) :: done_ind) (done_call) more
        | .ofSort l ind _ =>
            let nlb := CExprTrie.getIndices_Sort l br
            match nlb with
            | [] => candidates br done_ind (done_call) more
            | _ => candidates br ((ind, nlb) :: done_ind) (done_call) more
        | .ofConst n l ind _ =>
            let nlb := CExprTrie.getIndices_Const n l br
            match nlb with
            | [] => candidates br done_ind (done_call) more
            | _ => candidates br ((ind, nlb) :: done_ind) (done_call) more
        | .ofFailed  => candidates br done_ind (done_call) more
  let rec go (ll lr : Nat) : List (List Nat × List Nat) :=
    let bl := CExprTrie.getAtLink L ll
    let br := CExprTrie.getAtLink R lr
    let (done_ind, done_call) := candidates br [] [] bl
    let more := done_call.map (fun x =>
      match x with
      | .one l L => go l L
      | .two l r L R =>
          let el := go l L
          let er := go r R
          merge el er
      | .three l r z L R Z =>
          let el := go l L
          let er := go r R
          let ez := go z Z
          merge (merge el er) ez
    )
    (done_ind :: more).join
  go 0 0


#eval (CExprTrie.ofList (· ≤ ·) test_list)

#eval test_list

def test_list_2 : List (Nat × CExpr) :=
  [(6, CExpr.app (CExpr.app (CExpr.const `a []) (CExpr.const `b [])) (CExpr.const `c [])),
   (66, CExpr.app (CExpr.app (CExpr.const `w []) (CExpr.const `b [])) (CExpr.const `d [])),
   (666, CExpr.app (CExpr.app (CExpr.const `a []) (CExpr.const `e [])) (CExpr.const `w [])),
   (42, CExpr.forallE `dummy (CExpr.const `x []) (CExpr.const `y []) (Lean.BinderInfo.default))
   ]

#eval CExprTrie.intersect (CExprTrie.ofList (· ≤ ·) test_list) (CExprTrie.ofList (· ≤ ·) test_list_2)

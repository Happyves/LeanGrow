
import LeanGrow.F.Utils.Trie.CTrie

def match_nontrivial [BEq α] (l r : Option α) : Bool :=
  match l with
  | .none => false
  | .some vl =>
      match r with
      | .none => false
      | .some vr => vl == vr

partial def CTrie.intersect [BEq α] (l r : CTrie α) : CTrie α :=
  let rec go (lpre rpre : Option ByteArray) (lo ro : Nat) : CTrie α → CTrie α → CTrie α
    | .leaf x, .leaf y => if match_nontrivial x y then .leaf y  else .leaf (.none)
    | .leaf x, .node1 y _ _ => if match_nontrivial x y then .leaf y  else .leaf (.none)
    | .leaf x, .node y _ _ => if match_nontrivial x y then .leaf y  else .leaf (.none)
    | .node1 x ax cx, .leaf y => if match_nontrivial x y then .leaf y  else .leaf (.none)
    | .node1 x ax cx, .node1 y ay cy =>
        match lpre, rpre with
        | .none, .none =>
            match ByteArray.lex_compare ax ay with
            | .eqB => if match_nontrivial x y then .leaf y  else .leaf (.none)
            | .eqL off =>
                if match_nontrivial x y
                then .node1 y ay (go (.some ax) .none off 0 cx cy)
                else .node1 .none ay (go (.some ax) .none off 0 cx cy)
            | .eqR off =>
                if match_nontrivial x y
                then .node1 x ax (go .none (.some ay) 0 off cx cy)
                else .node1 .none ax (go .none (.some ay) 0 off cx cy)
            | _ => .leaf (.none)

    | .node1 x ax cx =>

  go .none .none 0 0 l r

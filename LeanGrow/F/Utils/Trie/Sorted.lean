
import LeanGrow.F.Utils.Trie.CTrie

#check 1

namespace CTrie

private inductive upsert_help_type where
  | hit (pos : Nat) (len : Nat)
  | ins (pos : Nat)
  deriving Inhabited, BEq, Repr


private def sorted_upsert_help (cs : Array ByteArray) (i : Nat) (s : ByteArray) (si : UInt8) : upsert_help_type :=
  let rec go : Nat → upsert_help_type
    | 0 => .ins 0
    | n+1 =>
        let c := (cs.get! n)
        let j := ByteArray.getLongestMatch_wOffset i s c
        if j == 0
        then
          if si < c.get! 0
          then go n
          else .ins (n+1)
        else .hit n j
  go cs.size

partial def sorted_upsert (t : CTrie α) (s : ByteArray) (f : Option α → α) : CTrie α :=
  let rec go (i : Nat) : CTrie α → CTrie α
    | .leaf v =>
          if i < s.size
          then
            .node1 v (s.drop i) (.leaf (f .none))
          else
            .leaf (f v)
    | .node1 v c t =>
          if i < s.size
          then
            let j := ByteArray.getLongestMatch_wOffset i s c
            let sum := (i+j)
            if j == c.size
            then
              .node1 v c (go sum t)
            else
              let nc := c.drop j
              let add := s.drop sum
              let join := c.take j
              if c.get! j < s.get! sum
              then .node1 v join (.node .none #[nc,add] #[t,(.leaf (f .none))])
              else .node1 v join (.node .none #[add,nc] #[(.leaf (f .none)),t])
          else
            .node1 (f v) c t
    | .node v cs ts =>
          if i < s.size
          then
            match CTrie.sorted_upsert_help cs i s (s.get! i) with
            | .ins pos =>
                .node v (cs.insertAt! pos (s.drop i)) (ts.insertAt! pos (.leaf (f .none)))
            | .hit idx len =>
                let c := (cs.get! idx)
                let sum := (i+len)
                if len == c.size
                then
                  .node v cs (ts.modify idx ((go (i+len))))
                else
                  let nc := c.drop len
                  let add := s.drop sum
                  let join := c.take len
                  if c.get! len < s.get! sum
                  then .node v ((cs.modify idx (fun _ => join))) (ts.modify idx (fun t => .node .none #[nc,add] #[t,(.leaf (f .none))]))
                  else .node v ((cs.modify idx (fun _ => join))) (ts.modify idx (fun t => .node .none #[add,nc] #[(.leaf (f .none)),t]))
          else
            .node (f v) cs ts
  go 0 t



partial def sorted_insert (t : CTrie α) (s : String) (val : α) : CTrie α :=
  CTrie.sorted_upsert t (s.toUTF8) (fun _ => val)



def ofList_sorted : List (String × α) → CTrie α
  | [] => CTrie.empty
  | (s,v) :: more => CTrie.sorted_insert (CTrie.ofList_sorted more) s v


partial def sorted_find? (t : CTrie α) (s : String) : Option α :=
  let toB := s.toUTF8
  let rec go (i : Nat) : CTrie α → Option α
    | .leaf v => v
    | .node1 v c t =>
          if i = toB.size
          then v
          else
            let j := ByteArray.getLongestMatch_wOffset i toB c
            if j == c.size
            then go (i+j) t
            else .none
    | .node v cs ts =>
          if i = toB.size
          then v
          else
            match CTrie.sorted_upsert_help cs i toB (toB.get! i) with
            | .ins _ => .none
            | .hit idx len =>
                  if len == (cs.get! idx).size
                  then go (i+len) (ts.get! idx)
                  else .none
  go 0 t



end CTrie

#exit

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


import LeanGrow.F.Utils.Trie.ByteArray


inductive CTrie (α : Type) where
  | leaf : Option α → CTrie α
  | node1 : Option α → ByteArray → CTrie α → CTrie α
  | node : Option α → Array ByteArray → Array (CTrie α) → CTrie α
deriving Repr


namespace CTrie
variable {α : Type}

def empty : CTrie α := leaf none

instance : EmptyCollection (CTrie α) :=
  ⟨empty⟩

instance : Inhabited (CTrie α) where
  default := empty


private def upsert_help (cs : Array ByteArray) (i : Nat) (s : ByteArray) : Option (Nat × Nat) :=
  let rec go : Nat → Option (Nat × Nat)
    | 0 => .none
    | n+1 =>
        let j := ByteArray.getLongestMatch_wOffset i s (cs.get! n)
        if j == 0 then go n else .some (n,j)
  go cs.size

partial def upsert (t : CTrie α) (s : ByteArray) (f : Option α → α) : CTrie α :=
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
            if j == c.size
            then
              .node1 v c (go (i+j) t)
            else
              let nc := c.drop j
              let add := s.drop (i+j)
              let join := c.take j
              .node1 v join (.node .none #[nc,add] #[t,(.leaf (f .none))])
          else
            .node1 (f v) c t
    | .node v cs ts =>
          if i < s.size
          then
            match CTrie.upsert_help cs i s with
            | .none =>
                .node v (cs.push (s.drop i)) (ts.push (.leaf (f .none)))
            | .some (idx,len) =>
                if len == (cs.get! idx).size
                then
                  .node v cs (ts.modify idx ((go (i+len))))
                else
                  let nc := (cs.get! idx).drop len
                  let add := s.drop (i+len)
                  let join := (cs.get! idx).take len
                  .node v ((cs.modify idx (fun _ => join))) (ts.modify idx (fun t => .node .none #[nc,add] #[t,(.leaf (f .none))]))
          else
            .node (f v) cs ts
  go 0 t



partial def insert (t : CTrie α) (s : String) (val : α) : CTrie α :=
  CTrie.upsert t (s.toUTF8) (fun _ => val)



def ofList : List (String × α) → CTrie α
  | [] => CTrie.empty
  | (s,v) :: more => CTrie.insert (CTrie.ofList more) s v



partial def find? (t : CTrie α) (s : String) : Option α :=
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
            match CTrie.upsert_help cs i toB with
            | .none => .none
            | .some (idx,len) =>
                  if len == (cs.get! idx).size
                  then go (i+len) (ts.get! idx)
                  else .none
  go 0 t


partial def toList (t : CTrie α) : List (String × α) :=

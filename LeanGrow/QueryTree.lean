
import LeanGrow.NameListCompare

open Lean Data


inductive QueryTree  where
| root (c : List (QueryTree))
| node (q : Trie Unit) (c : List (QueryTree))
| leaf
deriving Inhabited

def QueryTree.init (l : List (Trie Unit)) : QueryTree := .root (l.map (fun x => .node x [.leaf]))

def QueryTree.find_keys (c : List (QueryTree)) : Trie Nat :=
  match c with
  | [] => Trie.empty
  | .root _ :: _ => Trie.empty -- ill formed tree, root shouldn't appear as child
  | .node t _ :: rest =>
        let sofar := QueryTree.find_keys rest
        let T := Trie.merge_count_initialise t
        Trie.merge_count T sofar
  | .leaf :: rest => QueryTree.find_keys rest

def QueryTree.split_on_split (k : String) (c : List (QueryTree)) : List (QueryTree) × List (QueryTree) :=
  match c with
  | [] => ([],[])
  | .root _ :: _ => ([],[]) -- ill formed tree, root shouldn't appear as child
  | .node t chi :: rest =>
        let (sofar_pos, sofar_neg) := QueryTree.split_on_split k rest
        let T := t.find? k
        match T with
        | .some _ => (.node t chi :: sofar_pos, sofar_neg)
        | .none => (sofar_pos, .node t chi :: sofar_neg)
  | .leaf :: rest =>
        let (sofar_pos, sofar_neg) := QueryTree.split_on_split k rest
        (sofar_pos, .leaf :: sofar_neg)


def QueryTree.split_on (k : String) (c : List (QueryTree)) : List (QueryTree) :=
  let (pos, neg) := QueryTree.split_on_split k c
  (.node (SortedTrieFormList' [k]) pos) :: neg


-- to NameListCompare
partial def Trie.clean : Trie α → Trie α
| .leaf x => .leaf x
| .node1 x a t =>
      match t , x with
      | .leaf .none, .some _ => .leaf x
      | .leaf .none, .none => .leaf .none
      | _ , _ => .node1 x a t
| .node x as ts => -- **TODO** we can do better by deleting all entries that lead to .leaf .none
  let cts := ts.map Trie.clean
  let prune? := Id.run do
    let mut b := true
    for t in cts do
      match t with
      | .leaf .none => b := false
      | _ => pure ()
    return b
  if prune?
  then .leaf .none
  else .node x as ts

-- to NameListCompare
partial def Trie.delete (k : List Char) : Trie α → Trie α
| .leaf _ => .leaf .none
| .node1 x a t =>
      match k with
      | [] => .node1 .none a t
      | c :: rest => if c.toUInt8 == a then Trie.delete rest t else .node1 x a t
| .node x as ts =>
      match k with
      | [] => .node .none as ts
      | c :: rest =>
          let idiomatic := c.toUInt8
          let idx? := as.findIdx? (· == idiomatic)
          match idx? with
          | .some idx => .node x as (ts.modify idx (fun t => Trie.delete rest t))
          | .none => .node x as ts

def QueryTree.map_on_children (f : QueryTree → QueryTree) : QueryTree → QueryTree
| .root (c : List (QueryTree)) => .root (c.map f)
| .node (q : Trie Unit) (c : List (QueryTree)) => .node q (c.map f)
| .leaf => .leaf

def QueryTree.delete_key_or_leave (k : String) : QueryTree → QueryTree :=
  let kd := k.data
  fun t =>  match t with
            | .node T r => .node (Trie.delete kd T) r
            | x => x


def QueryTree.lift_topmost_on (k : String) : QueryTree → QueryTree
| .root (c : List (QueryTree)) => .root [.node (SortedTrieFormList' [k]) (c.map (QueryTree.delete_key_or_leave  k))]
| .node (q : Trie Unit) (c : List (QueryTree)) => .node (sorted_insert q k ()) (c.map (QueryTree.delete_key_or_leave k))
| .leaf => .leaf


-- to NameListCompare
partial def Trie.find_max (cache : ByteArray) : Trie Nat → Option (String × Nat)
| .leaf x =>
      match x with
      | .some v => .some (String.fromUTF8 cache (by sorry), v)
      | .none => .none
| .node1 x a t =>
      match Trie.find_max (cache.push a) t with
      | .some (s,v) =>
          match x with
          | .some w => if w > v then .some (String.fromUTF8 cache (by sorry), w) else .some (s,v)
          | .none => .some (s,v)
      | .none =>
          match x with
          | .some w => .some (String.fromUTF8 cache (by sorry), w)
          | .none => .none
| .node x as ts => Id.run do
      let mut M := 0
      let mut idx := Option.none
      for i in Array.range as.size do
        let a := as.get! i
        let t := ts.get! i
        match Trie.find_max (cache.push a) t with
        | .some (s,v) =>
            if v > M
            then
              M := v
              idx := .some s
        | .none => pure ()
      match idx with
      | .some s =>
            match x with
            | .some w => if w > M then .some (String.fromUTF8 cache (by sorry), w) else .some (s,M)
            | .none => .some (s,M)
      | .none =>
            match x with
            | .some w => .some (String.fromUTF8 cache (by sorry), w)
            | .none => .none


#eval Trie.find_max ⟨#[]⟩ (.node .none ⟨#[(62 : UInt8),72]⟩ #[(.node (.some 3) ⟨#[(63 : UInt8),64]⟩ #[(.leaf (.some 2)), (.leaf (.some 2))]), (.node1 .none 73 (.leaf (.some 1)))])
#eval Trie.find_max ⟨#[]⟩ (.node .none ⟨#[(62 : UInt8),72]⟩ #[(.node (.some 3) ⟨#[(63 : UInt8),64]⟩ #[(.leaf (.some 4)), (.leaf (.some 2))]), (.node1 .none 73 (.leaf (.some 1)))])
#eval Trie.find_max ⟨#[]⟩ (.node .none ⟨#[(62 : UInt8),72]⟩ #[(.node (.some 3) ⟨#[(63 : UInt8),64]⟩ #[(.leaf (.some 2)), (.leaf (.some 4))]), (.node1 .none 73 (.leaf (.some 1)))])
#eval Trie.find_max ⟨#[]⟩ (.node .none ⟨#[(62 : UInt8),72]⟩ #[(.node (.some 3) ⟨#[(63 : UInt8),64]⟩ #[(.leaf (.some 2)), (.leaf (.some 2))]), (.node1 .none 73 (.leaf (.some 4)))])
#eval Trie.find_max ⟨#[]⟩ (.node .none ⟨#[(62 : UInt8),72]⟩ #[(.node (.some 4) ⟨#[(63 : UInt8),64]⟩ #[(.leaf (.some 2)), (.leaf (.some 2))]), (.node1 .none 73 (.leaf (.some 4)))])

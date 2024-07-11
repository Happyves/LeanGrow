

import Lean.Data
import Mathlib.Data.List.Sort

open Lean Data

#check Trie

#check ByteArray



-- assumes byte array is sorted
def ByteArray.has? (A : ByteArray) (b : UInt8) : Option Nat :=
  Id.run do
    let mut v := .none
    let mut c := 0
    for x in A do
      match Ord.compare x b with
      | .lt => c := c+1
      | .eq => v := .some c ; break
      | .gt => break
    return v

#eval ByteArray.has? ⟨#[(UInt8.ofNatCore 1 (by decide)),(UInt8.ofNatCore 2 (by decide)),(UInt8.ofNatCore 5 (by decide))]⟩ (UInt8.ofNatCore 1 (by decide))
#eval ByteArray.has? ⟨#[(UInt8.ofNatCore 1 (by decide)),(UInt8.ofNatCore 2 (by decide)),(UInt8.ofNatCore 5 (by decide))]⟩ (UInt8.ofNatCore 2 (by decide))
#eval ByteArray.has? ⟨#[(UInt8.ofNatCore 1 (by decide)),(UInt8.ofNatCore 2 (by decide)),(UInt8.ofNatCore 5 (by decide))]⟩ (UInt8.ofNatCore 5 (by decide))
#eval ByteArray.has? ⟨#[(UInt8.ofNatCore 1 (by decide)),(UInt8.ofNatCore 2 (by decide)),(UInt8.ofNatCore 5 (by decide))]⟩ (UInt8.ofNatCore 0 (by decide))
#eval ByteArray.has? ⟨#[(UInt8.ofNatCore 1 (by decide)),(UInt8.ofNatCore 2 (by decide)),(UInt8.ofNatCore 5 (by decide))]⟩ (UInt8.ofNatCore 3 (by decide))
#eval ByteArray.has? ⟨#[(UInt8.ofNatCore 1 (by decide)),(UInt8.ofNatCore 2 (by decide)),(UInt8.ofNatCore 5 (by decide))]⟩ (UInt8.ofNatCore 10 (by decide))

-- assumes sortes arrays
def ByteArray.intersect (A B: ByteArray) : List (Nat × Nat) :=
  Id.run do
    let mut v := []
    let mut cb := 0
    let mut ca := 0
    for _ in (List.range (A.size + B.size)) do
      if ca < A.size ∧ cb < B.size
      then
        match Ord.compare (A.get! ca) (B.get! cb) with
        | .lt => ca := ca+1
        | .eq => v := (ca,cb) :: v ; ca := ca+1 ; cb := cb+1
        | .gt => cb := cb+1
      else break
    return v


#eval ByteArray.intersect ⟨#[(UInt8.ofNatCore 1 (by decide)),(UInt8.ofNatCore 2 (by decide)),(UInt8.ofNatCore 5 (by decide))]⟩ ⟨#[(UInt8.ofNatCore 1 (by decide)),(UInt8.ofNatCore 2 (by decide)),(UInt8.ofNatCore 5 (by decide))]⟩
#eval ByteArray.intersect ⟨#[(UInt8.ofNatCore 1 (by decide)),(UInt8.ofNatCore 2 (by decide)),(UInt8.ofNatCore 5 (by decide))]⟩ ⟨#[(UInt8.ofNatCore 2 (by decide)),(UInt8.ofNatCore 5 (by decide)),(UInt8.ofNatCore 10 (by decide))]⟩





-- assumes Tries are sorted
partial def Trie.CountCommon [BEq α] (l r : Trie α) : Nat :=
  match l with
  | .leaf x =>
      match r with
      | .leaf y => if x == y then 1 else 0
      | .node1 y _ _ => if x == y then 1 else 0
      | .node y _ _ => if x == y then 1 else 0
  | .node1 x ax cx =>
      match r with
      | .leaf y => if x == y then 1 else 0
      | .node1 y ay cy =>
          if x == y
          then
            if ax == ay
            then Trie.CountCommon cx cy --Nat.succ (Trie.CountCommon cx cy)
            else 0 --1
          else
            if ax == ay
            then (Trie.CountCommon cx cy)
            else 0
      | .node y ay cy =>
          match ay.has? ax with
          | .none => if x == y then 1 else 0
          | .some i =>
                let cym := cy.get! i
                let sofar := (Trie.CountCommon cx cym)
                sofar --if x == y then Nat.succ sofar else sofar
  | .node x ax cx =>
      match r with
      | .leaf y => if x == y then 1 else 0
      | .node1 y ay cy =>
          match ax.has? ay with
          | .none => if x == y then 1 else 0
          | .some i =>
                let cxm := cx.get! i
                let sofar := (Trie.CountCommon cxm cy)
                sofar --if x == y then Nat.succ sofar else sofar
      | .node y ay cy =>
          let ints := ByteArray.intersect ax ay
          let sofar := (ints.map (fun p => Trie.CountCommon (cx.get! p.1) (cy.get! p.2))).foldl (fun r i => i+r) 0
          sofar --if x == y then Nat.succ sofar else sofar




-- write a way to produce a sorted trie from a list of names next
-- note Byte array and corresponding child array should be sorted

#check List.orderedInsert

def List.orderedInsertWithIndex {α : Type _} (r : α → α → Prop) [DecidableRel r] (a : α) : List α → (List α × Nat)
  | [] => ([a], 0)
  | b :: l => if r a b
              then (a :: b :: l, 0)
              else  let (L, c) := orderedInsertWithIndex r a l
                    (b :: L, c+1)

#eval List.orderedInsertWithIndex (· ≤ ·) 3 [1,2,4,5]

def Array.orderedInsert {α : Type _} (r : α → α → Prop) [DecidableRel r] (a : α) (l : Array α) : (Array α ) :=
  let L := List.orderedInsert r a l.data
  (L.toArray)

def Array.orderedInsertWithIndex {α : Type _} (r : α → α → Prop) [DecidableRel r] (a : α) (l : Array α) : (Array α × Nat) :=
  let (L,n) := List.orderedInsertWithIndex r a l.data
  (L.toArray, n)


partial def sorted_upsert (t : Trie α) (s : String) (f : Option α → α) : Trie α :=
  let rec insertEmpty (i : Nat) : Trie α :=
    if h : i < s.utf8ByteSize then
      let c := s.getUtf8Byte i h
      let t := insertEmpty (i + 1)
      .node1 none c t
    else
      .leaf (f .none)
  let rec loop
    | i, .leaf v =>
      if h : i < s.utf8ByteSize then
        let c := s.getUtf8Byte i h
        let t := insertEmpty (i + 1)
        .node1 v c t
      else
        .leaf (f v)
    | i, .node1 v c' t' =>
      if h : i < s.utf8ByteSize then
        let c := s.getUtf8Byte i h
        if c == c'
        then .node1 v c' (loop (i + 1) t')
        else
          let t := insertEmpty (i + 1)
          if c < c'
          then .node v (.mk #[c, c']) #[t, t']
          else .node v (.mk #[c', c]) #[t', t]
      else
        .node1 (f v) c' t'
    | i, .node v cs ts =>
      if h : i < s.utf8ByteSize then
        let c := s.getUtf8Byte i h
        match cs.findIdx? (· == c) with
          | none   =>
            let t := insertEmpty (i + 1)
            let (cs',n) := Array.orderedInsertWithIndex (· ≤ ·) c cs.data
            .node v (⟨cs'⟩) (ts.insertAt! n t)
          | some idx =>
            .node v cs (ts.modify idx (loop (i + 1)))
      else
        .node (f v) cs ts
  loop 0 t

partial def sorted_insert (t : Trie α) (s : String) (val : α) : Trie α :=
  sorted_upsert t s (fun _ => val)


def SortedTrieFormList (namez : List String) : Trie Unit :=
  namez.foldl (fun t s => sorted_insert t s ()) Trie.empty


#eval SortedTrieFormList ["hello", "world", "and", "more", "content"]

partial def ppTrie : Trie Unit → String
| .leaf _ => "leaf"
| .node1 has s c => s!"node1 {has} {String.fromUTF8 ⟨#[s]⟩ (by sorry)} (\n" ++ ppTrie c ++ "\n)"
| .node has s c => s!"node1 {has} {String.fromUTF8 s (by sorry)} (\n" ++ String.intercalate "\n" (c.map ppTrie).toList ++ "\n)"

#eval ppTrie (SortedTrieFormList ["hello", "world", "and", "more", "content"])


#eval Trie.CountCommon (SortedTrieFormList ["hello", "world", "and", "more", "content"]) (SortedTrieFormList ["hello", "world", "and", "more", "content"])
#eval Trie.CountCommon (SortedTrieFormList ["hello", "world", "and", "more", "content"]) (SortedTrieFormList ["hello", "not", "and", "content"])
#eval Trie.CountCommon (SortedTrieFormList ["content", "hello", "world", "more"]) (SortedTrieFormList ["hello", "world", "and", "more"])

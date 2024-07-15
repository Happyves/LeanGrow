

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



def match_nontrivial [BEq α] (l r : Option α) := if !(l == .none) then (l == r) else false -- should avoid a computaiton quite often

--#exit

-- assumes Tries are sorted
partial def Trie.CountCommon [BEq α] (l r : Trie α) : Nat :=
  match l with
  | .leaf x =>
      match r with
      | .leaf y => if match_nontrivial x y then 1 else 0
      | .node1 y _ _ => if match_nontrivial x y then 1 else 0
      | .node y _ _ => if match_nontrivial x y then 1 else 0
  | .node1 x ax cx =>
      match r with
      | .leaf y => if match_nontrivial x y then 1 else 0
      | .node1 y ay cy =>
          if match_nontrivial x y
          then
            if ax == ay
            then Nat.succ (Trie.CountCommon cx cy)
            else 1
          else
            if ax == ay
            then (Trie.CountCommon cx cy)
            else 0
      | .node y ay cy =>
          match ay.has? ax with
          | .none => if match_nontrivial x y then 1 else 0
          | .some i =>
                let cym := cy.get! i
                let sofar := (Trie.CountCommon cx cym)
                if match_nontrivial x y then Nat.succ sofar else sofar
  | .node x ax cx =>
      match r with
      | .leaf y => if match_nontrivial x y then 1 else 0
      | .node1 y ay cy =>
          match ax.has? ay with
          | .none => if match_nontrivial x y then 1 else 0
          | .some i =>
                let cxm := cx.get! i
                let sofar := (Trie.CountCommon cxm cy)
                if match_nontrivial x y then Nat.succ sofar else sofar
      | .node y ay cy =>
          let ints := ByteArray.intersect ax ay
          let sofar := (ints.map (fun p => Trie.CountCommon (cx.get! p.1) (cy.get! p.2))).foldl (fun r i => i+r) 0
          if match_nontrivial x y then Nat.succ sofar else sofar


partial def Trie.intersect [BEq α] (l r : Trie α) : List (Option α)  :=
  match l with
  | .leaf x =>
      match r with
      | .leaf y => if match_nontrivial x y then [y] else []
      | .node1 y _ _ => if match_nontrivial x y then [y] else []
      | .node y _ _ => if match_nontrivial x y then [y] else []
  | .node1 x ax cx =>
      match r with
      | .leaf y => if match_nontrivial x y then [y] else []
      | .node1 y ay cy =>
          if match_nontrivial x y
          then
            if ax == ay
            then  [x] ++ Trie.intersect cx cy --Nat.succ (Trie.CountCommon cx cy)
            else [x] --1
          else
            if ax == ay
            then (Trie.intersect cx cy)
            else []
      | .node y ay cy =>
          match ay.has? ax with
          | .none => []
          | .some i =>
                let cym := cy.get! i
                let sofar := (Trie.intersect cx cym)
                if match_nontrivial x y then [x] ++ sofar else sofar
  | .node x ax cx =>
      match r with
      | .leaf y => if match_nontrivial x y then [y] else []
      | .node1 y ay cy =>
          match ax.has? ay with
          | .none => []
          | .some i =>
                let cxm := cx.get! i
                let sofar := (Trie.intersect cxm cy)
                if match_nontrivial x y then [x] ++ sofar else sofar
      | .node y ay cy =>
          let ints := ByteArray.intersect ax ay
          let sofar := List.join (ints.map (fun p => Trie.intersect (cx.get! p.1) (cy.get! p.2)))
          if match_nontrivial x y then [x] ++ sofar else sofar


--#exit


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


def SortedTrieFormList (namez : List String) : Trie String :=
  namez.foldl (fun t s => sorted_insert t s s) Trie.empty

def SortedTrieFormList' (namez : List String) : Trie Unit :=
  namez.foldl (fun t s => sorted_insert t s ()) Trie.empty


#eval SortedTrieFormList ["hello", "world", "and", "more", "content"]

partial def ppTrie : Trie String → String
| .leaf e => s!"leaf {e}"
| .node1 has s c => s!"node1 {has} {String.fromUTF8 ⟨#[s]⟩ (by sorry)} (\n" ++ ppTrie c ++ "\n)"
| .node has s c => s!"node {has} {String.fromUTF8 s (by sorry)} (\n" ++ String.intercalate "\n" (c.map ppTrie).toList ++ "\n)"

-- #eval ppTrie (SortedTrieFormList ["hello", "world", "and", "more", "content"])
-- #eval ppTrie (SortedTrieFormList ["hello", "world", "and", "more"])
-- #eval ppTrie (SortedTrieFormList ["bool", "boom", "book"])
-- #eval ppTrie (SortedTrieFormList ["hello", "world", "and", "more", "content", ", ", "and", "it", "goes", "on"])
-- #eval ppTrie (SortedTrieFormList ["ban", "banana", "bandana"])


-- #eval "hello".getUtf8Byte 0 (by sorry)

-- #eval String.fromUTF8 ⟨#[("hello".getUtf8Byte 0 (by sorry))]⟩ (by sorry)

-- --#exit


-- #eval Trie.CountCommon (SortedTrieFormList ["hello", "world", "and", "more", "content"]) (SortedTrieFormList ["hello", "world", "and", "more", "content"])
-- #eval Trie.CountCommon (SortedTrieFormList ["hello", "world", "and", "more", "content"]) (SortedTrieFormList ["hello", "not", "and", "content"])
-- #eval Trie.CountCommon (SortedTrieFormList ["content", "hello", "world", "more"]) (SortedTrieFormList ["hello", "world", "and", "more"])
-- #eval Trie.CountCommon (SortedTrieFormList ["bool", "boom", "book"]) (SortedTrieFormList ["hello", "world", "and", "more"])
-- #eval Trie.CountCommon (SortedTrieFormList ["bool", "boom", "book"]) (SortedTrieFormList ["hello", "more"])

-- #eval Trie.intersect (SortedTrieFormList ["hello", "world", "and", "more", "content"]) (SortedTrieFormList ["hello", "world", "and", "more", "content"])
-- #eval Trie.intersect (SortedTrieFormList ["hello", "world", "and", "more", "content"]) (SortedTrieFormList ["hello", "not", "and", "content"])
-- #eval Trie.intersect (SortedTrieFormList ["content", "hello", "world", "more"]) (SortedTrieFormList ["hello", "world", "and", "more"])
-- #eval Trie.intersect (SortedTrieFormList ["bool", "boom", "book"]) (SortedTrieFormList ["hello", "world", "and", "more"])
-- #eval Trie.intersect (SortedTrieFormList ["bool", "boom", "book"]) (SortedTrieFormList ["hello", "more"])
-- #eval Trie.intersect (SortedTrieFormList ["bool", "boom", "book"]) (SortedTrieFormList ["book"])
-- #eval Trie.intersect (SortedTrieFormList ["ban", "banana", "bandana"]) (SortedTrieFormList ["ban"])


#eval (2 : UInt8)
#eval #["testing"]

#eval (⟨#[1,2]⟩ : ByteArray)

def print_bytearray (a : ByteArray) : String :=
  --dbg_trace "comp bytearray"
  s!"⟨#[{String.intercalate "," (a.data.map ToString.toString).toList}]⟩"

#eval print_bytearray (⟨#[1,2]⟩ : ByteArray)


partial def print_trie : Trie Unit → String
  | .leaf x => --dbg_trace "comp trie"
      s!"Lean.Data.Trie.leaf ({x})"
  | .node1 o i t => --dbg_trace "comp trie"
      s!"Lean.Data.Trie.node1 ({o}) {i} ({print_trie t})"
  | .node o i t => --dbg_trace "comp trie"
      s!"Lean.Data.Trie.node ({o}) {print_bytearray i} #[{String.intercalate "," (t.data.map print_trie)}]"


#eval (SortedTrieFormList' ["ban", "banana", "bandana"])

#eval print_trie (SortedTrieFormList' ["ban", "banana", "bandana"])

#eval print_trie (SortedTrieFormList' ["ban", "banana", "banal"])

#eval print_trie (SortedTrieFormList' ["", "ban", "banana", "banal"])


#eval Lean.Data.Trie.node1 (none) 98 (Lean.Data.Trie.node1 (none) 97 (Lean.Data.Trie.node1 (none) 110 (Lean.Data.Trie.node ((some ())) ⟨#[97,100]⟩ #[Lean.Data.Trie.node1 (none) 110 (Lean.Data.Trie.node1 (none) 97 (Lean.Data.Trie.leaf ((some ())))),Lean.Data.Trie.node1 (none) 97 (Lean.Data.Trie.node1 (none) 110 (Lean.Data.Trie.node1 (none) 97 (Lean.Data.Trie.leaf ((some ())))))])))


-- assumes sortes arrays
def ByteArray.merge (A B: ByteArray) : ByteArray:=
  Id.run do
    let mut v := Array.mkEmpty (A.size + B.size)
    let mut cb := 0
    let mut ca := 0
    for _ in (List.range (A.size + B.size)) do
      if ca < A.size ∧ cb < B.size
      then
        let va := (A.get! ca)
        let vb := (B.get! cb)
        match Ord.compare va vb with
        | .lt => v := v.push va ; ca := ca+1
        | .eq => v := v.push va ; ca := ca+1 ; cb := cb+1
        | .gt => v := v.push vb ; cb := cb+1
      else break
    if ca < A.size
    then
      for _ in [ca : A.size] do
        v := v.push (A.get! ca) ; ca := ca+1
    else
      for _ in [cb : B.size] do
        v := v.push (B.get! cb) ; cb := cb+1
    return ⟨v⟩

#eval ByteArray.merge ⟨#[(UInt8.ofNatCore 1 (by decide)),(UInt8.ofNatCore 2 (by decide)),(UInt8.ofNatCore 5 (by decide))]⟩ ⟨#[(UInt8.ofNatCore 2 (by decide)),(UInt8.ofNatCore 5 (by decide)),(UInt8.ofNatCore 10 (by decide))]⟩

mutual

partial def ByteArray.merge_extra [BEq α] [Inhabited α] (A B: ByteArray) (XA XB : Array (Trie α)) : (ByteArray) × (Array (Trie α)):=
  Id.run do
    let mut v := Array.mkEmpty (A.size + B.size)
    let mut x := Array.mkEmpty (A.size + B.size)
    let mut cb := 0
    let mut ca := 0
    for _ in (List.range (A.size + B.size)) do
      if ca < A.size ∧ cb < B.size
      then
        let va := (A.get! ca)
        let vb := (B.get! cb)
        match Ord.compare va vb with
        | .lt => v := v.push va ; x := x.push (XA.get! ca) ; ca := ca+1
        | .eq => v := v.push va ; x := x.push (Trie.merge (XA.get! ca) (XB.get! cb)) ; ca := ca+1 ; cb := cb+1
        | .gt => v := v.push vb ; x := x.push (XB.get! cb) ;  cb := cb+1
      else break
    if ca < A.size
    then
      for _ in [ca : A.size] do
        v := v.push (A.get! ca) ; x := x.push (XA.get! ca) ; ca := ca+1
    else
      for _ in [cb : B.size] do
        v := v.push (B.get! cb) ; x := x.push (XB.get! cb) ; cb := cb+1
    return (⟨v⟩,x)


partial def Trie.merge [BEq α] [Inhabited α] (l r : Trie α) : Trie α  :=
  let mini_merge (x y : Option α) : Option α := (match x with | .some X => X | .none => match y with | .some Y => Y | .none => .none)
  match l with
  | .leaf x =>
      match r with
      | .leaf y => .leaf (mini_merge x y)
      | .node1 y ay cy => .node1 (mini_merge x y) ay cy
      | .node y ay cy => .node (mini_merge x y) ay cy
  | .node1 x ax cx =>
      match r with
      | .leaf y => .node1 (mini_merge x y) ax cx
      | .node1 y ay cy =>
          match Ord.compare ax ay with
          | .lt => .node (mini_merge x y) ⟨#[ax, ay]⟩  #[cx, cy]
          | .eq => .node1 (mini_merge x y) ax  (Trie.merge cx cy)
          | .gt => .node (mini_merge x y) ⟨#[ay, ax]⟩  #[cy, cx]
      | .node y ay cy =>
          match ay.has? ax with
          | .none =>
                let (cs',n) := Array.orderedInsertWithIndex (· ≤ ·) ax ay.data
                .node (mini_merge x y) (⟨cs'⟩) (cy.insertAt! n cx)
          | .some i =>
                .node (mini_merge x y) ay (cy.modify i (Trie.merge cx))
  | .node x ax cx =>
      match r with
      | .leaf y => .node (mini_merge x y) ax cx
      | .node1 y ay cy =>
          match ax.has? ay with
          | .none =>
                let (cs',n) := Array.orderedInsertWithIndex (· ≤ ·) ay ax.data
                .node (mini_merge x y) (⟨cs'⟩) (cx.insertAt! n cy)
          | .some i =>
                .node (mini_merge x y) ax (cx.modify i (Trie.merge cy))
      | .node y ay cy =>
          let (uni_b, uni_t) := ByteArray.merge_extra ax ay cx cy
          .node (mini_merge x y) uni_b uni_t

end


#eval ppTrie (Trie.merge (SortedTrieFormList ["ban", "banana", "banal"]) (SortedTrieFormList ["ban", "banana", "bandana"]))

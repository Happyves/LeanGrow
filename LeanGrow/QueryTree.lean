
import LeanGrow.NameListCompare

open Lean Data


inductive QueryTree  where
| root (c : List (QueryTree))
| node (q : Trie Unit) (c : List (QueryTree))
| leaf
deriving Inhabited


partial def QueryTree.visualize (count : Nat) : QueryTree → String
| .root (c : List (QueryTree)) => s!"Root\n ({String.intercalate "\n" (c.map (QueryTree.visualize 1))})"
| .node (q : Trie Unit) (c : List (QueryTree)) => (String.replicate count ' ') ++ s!"Node ({Trie.print_keys ⟨#[]⟩ q})\n{(String.replicate count ' ')}({String.intercalate "\n" (c.map (QueryTree.visualize (count + 3)))})"
| .leaf => (String.replicate count ' ') ++ "Leaf"


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
| .node x as ts =>  -- **done** we can do better by deleting all entries that lead to .leaf .none
      let cts := ts.map Trie.clean
      let (As, Ts) := Id.run do
            let mut idxs := []
            for i in List.range as.size do
                  match cts.get! i with
                  | .leaf .none => pure ()
                  | _ => idxs := i :: idxs
            let idxz := idxs.reverse
            let len := idxs.length
            let mut As := Array.mkArray len (0 : UInt8)
            let mut Ts := Array.mkArray len Trie.empty
            let mut c := 0
            for i in idxz do
                  As := As.set! c (as.get! i)
                  Ts := Ts.set! c (cts.get! i)
                  c := c+1
            return (As,Ts)
      match x, As.isEmpty with
      | .none, true => .leaf .none
      | .some v, true => .leaf (.some v)
      | _, false => .node x ⟨As⟩ Ts

--   let prune? := Id.run do
--     let mut b := true
--     for t in cts do
--       match t with
--       | .leaf .none => b := false
--       | _ => pure ()
--     return b
--   if prune?
--   then .leaf .none
--   else .node x as ts



-- to NameListCompare
partial def Trie.delete (k : List Char) : Trie α → Trie α
| .leaf _ => .leaf .none
| .node1 x a t =>
      --dbg_trace s!"{String.fromUTF8 ⟨#[a]⟩ (by sorry)} {x.isSome} {k}"
      match k with
      | [] => .node1 .none a t
      | c :: rest => if c.toUInt8 == a then .node1 x a (Trie.delete rest t) else .node1 x a t
| .node x as ts =>
      --dbg_trace s!"{as.data.map (String.fromUTF8 ⟨#[·]⟩ (by sorry))} {x.isSome} {k}"
      match k with
      | [] => .node .none as ts
      | c :: rest =>
          let idiomatic := c.toUInt8
          let idx? := as.findIdx? (· == idiomatic)
          match idx? with
          | .some idx => .node x as (ts.modify idx (fun t => Trie.delete rest t))
          | .none => .node x as ts

#eval Trie.print_keys ⟨#[]⟩  (Trie.delete "ban".data (SortedTrieFormList' ["ban", "banal", "bandana"]))
#eval Trie.print_keys ⟨#[]⟩  (Trie.delete "bandana".data (SortedTrieFormList' ["ban", "banal", "bandana"]))
#eval Trie.print_keys ⟨#[]⟩  (Trie.delete "banal".data (SortedTrieFormList' ["ban", "banal", "bandana"]))



def QueryTree.map_on_children (f : QueryTree → QueryTree) : QueryTree → QueryTree
| .root (c : List (QueryTree)) => .root (c.map f)
| .node (q : Trie Unit) (c : List (QueryTree)) => .node q (c.map f)
| .leaf => .leaf

def QueryTree.delete_key_or_leave (k : String) : QueryTree → QueryTree :=
  let kd := k.data
  fun t =>  match t with
            | .node T r => .node (Trie.clean (Trie.delete kd T)) r
            | x => x


def QueryTree.split_maintain_on (k : String) (c : List (QueryTree)) : List (QueryTree) :=
  let (pos, neg) := QueryTree.split_on_split k c
  let pos' := pos.map (fun qt => qt.delete_key_or_leave k)
  (.node (SortedTrieFormList' [k]) pos') :: neg



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


partial def QueryTree.split_greedy_exact_hitting_set (c : List (QueryTree)) : List (QueryTree) :=
      match c with
      | [] => []
      | _ =>
            let apps := QueryTree.find_keys c
            match Trie.find_max ⟨#[]⟩ apps with
            | .none => c
            | .some (name, _) =>
                  let (pos, neg) := QueryTree.split_on_split name c
                  let pos' := pos.map (fun qt => QueryTree.delete_key_or_leave name qt)
                  let proceed := QueryTree.split_greedy_exact_hitting_set neg

                  match pos' with
                  | [] =>  proceed
                  | _ => (.node (SortedTrieFormList' [name]) pos') :: proceed

partial def QueryTree.build_main (c : List (QueryTree)) : Trie Unit × List (QueryTree) :=
      match c with
      | [] => (Trie.empty,[])
      | _ =>
            let rec lift (c : List (QueryTree)) : Trie Unit × List (QueryTree) :=
                  let apps := QueryTree.find_keys c
                  match Trie.find_max ⟨#[]⟩ apps with
                  | .none => (Trie.empty,c)
                  | .some (name, M) =>
                        if M = c.length
                        then  let c' := c.map (fun qt => QueryTree.delete_key_or_leave name qt)
                              let (T,cf) := lift c'
                              (sorted_insert T name (), cf)
                        else (Trie.empty,c)
            let (lifted_names, listed_children) := lift c
            (lifted_names, QueryTree.split_greedy_exact_hitting_set listed_children)




partial def QueryTree.build (count : Nat) : QueryTree → QueryTree
| .root c =>
      let (l,cn) := QueryTree.build_main c
      match l with
      | .leaf .none => .root (cn.map (QueryTree.build (count+1)))
      | _=> .root [.node l (cn.map ((QueryTree.build) (count+1)) )]
| .node t c =>
      let (l,cn) := QueryTree.build_main c
      if cn.isEmpty
      then   .node (Trie.merge t l) [.leaf]
      else   .node (Trie.merge t l) (cn.map (QueryTree.build (count+1)))
| .leaf =>  .leaf



-- def QueryTree.toPrune : QueryTree → List (QueryTree)
-- | .node (.leaf .none) x => x
-- | x => [x]

-- partial def QueryTree.clean : QueryTree → QueryTree
-- | .root c => .root (List.join ((c.map QueryTree.clean).map QueryTree.toPrune ))
-- | .node t c => .node t (List.join ((c.map QueryTree.clean).map QueryTree.toPrune ))
-- | .leaf => .leaf


def QueryTree.make (l : List (Trie Unit)) : QueryTree := (QueryTree.build 0 (QueryTree.init  l))


partial def QueryTree.toString : QueryTree → String
| .root (c : List (QueryTree)) => s!"QueryTree.root ([{String.intercalate ", " (c.map QueryTree.toString)}])"
| .node (q : Trie Unit) (c : List (QueryTree)) => s!"QueryTree.node ({print_trie q}) ([{String.intercalate ", " (c.map QueryTree.toString)}])"
| .leaf => "QueryTree.leaf"



def test_trees := QueryTree.init ([["ban", "banana"], ["ban", "banal"], ["ban", "bandana"],["and","some","more","banana"]].map SortedTrieFormList')

#eval (QueryTree.visualize 0 ((QueryTree.build 0 test_trees))).toFormat

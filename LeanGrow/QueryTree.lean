
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


#exit

-- TODO : clean Tries → process children ; if only leaves with none, replace node by leaf with none
-- apply cleaning after deletes ; otherwise a lot of dead branches ...

partial def Trie.cut (t : Trie Nat) (s : Nat) (ratio : Float) :  Trie Unit :=
  let main_cut (x : Option Nat) : Option Unit :=
    match x with
    | .some y => if (Nat.toFloat y) / (Nat.toFloat s) ≥ ratio then .some () else .none
    | .none => .none
  let rec go : Trie Nat → Trie Unit
    | .leaf x => .leaf (main_cut x)
    | .node1 x ax cx => .node1 (main_cut x) ax (Trie.cut cx s ratio)
    | .node x ax cx => .node (main_cut x) ax (cx.map (Trie.cut · s ratio))
  go t

def QueryTree.lift_on (k : String) (c : List (QueryTree)) : List (QueryTree) × List (QueryTree) :=
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

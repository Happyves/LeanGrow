
import LeanGrow.NameListCompare

open Lean Data



inductive QueryTree (α : Type _)  where
| root (c : List (QueryTree α ))
| node (q : Trie Unit) (c : List (QueryTree α ))
| leaf (a : α)
deriving Inhabited


partial def QueryTree.visualize (count : Nat) : QueryTree α → String
| .root (c : List (QueryTree α)) => s!"Root\n ({String.intercalate "\n" (c.map (QueryTree.visualize 1))})"
| .node (q : Trie Unit) (c : List (QueryTree α)) => (String.replicate count ' ') ++ s!"Node ({Trie.print_keys ⟨#[]⟩ q})\n{(String.replicate count ' ')}({String.intercalate "\n" (c.map (QueryTree.visualize (count + 3)))})"
| .leaf _ => (String.replicate count ' ') ++ "Leaf"

-- to fix : remove inhabited and make use of actual data
def QueryTree.init (l : List (Trie Unit)) [Inhabited α] : QueryTree α := .root (l.map (fun x => .node x [.leaf default]))

def QueryTree.find_keys (c : List (QueryTree α)) : Trie Nat :=
  match c with
  | [] => Trie.empty
  | .root _ :: _ => Trie.empty -- ill formed tree, root shouldn't appear as child
  | .node t _ :: rest =>
        let sofar := QueryTree.find_keys rest
        let T := Trie.merge_count_initialise t
        Trie.merge_count T sofar
  | .leaf _ :: rest => QueryTree.find_keys rest

def QueryTree.split_on_split (k : String) (c : List (QueryTree α)) : List (QueryTree α) × List (QueryTree α) :=
  match c with
  | [] => ([],[])
  | .root _ :: _ => ([],[]) -- ill formed tree, root shouldn't appear as child
  | .node t chi :: rest =>
        let (sofar_pos, sofar_neg) := QueryTree.split_on_split k rest
        let T := t.find? k
        match T with
        | .some _ => (.node t chi :: sofar_pos, sofar_neg)
        | .none => (sofar_pos, .node t chi :: sofar_neg)
  | .leaf a :: rest =>
        let (sofar_pos, sofar_neg) := QueryTree.split_on_split k rest
        (sofar_pos, .leaf a :: sofar_neg)


def QueryTree.split_on (k : String) (c : List (QueryTree α)) : List (QueryTree α) :=
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



def QueryTree.map_on_children (f : QueryTree α → QueryTree α) : QueryTree α → QueryTree α
| .root (c : List (QueryTree α)) => .root (c.map f)
| .node (q : Trie Unit) (c : List (QueryTree α)) => .node q (c.map f)
| .leaf a => .leaf a

def QueryTree.delete_key_or_leave (k : String) : QueryTree α → QueryTree α :=
  let kd := k.data
  fun t =>  match t with
            | .node T r => .node ((Trie.delete kd T)) r --.node (Trie.clean (Trie.delete kd T)) r
            | x => x


def QueryTree.split_maintain_on (k : String) (c : List (QueryTree α)) : List (QueryTree α) :=
  let (pos, neg) := QueryTree.split_on_split k c
  let pos' := pos.map (fun qt => qt.delete_key_or_leave k)
  (.node (SortedTrieFormList' [k]) pos') :: neg



def QueryTree.lift_topmost_on (k : String) : QueryTree α → QueryTree α
| .root (c : List (QueryTree α)) => .root [.node (SortedTrieFormList' [k]) (c.map (QueryTree.delete_key_or_leave  k))]
| .node (q : Trie Unit) (c : List (QueryTree α)) => .node (sorted_insert q k ()) (c.map (QueryTree.delete_key_or_leave k))
| .leaf a => .leaf a


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


partial def QueryTree.split_greedy_exact_hitting_set (c : List (QueryTree α)) : List (QueryTree α) :=
      let apps := QueryTree.find_keys c
      match Trie.find_max ⟨#[]⟩ apps with
      | .none => c
      | .some (name, M) =>
            if M > 1
            then  let (pos, neg) := QueryTree.split_on_split name c
                  let pos' := pos.map (fun qt => QueryTree.delete_key_or_leave name qt)
                  let proceed := QueryTree.split_greedy_exact_hitting_set neg
                  (.node (SortedTrieFormList' [name]) pos') :: proceed
            else  c



/-

Make lifting more efficient as its the mass stackspace consumer in the crashes.

- instead of recomputing apps:
      - upsert the value at maximising key by deacresing it ?
      - make a version of find_max that ignores branches of a tree that we iteraively megre the maximising keys to ?

-/


partial def QueryTree.lift (c : List (QueryTree α)) : Trie Unit × List (QueryTree α) :=
                  let apps := QueryTree.find_keys c
                  match Trie.find_max ⟨#[]⟩ apps with
                  | .none => (Trie.empty,c)
                  | .some (name, M) =>
                        if M = c.length
                        then  let c' := c.map (fun qt => QueryTree.delete_key_or_leave name qt)
                              let (T,cf) := lift c'
                              (sorted_insert T name (), cf)
                        else (Trie.empty,c)




partial def Trie.find_maxes (cache : ByteArray) : Trie Nat → Option (Trie Unit × Nat)
| .leaf x =>
      match x with
      | .some v => .some (SortedTrieFormList' [(String.fromUTF8 cache (by sorry))], v)
      | .none => .none
| .node1 x a t =>
      match Trie.find_maxes (cache.push a) t with
      | .some (s,v) =>
          match x with
          | .some w => match compare w v with
                       | .gt => .some (SortedTrieFormList' [(String.fromUTF8 cache (by sorry))], w)
                       | .eq => .some (sorted_insert s ((String.fromUTF8 cache (by sorry))) () ,v)
                       | .lt => .some (s,v)
          | .none => .some (s,v)
      | .none =>
          match x with
          | .some w => .some (SortedTrieFormList' [(String.fromUTF8 cache (by sorry))], w)
          | .none => .none
| .node x as ts => Id.run do
      let mut M := 0
      let mut T := Trie.empty
      for i in Array.range as.size do
        let a := as.get! i
        let t := ts.get! i
        match Trie.find_maxes (cache.push a) t with
        | .some (s,v) =>
            match compare v M with
            | .gt =>
                  M := v
                  T := s
            | .eq =>
                  T := Trie.merge T s
            | .lt => pure ()
        | .none => pure ()
      match x with
      | .some w => match compare w M with
                   | .gt => .some (SortedTrieFormList' [(String.fromUTF8 cache (by sorry))], w)
                   | .eq => .some (sorted_insert T ((String.fromUTF8 cache (by sorry))) () ,w)
                   | .lt => .some (T,M)
      | .none => .some (T,M)



def QueryTree.delete_keyes_or_leave (k : Trie Unit) : QueryTree α → QueryTree α :=
  fun t =>  match t with
            | .node T r => .node ((Trie.filter T k)) r
            | x => x

partial def QueryTree.lift' (c : List (QueryTree α)) : Trie Unit × List (QueryTree α) :=
                  let apps := QueryTree.find_keys c
                  match Trie.find_maxes ⟨#[]⟩ apps with
                  | .none => (Trie.empty,c)
                  | .some (names, M) =>
                        if M = c.length
                        then  let c' := c.map (fun qt => QueryTree.delete_keyes_or_leave names qt)
                              (names, c')
                        else (Trie.empty,c)


--#exit


partial def QueryTree.build_main (c : List (QueryTree α)) : Trie Unit × List (QueryTree α) :=
      let (lifted_names, listed_children) := QueryTree.lift' c
      (lifted_names, QueryTree.split_greedy_exact_hitting_set listed_children)



partial def QueryTree.build [Inhabited α] : QueryTree α → QueryTree α
| .root c =>
      let (l,cn) := QueryTree.build_main c
      match l with
      | .leaf .none => .root (cn.map (QueryTree.build))
      | _=> .root [.node l (cn.map ((QueryTree.build)) )]
| .node t c =>
      let (l,cn) := QueryTree.build_main c
      if cn.isEmpty
      then   .node (Trie.merge t l) [.leaf default]
      else   .node (Trie.merge t l) (cn.map (QueryTree.build))
| .leaf a =>  .leaf a



def QueryTree.make [Inhabited α] (l : List (Trie Unit)) : QueryTree  α := (QueryTree.build (QueryTree.init l))


partial def QueryTree.toString (string_alpha : α → String) : QueryTree  α → String
| .root (c : List (QueryTree α)) => s!"QueryTree.root ([{String.intercalate ", " (c.map (QueryTree.toString string_alpha))}])"
| .node (q : Trie Unit) (c : List (QueryTree α)) => s!"QueryTree.node ({print_trie q}) ([{String.intercalate ", " (c.map (QueryTree.toString string_alpha))}])"
| .leaf a => s!"QueryTree.leaf ({string_alpha a})"



def test_trees : QueryTree Unit := QueryTree.init ([["ban", "banana"], ["ban", "banal"], ["ban", "bandana"],["and","some","more","banana"]].map SortedTrieFormList')

#eval (QueryTree.visualize 0 ((QueryTree.build test_trees))).toFormat
#eval (QueryTree.visualize 0 ((QueryTree.make ([["ban", "banana"], ["ban", "banal"], ["ban", "bandana"],["and","some","more","banana"]].map SortedTrieFormList')) : QueryTree Unit)).toFormat

#eval (QueryTree.visualize 0 ((QueryTree.make ([["ban", "bon", "banana"], ["ban", "bon", "banal"], ["ban", "bandana"],["and","some","more","banana", "bon"]].map SortedTrieFormList')) : QueryTree Unit)).toFormat


def QueryTree.init_wData (l : List ((Trie Unit) × α)) : QueryTree α := .root (l.map (fun (t,d) => .node t [.leaf d]))

def QueryTree.make_wData [Inhabited α]  (l : List ((Trie Unit) × α)) : QueryTree  α := (QueryTree.build (QueryTree.init_wData l))


-- # BS

inductive BS (α : Type _) where
| ofVal (_ : α)
| ofPoint (_ : QueryTree (BS α))
deriving Inhabited


inductive preBS (α : Type _) where
| ofVal (_ : α)
| ofPoint (_ : Nat)

partial def QueryTree.stratify (depth count idx : Nat) (T : QueryTree α ) : Nat × List (Nat × QueryTree (preBS α)) × (QueryTree (preBS α)) :=
      match T with
      | .node t c =>
            if count = 0
            then  let (idx_c, qts, pqt) := QueryTree.stratify depth depth idx (.root c)
                  let link := .node t [.leaf (.ofPoint idx_c)]
                  (idx_c + 1, (idx_c, pqt) :: qts, link)
            else  Id.run do
                        let mut i := idx
                        let mut rev_pqt := []
                        let mut qts_all := []
                        for qt in c do
                              let (idx_c, qts, pqt) := QueryTree.stratify depth (count-1) i qt
                              i := idx_c + 1
                              rev_pqt := pqt :: rev_pqt
                              qts_all := qts ++ qts_all
                        return (i, qts_all, .node t rev_pqt)
      | .root c => -- shouldn't occure but I'll code anyway
            if count = 0
            then  let (idx_c, qts, pqt) := QueryTree.stratify depth depth idx (.root c)
                  let link := .root [.leaf (.ofPoint idx_c)]
                  (idx_c + 1, (idx_c, pqt) :: qts, link)
            else  Id.run do
                        let mut i := idx
                        let mut rev_pqt := []
                        let mut qts_all := []
                        for qt in c do
                              let (idx_c, qts, pqt) := QueryTree.stratify depth (count-1) i qt
                              i := idx_c + 1
                              rev_pqt := pqt :: rev_pqt
                              qts_all := qts ++ qts_all
                        return (i, qts_all, .root rev_pqt)
      | .leaf a => (idx, [], .leaf (.ofVal a))


def test_tree' := ((QueryTree.make ([["ban", "bon", "banana"], ["ban", "bon", "banal"], ["ban", "bandana"],["and","some","more","banana", "bon"]].map SortedTrieFormList')) : QueryTree Unit)

partial def QueryTree.visualize' (count : Nat) : QueryTree (preBS α) → String
| .root (c : List (QueryTree (preBS α))) => s!"Root\n ({String.intercalate "\n" (c.map (QueryTree.visualize' 1))})"
| .node (q : Trie Unit) (c : List (QueryTree (preBS α))) => (String.replicate count ' ') ++ s!"Node ({Trie.print_keys ⟨#[]⟩ q})\n{(String.replicate count ' ')}({String.intercalate "\n" (c.map (QueryTree.visualize' (count + 3)))})"
| .leaf bs => (String.replicate count ' ') ++ s!"Leaf {match bs with | .ofVal _ => "val" | .ofPoint x => s!"pointer {x}"}"


#eval (QueryTree.visualize' 0 (QueryTree.stratify 1 1 0 test_tree').2.2).toFormat
#eval (String.join (((QueryTree.stratify 1 1 0 test_tree').2.1).map (fun (n,t) => s!"\nTree {n}:\n" ++ (QueryTree.visualize' 0 t)))).toFormat
#eval (QueryTree.stratify 1 1 0 test_tree').1

def QueryTree.stratify_full (depth : Nat) (T : QueryTree α ) : Nat × List (Nat × QueryTree (preBS α)) :=
      let (c,l,qt) := QueryTree.stratify depth depth 0 T
      (c, (c,qt) :: l)

#check QueryTree.toString


def preBS.toString_trick {α : Type _} (string_alpha : α → String) : preBS α → String
| .ofVal (a : α) => s!"(BS.ofVal ({string_alpha a}))"
| .ofPoint (p : Nat) => s!"(BS.ofPoint qete_{p})"

def QueryTree.toString_preBS (T : QueryTree (preBS α)) (string_alpha : α → String) : String :=
      QueryTree.toString (preBS.toString_trick string_alpha) T

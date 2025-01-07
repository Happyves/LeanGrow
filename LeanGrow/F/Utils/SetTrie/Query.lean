
import LeanGrow.F.Utils.SetTrie.Build


#check 1

namespace SetTrie


partial def depth (T : SetTrie α β) : Nat :=
  let rec go (candidates : List Nat) (depth : Nat) : List (SetTrie α β) → Nat
    | [] => depth
    | t :: ts =>
        match t with
        | .leaf _ =>
            match candidates with
            | n :: more => go more (if n > depth then n else depth) ts
            | _ => 0
        | .root c | .node _ c =>
            match candidates with
            | n :: more =>
                go ((List.replicate c.length (n+1)) ++ more) depth (c ++ ts)
            | _ => 0
  go [0] 0 [T]


partial def depth' : SetTrie α β →  Nat
  | .root c | .node _ c => match List.maximum? (c.map depth') with | .some x => x+1 | .none => 1
  | .leaf _ => 0


def join_buggy_leaves_main [BEq β] (emptyB : β) : List (SetTrie α β) → (List α) × List (SetTrie α β)
| [] => ([],[])
| x :: l =>
      match x with
      | .node y [.leaf ( a)] =>
        let (j,o) := join_buggy_leaves_main emptyB l
        if y == emptyB
        then (a :: j, o)
        else (j, x :: o)
      | .leaf (a) => let (j,o) := join_buggy_leaves_main emptyB l ; (a :: j, o)
      | x =>  let (j,o) := join_buggy_leaves_main emptyB l ; (j, x :: o)

partial def getVals (T : SetTrie α β) : List α :=
  let rec go (done : List α) : List (SetTrie α β) → (List α)
    | [] => done
    | nx :: more =>
        match nx with
        | .leaf a => go (a :: done) more
        | .root c | .node _ c => go done (c ++ more)
  go [] [T]


partial def query' (inter : β → β → Bool) (Q : β) (T : SetTrie α β) : List α :=
  match T with
  | .root c => (c.map (query' inter Q)).join
  | .node t c => if inter t Q then (c.map (query' inter Q)).join else []
  | .leaf a => [a]


partial def query (inter : β → β → Bool) (Q : β) (T : SetTrie α β) : List α :=
  let rec go (done : List α) : List (SetTrie α β) → List α
    | [] => done
    | nx :: more =>
        match nx with
        | .root c => go done (c ++ more)
        | .node t c => if inter t Q then go done (c ++ more) else go done more
        | .leaf a => go (a :: done) more
  go [] [T]

/-- Ignores entries with key of number (not actual key size ; example Trie size) ≤ then depth-/
partial def queryWC (inter : β → β → Bool) (Q : β) (depth : Nat) (T : SetTrie α β) : List α :=
  let rec go (done : List α) : List (Nat × SetTrie α β) → List α
    | [] => done
    | (nxd,nx) :: more =>
        match nx with
        | .root c => go done ((c.map (fun x => (1,x))) ++ more)
        | .node t c => if inter t Q then go done ((c.map (fun x => (nxd.succ,x))) ++ more) else go done more
        | .leaf a => if nxd > depth then go (a :: done) more else go done more
  go [] [(0,T)]

partial def queryDeepest [Inhabited α] (inter : β → β → Bool) (Q : β) (T : SetTrie α β) : α :=
  let rec go (depth : Nat) (done : α) : List (Nat × SetTrie α β) → α
    | [] => done
    | (nxd,nx) :: more =>
        match nx with
        | .root c => go 0 done ((c.map (fun x => (1,x))) ++ more)
        | .node t c => if inter t Q then go depth done ((c.map (fun x => (nxd.succ,x))) ++ more) else go depth done more
        | .leaf a => if nxd > depth then go nxd a more else go depth done more
  go 0 default [(0,T)]

partial def queryDeepests [Inhabited α] (inter : β → β → Bool) (Q : β) (T : SetTrie α β) : List α :=
  let rec go (depth : Nat) (done : List α) : List (Nat × SetTrie α β) → List α
    | [] => done
    | (nxd,nx) :: more =>
        match nx with
        | .root c => go 0 done ((c.map (fun x => (1,x))) ++ more)
        | .node t c => if inter t Q then go depth done ((c.map (fun x => (nxd.succ,x))) ++ more) else go depth done more
        | .leaf a =>
            match compare nxd depth with
            | .gt => go nxd [a] more
            | .eq => go depth (a :: done) more
            | _ => go depth done more
  go 0 default [(0,T)]

partial def queryHeaviests [Inhabited α] (inter : β → β → Bool) (weight : β → Nat) (Q : β) (T : SetTrie α β) : List α :=
  let rec go (depth : Nat) (done : List α) : List (Nat × SetTrie α β) → List α
    | [] => done
    | (nxd,nx) :: more =>
        match nx with
        | .root c => go 0 done ((c.map (fun x => (0,x))) ++ more)
        | .node t c => if inter t Q then go depth done ((c.map (fun x => (nxd + weight t,x))) ++ more) else go depth done more
        | .leaf a =>
            match compare nxd depth with
            | .gt => go nxd [a] more
            | .eq => go depth (a :: done) more
            | _ => go depth done more
  go 0 default [(0,T)]

partial def map (inter : β → β → Bool) (Q : β) (T : SetTrie α β) (f : α → α) : SetTrie α β :=
  let rec go (T : SetTrie α β) : SetTrie α β := -- will overflow for sure
    match T with
    | .root c => .root (c.map go)
    | .node t c => if inter t Q then .node t (c.map go) else T
    | .leaf a => .leaf (f a)
  go T

partial def mapWC (inter : β → β → Bool) (Q : β) (depth : Nat) (T : SetTrie α β) (f : α → α) : SetTrie α β :=
  let rec go (d : Nat) (T : SetTrie α β) : SetTrie α β := -- will overflow for sure
    match T with
    | .root c => .root (c.map (go (d+1)))
    | .node t c => if inter t Q then .node t (c.map (go (d+1))) else T
    | .leaf a => if d ≥ depth then .leaf (f a) else T
  go 0 T

partial def mapDeepest (inter : β → β → Bool) (Q : β) (T : SetTrie α β) (f : α → α) : SetTrie α β :=
  let rec split (pos leafs neg : List (SetTrie α β))
    : List (SetTrie α β) → (List (SetTrie α β) × List (SetTrie α β) × List (SetTrie α β))
      | [] => (pos,leafs,neg)
      | nx :: more =>
          match nx with
          | .leaf _ => split pos ( nx :: leafs) neg more
          | .node k _ => if inter k Q then split (nx :: pos) leafs neg more else split pos leafs (nx :: neg) more
          | .root _ => split pos leafs neg more -- shoudn't
  let rec go (T : SetTrie α β) : SetTrie α β :=
    match T with
    | .root c =>
        let (pos,ls,neg) := split [] [] [] c
        match pos with
        | [] => .root ((ls.map go) ++ neg)
        | _ => .root ((pos.map go) ++ ls ++ neg)
    | .node t c =>
        let (pos,ls,neg) := split [] [] [] c
        match pos with
        | [] => .node t ((ls.map go) ++ neg)
        | _ => .node t ((pos.map go) ++ ls ++ neg)
    | .leaf a => .leaf (f a)
  go T

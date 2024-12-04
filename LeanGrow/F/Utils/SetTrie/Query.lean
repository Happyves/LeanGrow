
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


import LeanGrow.F.Utils.SetTrie.Build


#check 1

namespace SetTrie

/-- to test! -/
partial def depth (T : SetTrie α β) : Nat :=
  let rec go (candidates depths : List Nat) : List (SetTrie α β) → Nat
    | [] =>
        match List.maximum? depths with
        | .some x => x
        | _ => 0
    | t :: ts =>
        match t with
        | .leaf _ =>
            match candidates with
            | n :: more => go more ((n+1) :: depths) ts
            | _ => 0
        | .root c | .node _ c =>
            match candidates with
            | n :: more =>
                go ((List.replicate c.length (n+1)) ++ more) depths (c ++ ts)
            | _ => 0
  go [0] [] [T]

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

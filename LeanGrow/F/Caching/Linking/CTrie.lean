
import LeanGrow.F.Caching.Linking.Types

open Lean


partial def sCTrie.depth (T : sCTrie α) : Nat :=
  let rec go (candidates : List Nat) (depth : Nat) : List (sCTrie α) → Nat
    | [] => depth
    | t :: ts =>
        match t with
        | .leaf _ =>
            match candidates with
            | n :: more => go more (if n > depth then n else depth) ts
            | _ => 0
        | .node1 _ _ c =>
            match candidates with
            | n :: more => go ((n+1) :: more) depth (c :: ts)
            | _ => 0
        | .node _ _ c =>
            match candidates with
            | n :: more =>
                go ((List.replicate c.size (n+1)) ++ more) depth (c.toList ++ ts)
            | _ => 0
        | .pointer _ =>
            match candidates with
            | n :: more => go more (if n > depth then n else depth) ts
            | _ => 0
  go [0] 0 [T]

namespace CTrie

def stratifyOnDepth (T : CTrie α) (d : Nat) : sCTrie α × List (Nat × sCTrie α) :=
  let rec go (indC : Nat) (done : List (Nat × sCTrie α)) : CTrie α → Nat × sCTrie α × List (Nat × sCTrie α)
    | .leaf x => (indC, .leaf x, done)
    | .node1 x a c =>
        let (ni, nt, nd) := go indC done c
        let NT := sCTrie.node1 x a nt
        let dep := NT.depth
        if dep > d
        then
          (indC+1, .pointer indC, (indC, NT) :: done)
        else
          (indC, NT, done)
    | .node1 x a c =>
  sorry

-- adaptative version that also take width into account (ie. big width (# of children) => depth 1)

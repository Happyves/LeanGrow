
import LeanGrow.F.Utils.Trie.Sorted

open Lean


inductive sCTrie (α : Type) where
  | leaf : Option α → sCTrie α
  | node1 : Option α → ByteArray → sCTrie α → sCTrie α
  | node : Option α → Array ByteArray → Array (sCTrie α) → sCTrie α
  | pointer (_ : Nat)
deriving Repr, BEq, Inhabited


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

partial def stratifyOnDepth (T : CTrie α) (d : Nat) : sCTrie α × List (Nat × sCTrie α) :=
  let rec inner (indC : Nat) (TS : Array (sCTrie α)) (done : List (Nat × sCTrie α)) (ref : Array (CTrie α))
    (go : Nat → List (Nat × sCTrie α) → CTrie α → Nat × sCTrie α × List (Nat × sCTrie α))
    : Nat → Nat × Array (sCTrie α) × List (Nat × sCTrie α)
      | 0 => (indC, TS, done)
      | n+1 =>
          let (ni, nt, nd) := go indC done (ref.get! n)
          inner ni (TS.set! n nt) nd ref go n
  let rec go (indC : Nat) (done : List (Nat × sCTrie α)) : CTrie α → Nat × sCTrie α × List (Nat × sCTrie α)
    | .leaf x => (indC, .leaf x, done)
    | .node1 x a c =>
        let (ni, nt, nd) := go indC done c
        let NT := sCTrie.node1 x a nt
        let dep := NT.depth
        if dep > d
        then
          (ni+1, .pointer indC, (indC, NT) :: nd)
        else
          (ni, NT, nd)
    | .node x a c =>
        let (ni, nts, nd) := inner indC (Array.mkArray c.size (.leaf .none)) done c go c.size
        let NT := sCTrie.node x a nts
        let dep := NT.depth
        if dep > d
        then
          (ni+1, .pointer indC, (indC, NT) :: nd)
        else
          (ni, NT, nd)
  (go 0 [] T).2


partial def stratify (T : CTrie α) (d w : Nat) : sCTrie α × List (Nat × sCTrie α) :=
  let rec inner (indC : Nat) (TS : Array (sCTrie α)) (done : List (Nat × sCTrie α)) (ref : Array (CTrie α))
    (go : Nat → List (Nat × sCTrie α) → CTrie α → Nat × sCTrie α × List (Nat × sCTrie α))
    : Nat → Nat × Array (sCTrie α) × List (Nat × sCTrie α)
      | 0 => (indC, TS, done)
      | n+1 =>
          let (ni, nt, nd) := go indC done (ref.get! n)
          inner ni (TS.set! n nt) nd ref go n
  let rec Inner (indC : Nat) (TS : Array (sCTrie α)) (done : List (Nat × sCTrie α)) (ref : Array (CTrie α))
    (go : Nat → List (Nat × sCTrie α) → CTrie α → Nat × sCTrie α × List (Nat × sCTrie α))
    : Nat → Nat × Array (sCTrie α) × List (Nat × sCTrie α)
      | 0 => (indC, TS, done)
      | n+1 =>
          let (ni, nt, nd) := go indC done (ref.get! n)
          Inner (ni+1) (TS.set! n (.pointer ni)) ((ni, nt) :: nd) ref go n
  let rec go (indC : Nat) (done : List (Nat × sCTrie α)) : CTrie α → Nat × sCTrie α × List (Nat × sCTrie α)
    | .leaf x => (indC, .leaf x, done)
    | .node1 x a c =>
        let (ni, nt, nd) := go indC done c
        let NT := sCTrie.node1 x a nt
        let dep := NT.depth
        if dep > d
        then
          (ni+1, .pointer ni, (ni, NT) :: nd)
        else
          (ni, NT, nd)
    | .node x a c =>
        if c.size < w
        then
          let (ni, nts, nd) := inner indC (Array.mkArray c.size (.leaf .none)) done c go c.size
          let NT := sCTrie.node x a nts
          let dep := NT.depth
          if dep > d
          then
            (ni+1, .pointer ni, (ni, NT) :: nd)
          else
            (ni, NT, nd)
        else
          let (ni, nts, nd) := Inner indC (Array.mkArray c.size (.leaf .none)) done c go c.size
          (ni, sCTrie.node x a nts, nd)
  (go 0 [] T).2


#check 1



-- /-
-- Testing elaboration.
-- Seems to be pretty performent ? So we don't have to worry about large arrays ?
-- -/

-- def test : IO Unit := do
--   let mut l : List Nat := []
--   for _ in (List.range 800) do
--     let new ← IO.rand 1 37
--     l := new :: l
--   IO.println l

-- --#eval test

-- def test_elab :=
--   #[23, 8, 22, 18, 6, 25, 16, 31, 23, 31, 11, 19, 6, 21, 18, 17, 18, 11, 1, 18, 7, 17, 27, 34, 22, 24, 9, 19, 36, 22, 29, 13, 16, 28, 25, 37, 26, 21, 9, 28, 22, 10, 34, 30, 17, 36, 3, 9, 13, 32, 10, 29, 21, 19, 24, 21, 8, 7, 21, 24, 11, 11, 10, 16, 7, 14, 28, 35, 31, 6, 29, 16, 30, 24, 29, 24, 31, 11, 23, 6, 8, 21, 35, 23, 14, 26, 14, 11, 3, 11, 23, 25, 5, 28, 25, 24, 6, 7, 28, 20, 20, 25, 2, 16, 27, 24, 34, 7, 7, 34, 30, 31, 27, 14, 27, 5, 24, 30, 37, 23, 19, 31, 34, 18, 8, 21, 7, 22, 9, 17, 9, 29, 25, 2, 6, 5, 13, 23, 26, 7, 20, 1, 16, 18, 10, 4, 3, 11, 25, 34, 28, 23, 34, 24, 31, 18, 37, 11, 32, 2, 16, 4, 19, 23, 31, 9, 16, 26, 1, 14, 35, 2, 30, 27, 37, 34, 17, 36, 25, 13, 14, 29, 29, 20, 27, 9, 33, 14, 25, 4, 30, 30, 33, 4, 27, 24, 1, 28, 6, 20, 8, 24, 6, 33, 16, 2, 9, 9, 25, 4, 34, 36, 11, 24, 11, 15, 21, 11, 10, 9, 6, 17, 16, 6, 25, 19, 13, 23, 8, 1, 26, 29, 27, 26, 13, 16, 32, 29, 35, 6, 33, 26, 35, 3, 36, 22, 28, 18, 24, 4, 30, 3, 1, 22, 22, 13, 30, 16, 12, 24, 17, 9, 11, 9, 9, 33, 27, 34, 9, 12, 29, 24, 20, 27, 25, 14, 30, 37, 12, 13, 8, 8, 30, 6, 12, 23, 24, 26, 27, 18, 28, 10, 18, 11, 20, 30, 15, 17, 1, 8, 9, 3, 32, 24, 5, 23, 29, 1, 30, 5, 18, 3, 4, 30, 13, 11, 15, 7, 27, 37, 8, 7, 1, 35, 32, 23, 12, 28, 1, 24, 18, 26, 17, 17, 12, 5, 27, 27, 18, 8, 8, 37, 13, 33, 24, 15, 11, 34, 13, 22, 36, 12, 24, 7, 26, 23, 13, 35, 13, 2, 6, 12, 12, 4, 10, 1, 4, 4, 13, 4, 29, 13, 36, 5, 25, 11, 25, 15, 9, 34, 21, 13, 35, 36, 26, 22, 35, 20, 31, 25, 12, 4, 22, 30, 16, 30, 5, 26, 32, 20, 1, 17, 18, 36, 32, 10, 23, 34, 6, 37, 19, 4, 1, 37, 15, 22, 22, 31, 11, 37, 5, 32, 3, 20, 13, 20, 34, 22, 13, 22, 26, 1, 19, 5, 31, 29, 24, 16, 15, 37, 35, 14, 7, 18, 1, 37, 28, 3, 30, 37, 1, 29, 26, 16, 8, 33, 21, 19, 1, 21, 25, 20, 21, 24, 4, 31, 14, 20, 18, 24, 7, 29, 7, 23, 13, 23, 17, 33, 4, 37, 21, 24, 20, 21, 1, 8, 27, 6, 11, 37, 21, 13, 9, 22, 5, 1, 8, 5, 13, 8, 4, 16, 34, 11, 24, 25, 31, 36, 9, 13, 34, 35, 10, 12, 30, 18, 37, 10, 22, 25, 17, 17, 22, 36, 8, 16, 17, 29, 29, 3, 6, 8, 13, 10, 23, 35, 30, 27, 7, 10, 32, 33, 18, 12, 31, 32, 18, 34, 31, 14, 37, 25, 12, 12, 33, 6, 14, 19, 7, 25, 15, 12, 14, 28, 19, 1, 19, 28, 21, 25, 14, 18, 14, 3, 32, 4, 35, 17, 12, 14, 1, 9, 14, 9, 7, 21, 13, 11, 24, 31, 28, 17, 25, 1, 17, 7, 12, 7, 28, 35, 19, 19, 21, 16, 33, 13, 23, 28, 35, 36, 24, 28, 1, 16, 34, 25, 16, 3, 34, 25, 33, 2, 10, 18, 6, 8, 37, 22, 10, 24, 1, 10, 37, 3, 8, 17, 33, 20, 1, 10, 15, 1, 23, 7, 29, 21, 10, 2, 20, 5, 23, 16, 15, 30, 22, 34, 5, 23, 25, 2, 27, 33, 4, 37, 12, 12, 21, 23, 22, 37, 25, 3, 15, 23, 13, 16, 12, 29, 31, 24, 31, 30, 13, 27, 36, 35, 8, 8, 24, 30, 26, 34, 37, 8, 28, 10, 10, 14, 33, 5, 32, 19, 27, 37, 12, 9, 11, 14, 25, 26, 23, 22, 2, 9, 31, 32, 36, 29, 36, 23, 13, 28, 18, 22, 25, 23, 19, 34, 25, 31, 8, 25, 4, 34, 36, 24, 4, 26, 20, 33, 15, 26, 22, 23, 17, 34, 15, 21, 28, 14, 5, 26, 16, 31, 12, 36, 9, 7, 5, 23, 37, 13, 33, 20, 21, 20, 13, 30, 34, 14, 24, 8, 32, 26, 35, 19, 36, 22, 31, 12, 9, 26, 1, 6, 10, 27, 13, 5, 12, 35, 16, 11, 6, 37, 26, 32, 22, 32, 17, 23]

-- #check test_elab

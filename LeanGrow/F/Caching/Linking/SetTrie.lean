
import LeanGrow.F.Utils.SetTrie.Types

open Lean

inductive sSetTrie (α : Type _) (β : Type _)  where
| root (c : List (sSetTrie α β))
| node (q : β) (c : List (sSetTrie α β))
| leaf (a : α)
| pointer (_ : Nat)
| snode (p : Nat) (c : List (sSetTrie α β))
deriving Inhabited, Repr, BEq


partial def sSetTrie.depth (T : sSetTrie α β) : Nat :=
  let rec go (candidates : List Nat) (depth : Nat) : List (sSetTrie α β) → Nat
    | [] => depth
    | t :: ts =>
        match t with
        | .leaf _ | .pointer _ =>
            match candidates with
            | n :: more => go more (if n > depth then n else depth) ts
            | _ => 0
        | .root c | .node _ c | .snode _ c =>
            match candidates with
            | n :: more =>
                go ((List.replicate c.length (n+1)) ++ more) depth (c ++ ts)
            | _ => 0
  go [0] 0 [T]


namespace SetTrie

partial def stratify (T : SetTrie α β) (depth size : Nat) (measure : β → Nat) :
  sSetTrie α β × List (Nat × sSetTrie α β) × List (Nat × β) :=
    let rec inner (ct cb : Nat) (TS : List (sSetTrie α β)) (doneT : List (Nat × sSetTrie α β)) (doneB : List (Nat × β))
      (go : Nat → Nat → List (Nat × sSetTrie α β) → List (Nat × β) → SetTrie α β → Nat × Nat × sSetTrie α β × List (Nat × sSetTrie α β) × List (Nat × β)) :
      List (SetTrie α β) → Nat × Nat × List (sSetTrie α β) × List (Nat × sSetTrie α β) × List (Nat × β)
        | [] => (ct,cb,TS,doneT,doneB)
        | nx :: more =>
            let (nct,ncb,nT,ndoneT,ndoneB) := go ct cb doneT doneB nx
            inner nct ncb (nT :: TS) ndoneT ndoneB go more
    let rec go (ct cb : Nat) (doneT : List (Nat × sSetTrie α β)) (doneB : List (Nat × β)) :
      SetTrie α β → Nat × Nat × sSetTrie α β × List (Nat × sSetTrie α β) × List (Nat × β)
      | .leaf x => (ct,cb, .leaf x, doneT, doneB)
      | .root c =>
          let (nct,ncb,nTS,ndoneT,ndoneB) := inner ct cb [] doneT doneB go c
          (nct,ncb,(.root nTS),ndoneT,ndoneB)
      | .node b c =>
          let (nct,ncb,nTS,ndoneT,ndoneB) := inner ct cb [] doneT doneB go c
          if measure b < size
          then
            let NT := .node b nTS
            if NT.depth < depth
            then
              (nct,ncb,NT,ndoneT,ndoneB)
            else
              (nct+1,ncb,(.pointer nct),((nct, NT) :: ndoneT),ndoneB)
          else
            let NT := .snode ncb nTS
            if NT.depth < depth
            then
              (nct,ncb+1,NT,ndoneT,((ncb,b) :: ndoneB))
            else
              (nct+1,ncb+1,(.pointer nct),((nct, NT) :: ndoneT),((ncb,b) :: ndoneB))
    (go 0 0 [] [] T).2.2



import LeanGrow.F.Data.CExpr.Types
import Mathlib.Data.List.Sort
import LeanGrow.F.Utils.List

open Lean


-- # Sorting, for real

def SinksFirst_getSinkRest (raw : List (Nat × CExpr × Bool × List Nat)) : List (Nat × CExpr × Bool × List Nat) × List (Nat × CExpr × Bool × List Nat)  :=
  let R := fun a b : Nat × CExpr × Bool × List Nat => a.1 ≤ b.1
  let dummy := fun n => ⟨n, default, false, []⟩
  let rec go (candidates blacklist : List (Nat × CExpr × Bool × List Nat)) : List (Nat × CExpr × Bool × List Nat) → (List (Nat × CExpr × Bool × List Nat) × List (Nat × CExpr × Bool × List Nat))
  | [] => (candidates, blacklist)
  | node :: more =>
      let pass? := List.orderedContains R node blacklist
      let nb := node.2.2.2.foldl (fun s n => List.orderedInsertOrLeave R (dummy n) s) blacklist
      let nc := node.2.2.2.foldl (fun s n => List.orderedEraseOrLeave R (dummy n)  s) candidates
      if pass?
      then
        go nc nb more
      else
        go (node :: nc) nb more
  go [] [] raw


partial def SinksFirst (raw : List (Nat × CExpr × Bool × List Nat)) : List (Nat × CExpr × Bool × List Nat) :=
  let rec go (cache : List (List (Nat × CExpr × Bool × List Nat))) : List (Nat × CExpr × Bool × List Nat) → List (List (Nat × CExpr × Bool × List Nat))
  | [] => cache
  | raw =>
      let (layer, next) := SinksFirst_getSinkRest raw
      go (layer :: cache) next
  (go [] raw).reverse.join


def DAG_RawToFormat (raw : List (Nat × CExpr × Bool × List Nat)) (l_len : Nat) : (Array Nat) × Array EmbedData :=
  let perm : Array Nat := Array.mkEmpty l_len
  let data : Array EmbedData := Array.mkEmpty l_len
  (raw.foldl (fun (i,p,d) (idx, ce, inst?, pars) =>
    let np := p.set! i idx
    let nd := d.set! idx (if inst? then .inst ce pars.toArray else .nonInst ce pars.toArray)
    let ni := i+1
    (ni,np,nd)
    )
    (0,perm, data)).2

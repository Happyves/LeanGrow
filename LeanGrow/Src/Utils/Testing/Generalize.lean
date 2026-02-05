

/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import LeanGrow.Src.Utils.LeanGrow.TestTools
import LeanGrow.Src.Utils.Lean.Generalize


open Lean Meta



def testP (_ _ _ _ _ _ _ _ _ ews objs : Array Expr) (_ : Array DepCache) (_ : Array (FVarId × List FVarId)) : MetaM Unit := do
    let T := objs[0]!
    let .mk gt fact l1 l2 ← generalizeProofs (← getLCtx) (← getLocalInstances) T (ews.map Expr.fvarId!)
    withLCtx l1 l2 <| do
      IO.println s!"Reverted to:\n{(← ppExpr gt)}\nFactors:\n{← fact.mapM ppExpr}"
      IO.println s!"\n\nRaw revert : {repr gt}"

def testT (_ _ _ _ _ _ _ _ _ ews objs : Array Expr) (_ : Array DepCache) (_ : Array (FVarId × List FVarId)) : MetaM Unit := do
    let T := objs[0]!
    let .mk gt fact l1 l2 ← generalizeTnodesSafeIgnoring (← getLCtx) (← getLocalInstances) T (ews.map Expr.fvarId!) (fun _ _ _ => return false)
    withLCtx l1 l2 <| do
      match gt with
      | .none => IO.println "Has Type-typed tnodes"
      | .some gt =>
            IO.println s!"Reverted to:\n{(← ppExpr gt)}\nFactors:\n{← fact.mapM ppExpr}"
            IO.println s!"\n\nRaw revert : {repr gt}"

set_option pp.proofs true



With context g(l : List Nat) g(x : Nat) and objects (((x :: l).reverse).get  ⟨l.length, (by rw [List.length_reverse] ; dsimp ; exact Nat.lt.base (List.length l)) ⟩ = x) run testP

With context g(l : List Nat) u(x : Nat : 42) and objects (((x :: l).reverse).get  ⟨l.length, (by rw [List.length_reverse] ; dsimp ; exact Nat.lt.base (List.length l)) ⟩ = x) run testP

With context and objects (fun (l : List Nat) (x : Nat) => ((x :: l).reverse).get  ⟨l.length, (by rw [List.length_reverse] ; dsimp ; exact Nat.lt.base (List.length l)) ⟩ = x) run testP

With context and objects (fun (l : List Nat) => let x : Nat := 42 ;  ((x :: l).reverse).get  ⟨l.length, (by rw [List.length_reverse] ; dsimp ; exact Nat.lt.base (List.length l)) ⟩ = x) run testP

With context g(l : List Nat) g(x : Nat) g(h : l.length < l.length + 1) and objects (((x :: l).reverse).get  ⟨l.length, (by rw [List.length_reverse] ; dsimp ; exact h)⟩ = x) run testP

With context g(l : List Nat) g(x : Nat) and objects ((by exact List.getElem_cons_zero _ _ (by rw [List.length_cons] ; apply Nat.zero_lt_succ)) : ((x :: l).get ⟨0, (by rw [List.length_cons] ; apply Nat.zero_lt_succ)⟩ = x)) run testP

With context g(l : List Nat) u(x : Nat : 42) and objects ((by exact List.getElem_cons_zero _ _ (by rw [List.length_cons] ; apply Nat.zero_lt_succ)) : ((x :: l).get ⟨0, (by rw [List.length_cons] ; apply Nat.zero_lt_succ)⟩ = x)) run testP

With context  and objects (fun (l : List Nat) (x : Nat) => ((by exact List.getElem_cons_zero _ _ (by rw [List.length_cons] ; apply Nat.zero_lt_succ)) : ((x :: l).get ⟨0, (by rw [List.length_cons] ; apply Nat.zero_lt_succ)⟩ = x))) run testP






With context g(l : List Nat) g(x : Nat) and objects (((x :: l).reverse).get  ⟨l.length, (by rw [List.length_reverse] ; dsimp ; exact Nat.lt.base (List.length l)) ⟩ = x) run testT

With context g(l : List Nat) u(x : Nat : 42) and objects (((x :: l).reverse).get  ⟨l.length, (by rw [List.length_reverse] ; dsimp ; exact Nat.lt.base (List.length l)) ⟩ = x) run testT

With context and objects (fun (l : List Nat) (x : Nat) => ((x :: l).reverse).get  ⟨l.length, (by rw [List.length_reverse] ; dsimp ; exact Nat.lt.base (List.length l)) ⟩ = x) run testT

With context and objects (fun (l : List Nat) => let x : Nat := 42 ;  ((x :: l).reverse).get  ⟨l.length, (by rw [List.length_reverse] ; dsimp ; exact Nat.lt.base (List.length l)) ⟩ = x) run testT

With context g(l : List Nat) g(x : Nat) g(h : l.length < l.length + 1) and objects (((x :: l).reverse).get  ⟨l.length, (by rw [List.length_reverse] ; dsimp ; exact h)⟩ = x) run testT

With context g(l : List Nat) g(x : Nat) and objects ((by exact List.getElem_cons_zero _ _ (by rw [List.length_cons] ; apply Nat.zero_lt_succ)) : ((x :: l).get ⟨0, (by rw [List.length_cons] ; apply Nat.zero_lt_succ)⟩ = x)) run testT

With context g(l : List Nat) u(x : Nat : 42) and objects ((by exact List.getElem_cons_zero _ _ (by rw [List.length_cons] ; apply Nat.zero_lt_succ)) : ((x :: l).get ⟨0, (by rw [List.length_cons] ; apply Nat.zero_lt_succ)⟩ = x)) run testT

With context  and objects (fun (l : List Nat) (x : Nat) => ((by exact List.getElem_cons_zero _ _ (by rw [List.length_cons] ; apply Nat.zero_lt_succ)) : ((x :: l).get ⟨0, (by rw [List.length_cons] ; apply Nat.zero_lt_succ)⟩ = x))) run testT


With context g(l : List Nat) t(0 : 0 : x : Nat) and objects (((x :: l).reverse).get  ⟨l.length, (by rw [List.length_reverse] ; dsimp ; exact Nat.lt.base (List.length l)) ⟩ = x) run testT

With context g(l : List Nat) g(x : Nat) t(0 : 0 : h : l.length < l.length + 1) and objects (((x :: l).reverse).get  ⟨l.length, (by rw [List.length_reverse] ; dsimp ; exact h)⟩ = x) run testT

With context g(l : List Nat) g(x : Nat) t(0 : 0 : h : ∀ l : List Nat, l.length < l.length + 1) and objects (fun (l : List Nat) (x : Nat) => ((x :: l).reverse).get  ⟨l.length, (by rw [List.length_reverse] ; dsimp ; exact h l)⟩ = x) run testT


With context g(l : List Nat) wg(true : 0 : x : Nat) and objects (((x :: l).reverse).get  ⟨l.length, (by rw [List.length_reverse] ; dsimp ; exact Nat.lt.base (List.length l)) ⟩ = x) run testT

With context g(n : Nat) g(P : Nat → Type) and objects (P (⟨0, Nat.zero_lt_succ n⟩ : Fin (n+1)).val) run testT

-- tracing_mode .std
-- tracing_flags [(`generalizeProofsIgnoringMain, TracingFlags.all)]

With context g(P : Nat → Type) and objects (fun n : Nat => P (⟨0, Nat.zero_lt_succ n⟩ : Fin (n+1)).val) run testT

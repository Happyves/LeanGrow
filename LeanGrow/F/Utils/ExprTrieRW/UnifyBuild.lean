
import LeanGrow.F.Utils.ExprTrieRW.Unify

open Lean

/-- should be used to build lnode matches, so that we can propagate ;
Recall that this builds the type, not the term of that type.
-/
partial def rwExpr.toCExpr (rww : rwExpr α) : CExpr :=
  let rec go : List (rwExpr α) → List CExpr
    | [] => []
    | nx :: more =>
        match nx with
        | .ofAtom ce => ce :: (go more)
        | .wRW _ _ _ ce => go (ce :: more)
        | .app f a =>
            let r := go (f :: a :: more)
            let (F,r2) := List.headD_tail r .failed
            let (A,r3) := List.headD_tail r2 .failed
            (.app F A) :: r3
        | .lam n f a i =>
            let r := go (f :: a :: more)
            let (F,r2) := List.headD_tail r .failed
            let (A,r3) := List.headD_tail r2 .failed
            (.lam n F A i) :: r3
        | .forallE n f a i =>
            let r := go (f :: a :: more)
            let (F,r2) := List.headD_tail r .failed
            let (A,r3) := List.headD_tail r2 .failed
            (.forallE n F A i) :: r3
        | .letE n f a z i =>
            let r := go (f :: a :: z :: more)
            let (F,r2) := List.headD_tail r .failed
            let (A,r3) := List.headD_tail r2 .failed
            let (Z,r4) := List.headD_tail r3 .failed
            (.letE n F A Z i) :: r4
        | .proj n i f =>
            let r := go (f :: more)
            let (F,r2) := List.headD_tail r .failed
            (.proj n i F) :: r2
  List.headD (go [rww]) .failed


import LeanGrow.F.Utils.ExprTrieRW.Query

open Lean

-- build expression with recursors from
#check RWblueprint


#check Eq.rec
#check Eq.ndrec


def CExpr.factor (on : CExpr) (dirs : List rwDirs) : CExpr :=
  let rec go (depth : Nat) : CExpr → List rwDirs → CExpr
    | .lam n t b i , d :: more =>
          match d with
          | .left => .lam n (go depth t more) b i
          | .right => .lam n t (go (depth+1) b more) i
          | _ => .failed
    | .forallE n t b i , d :: more =>
          match d with
          | .left => .forallE n (go depth t more) b i
          | .right => .forallE n t (go (depth+1) b more) i
          | _ => .failed
    | .letE n t v b i  , d :: more=>
          match d with
          | .left => .letE n (go depth t more) v b i
          | .mid => .letE n t (go depth v more) b i
          | .right => .letE n t v (go (depth+1) b more) i
    | .app l r, d :: more =>
        match d with
          | .left => .app (go depth l more) r
          | .right => .app l (go depth r more)
          | _ => .failed
    | .proj n i e, d :: more =>
        match d with
          | .left => .proj n i (go depth e more)
          | _ => .failed
    | _, _ :: _  => .failed
    | _, [] => .bvar depth
  .lam `LenGrow.EqFacto (.failed) (go 0 on dirs) .default
                        -- we really need mvars here, or the type of what we rewrite...

/-
Alternatively, when we generate the Eq-thms-cache-thing for rewrites, we can take note of the type
in the rw theorem ; the type should have to get filled out when embedding the epxression-thm-thing
we'll then use this type for the motive and Eq.ndrec (the α)
-/

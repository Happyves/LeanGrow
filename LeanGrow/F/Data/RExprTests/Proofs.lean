
import LeanGrow.F.Data.RExprTests.API
import  LeanGrow.F.Data.CExpr.Types

open Lean


#check Eq.rec

#check fun n : Nat => Eq.refl n

#check fun n : 2+2=4 => n

#check fun n : Unit → 2+2=4 => n ()
#check (Unit → 2 + 2 = 4) → 2 + 2 = 4

#check let p : 2+2=4 := rfl ; p

/-
To check if a term is a proof, without using inferType, we could:
- for applications, get head, check that it's type is an forall with a Prop head
- lams are if there body is ; we should also check if the binder is a Prop
  (function app with const at head who's type is Prop.headed ; forall with a Prop head)
  so that we get corect answer in `fun n : 2+2=4 => n`
  Similar situation for let ?
- forall aren't terms
- for lnodes and gnodes, we'll need a context...

-/

#check Meta.inferType

#check ReaderT.run (pure () : MetaM Unit) {}
#check Meta.Context
#reduce ReaderT.run (pure () : MetaM Unit) {}

/-- Assumes reduced input -/
def Expr.naiveIsPropHeaded (e : Expr) : Bool :=
  let rec go (bvarIsProp : List Bool) : Expr → Bool
    | .bvar i =>
            match bvarIsProp.get? i with
            | .some b => b
            | _ => false
    | .sort u => u == .zero
    | .app f _ => go bvarIsProp f
    | .forallE _ t b _ =>
            let is? := go bvarIsProp t
            go (is? :: bvarIsProp) b
    | .letE _ t _ b _ =>
            let is? := go bvarIsProp t
            go (is? :: bvarIsProp) b
    | .mdata _ e => go bvarIsProp e
    | _ => false
  go [] e



def RExpr.naiveIsPropHeaded (env : Environment) (re : RExpr) (LNodeIsProp : List (Option Nat × Nat))
  (GNodeIsProp : List (Nat)) : Bool :=
    let rec go (bvarIsProp : List Bool) : RExpr → Bool
      | .lnode idx t =>
            match LNodeIsProp.find? (fun x => x.1 == t && x.2 == idx) with
            | .some _ => true
            | _ => false
      | .gnode idx => GNodeIsProp.contains idx
      | .bvar i =>
            match bvarIsProp.get? i with
            | .some b => b
            | _ => false
      | .forallE _ t b _ =>
            let is? := go bvarIsProp t
            go (is? :: bvarIsProp) b
      | .letE _ t _ b _ =>
            let is? := go bvarIsProp t
            go (is? :: bvarIsProp) b
      | .app f _ => go bvarIsProp f
      | .sort u => u == .zero
      | .axm n _ =>
            match env.find? n with
            | .none => false
            | .some v =>  Expr.naiveIsPropHeaded v.type



    sorry

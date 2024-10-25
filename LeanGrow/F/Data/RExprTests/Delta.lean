
import LeanGrow.F.Data.RExprTests.API
import  LeanGrow.F.Data.CExpr.Types

open Lean



partial def deAbbrev (env : Environment) (n : Name) (lvl : List Level) : Expr :=
  let rec go (m : Name) (l : List Level) : Expr :=
    match env.find? m  with
    | .some (.defnInfo I) =>
        match I.value with
        | .const M L =>  go M L
        | _ => .const m l
    | _ => .const  m l
  go n lvl



inductive splitConstType where
| missing
| ofPass (r : RExpr)
| ofPost (r : RecursorVal)

-- assumes `deAbbrev` occured
def splitConst (env : Environment) (n : Name) (lvl : List Level) : splitConstType :=
  match env.find? n with
  | .some (.defnInfo I) | .some (.thmInfo I) | .some (.opaqueInfo I) =>
        match I.type with
        | .forallE _ _ _ _ => -- not up to reduction :(
              .ofPass (.deltaFun n lvl)
        | _ => .ofPass (.deltaDef n lvl)
  | .some (.axiomInfo _) => .ofPass (.axm n lvl)
  | .some (.ctorInfo v) => .ofPass (.ctor n v lvl)
  | .some (.inductInfo v) => .ofPass (.indt n v lvl)
  | .some (.quotInfo v) => .ofPass (.quo n v lvl)
  | .some (.recInfo v) => .ofPost v
  | .none => .missing


import Lean

open Lean Meta


#check etaExpand



/-- function head f so that f target = body

It's overkill as we don't expect out of bounds bvars in ltx ?? -/
def targeted_eta (target body : Expr) : Expr :=
  let rec shift (d : Nat) : Expr → Expr
    | .bvar i => if i ≥ d then .bvar (i+1) else .bvar i
    | .app l r => .app (shift d l) (shift d r)
    | .lam n l r B => .lam n (shift d l) (shift (d+1) r) B
    | .forallE n l r B => .forallE n (shift d l) (shift (d+1) r) B
    | .mdata _ e => shift d e
    | .proj n i e => .proj n i (shift d e)
    | x => x
  let rec go (d : Nat) : Expr → Expr :=
    fun t =>
      if t == target
      then .bvar d
      else
        match t with
        | .app l r => .app (go d l) (go d r)
        | .lam n l r B => .lam n (go d l) (go (d+1) r) B
        | .forallE n l r B => .forallE n (go d l) (go (d+1) r) B
        | .mdata _ e => go d e
        | .proj n i e => .proj n i (go d e)
        | x => x
  go 0 (shift 0 body)


-- ↑ should be used in ↓, but redoing from scratch is probably easier that dealing with the undocumented maze that is this implementation
#check Lean.Elab.Tactic.evalInduction

elab "isItInductive?" n:name : command =>
  match (Lean.Syntax.isNameLit? n.raw) with
  | none => throwError s!"Error : please enter the correct name of a type to search theorems in."
  | some N => do
      let env ← getEnv
      match env.constants.find? N with
      | .none => throwError "Unknown constant"
      | .some info => do
          IO.println s!"Is it inductive : {info.isInductive}"

isItInductive? `Nat


open Elab Tactic


#check ConstantInfo

elab "try_induciton" : tactic => do
  let env ← getEnv
  let ref ← getRef
  let ltx ← getLCtx
  let g ← getMainTarget
  for f in ltx.getFVars do
    let tf ← withMainContext (inferType f)
    match tf with
    | .const n _ =>
          match env.constants.find? n with
          | .some (.inductInfo _) => do
              let head := targeted_eta f g
              let sc ← isDefEq g (.app (.lam `stuff tf head .default) f)
              logInfoAt ref s!"For {← ppExpr (.app (.lam `stuff tf head .default) f)}\nSanity check {sc}"
          | _ => pure ()
    | _ => pure ()



example (n : Nat) : n + n = 2*n := by
  try_induciton
  sorry

example (n m : Nat) : n + n = 2*n := by
  try_induciton
  sorry

example (n : Nat) : 2 + 2 = 42 := by
  try_induciton
  sorry

example (n : Nat) (h : n = 3) (f : Nat → Nat): n + n = 2*n := by
  try_induciton
  sorry

example (b : Bool) :  2 + 2 = 42 := by
  try_induciton
  sorry

example :  2 + 2 = 42 := by
  try_induciton
  sorry

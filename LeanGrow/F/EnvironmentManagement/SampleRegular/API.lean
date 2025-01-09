
import Lean
import LeanGrow.F.EnvironmentManagement.SampleRegular.Types
import Init.Data.Array.Basic

open Lean Meta


#check LocalContext.decls
#check PersistentArray.foldl
#check LocalDecl.fvarId

def Array.reduceOption (a : Array (Option α)) : Array α := Array.filterMap id a -- versioning


def translateForSample (dict : List (FVarId × Nat)) (e : Expr) : CExpr :=
  let rec go : Expr → CExpr -- optimize
    | .app f a => .app (go f) (go a)
    | .lam n f a i => .lam n (go f) (go a) i
    | .forallE n f a i => .forallE n (go f) (go a) i
    | .letE n f a z i => .letE n (go f) (go a) (go z) i
    | .proj n i f => .proj n i (go f)
    | .mdata _ f => (go f)
    | .fvar id =>
        match dict.find? (fun x => x.1 == id) with
        | .some (_,mid) => .lnode mid (.ofFvar id) .none
        | .none => .failed
    | .bvar i => .bvar i
    | .mvar _ => .failed
    | .lit l => .lit l
    | .const n l => .const n l
    | .sort u => .sort u
  go e


elab "test" : tactic => Lean.Elab.Tactic.withMainContext do
  let ref ← getRef
  let ltx ← getLCtx
  let cleaned ← (ltx.decls.toArray.reduceOption.mapM (fun x => do let t ← ppExpr x.type ; return (x.fvarId, Std.Format.pretty t)))
  logInfoAt ref (repr cleaned)


example (n : Nat) (h : n + n = 42) : n = n - 1 := by
  let m := 37
  have : n = 37 := sorry
  test
  sorry -- hence we can assume in translateLocalContext that order makes sense


def translateLocalContext (ltx : LocalContext) (goal : Expr) : CExpr × List (Nat × CExpr) :=
  let Ltx := ltx.decls.toArray.reduceOption
  let (dict, mltx) := (Array.range (Ltx.size - 1)).foldl
    (fun (d,l) i =>
      let decl := Ltx.get! (i.succ)
      let T := translateForSample d decl.type
      ((decl.fvarId, i) :: d, (i,T) :: l)
      )
    ([],[])
  let G := translateForSample dict goal
  (G,mltx)


elab "test_2" : tactic => Lean.Elab.Tactic.withMainContext do
  let ref ← getRef
  let ltx ← getLCtx
  let goal ← Elab.Tactic.getMainTarget
  let done := translateLocalContext ltx goal
  logInfoAt ref (repr done)

example (n : Nat) (h : n + n = 42) : n = n - 1 := by
  test_2
  sorry




def getRelevantArgsWTypes (proof : Expr) : MetaM (List Expr × List Expr) :=
  match proof with
  | .app _ _ => do
    let as := proof.getAppArgs
    let mut L := []
    let mut Ts := []
    for e in as do
      match e with
      | .fvar _ => continue
      | _ =>
        let T ← inferType e
        let TT ← inferType T
        if TT.isProp
        then
          L := e :: L
          Ts := T :: Ts
    return (L,Ts)
  | _ => return ([],[])

def getRelevantArgsOTypes (as : Array Expr) : MetaM (List Expr) := do
    let mut Ts := []
    for e in as do
      let T ← inferType e
      let TT ← inferType T
      if TT.isProp
      then
        Ts := T :: Ts
    return (Ts)

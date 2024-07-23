
import Lean
import Mathlib

open Lean Meta


#check etaExpand



/-- function head f so that f target = body -/
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
          match info with
          | .inductInfo i => IO.println s!"Ctors : {i.ctors}"
          | _ => pure ()

isItInductive? `List



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
    | .const n _ => -- actally, consider constant head (ex: Lists)
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

#check List.rec

inductive test (a  b : Nat) : Int → Type where
| fst (h : a = 2) : test a b 3
| snd (n : Int) : test a b (n+1)

#check test.rec

def Lean.ConstantInfo.isRecInfo : ConstantInfo → Bool
| .recInfo _ => true
| _ => false

#eval (do let env ← getEnv ; match env.constants.find? `test with | .some info => IO.println (info.levelParams) | _ => pure () : CoreM Unit)
#eval (do let env ← getEnv ; match env.constants.find? `List with | .some info => IO.println (info.levelParams) | _ => pure () : CoreM Unit)
#eval (do let env ← getEnv ; match env.constants.find? `test.rec with | .some info => IO.println (info.levelParams) | _ => pure () : CoreM Unit)
#eval (do let env ← getEnv ; match env.constants.find? `List.rec with | .some info => IO.println s!"{info.isRecInfo} {(info.levelParams)}" | _ => pure () : CoreM Unit)
#eval (do let env ← getEnv ; match env.constants.find? `Nat.rec with | .some info => IO.println s!"{info.isRecInfo} {(info.levelParams)}" | _ => pure () : CoreM Unit)



structure data_of_processed_type where
  envdata : InductiveVal
  params : List Expr
  indices : List Expr
deriving Inhabited

def process_type_of_ind_arg (Typ : Expr) : MetaM (Option (data_of_processed_type)) := do
  let env ← getEnv
  let (hn, args):= Expr.getAppFnArgs Typ
  match env.constants.find? hn with
  | .some (.inductInfo info) => do
      let largs := args.toList
      let ps := largs.take info.numParams
      let is := largs.take info.numIndices
      return .some ⟨info, ps, is⟩
  | _ => pure .none

def factor_eta (targets : List Expr) (body : Expr) : Expr :=
  let rt := targets.reverse
  let rec go (b : Expr) : List Expr → Expr
    | [] => b
    | x :: l =>
        let step := targeted_eta x b
        go step l
  go body rt

def wrap_factor_eta (targets : List Expr) (body : Expr) : MetaM Expr :=
  let inner := factor_eta targets body
  let rec mkLam (t : List Expr) (b : Expr) : MetaM Expr :=
    match t with
    | [] => do return b
    | x :: l => do return (.lam `wfe (← (inferType x)) (← mkLam l b) .default)
  mkLam targets inner


def myGetHyps (ty : Expr) (upto : Nat): (List (Expr)) :=
  if upto > 0
  then
    match ty with
    | .forallE _ h b _ => h :: (myGetHyps b (upto-1))
    | .mdata  _ e => myGetHyps e (upto-1)
    | _ => []
  else []

elab "TryInduction" : tactic => withMainContext do
  let env ← getEnv
  let ltx ← getLCtx
  let g ← getMainTarget
  for f in ltx.getFVars do
    let tf ←  (inferType f)
    let .some dtf ← process_type_of_ind_arg tf | continue
    --dbg_trace s!"{dtf.params ++ dtf.indices}"
    let mot ←  wrap_factor_eta (dtf.indices ++ [f]) g
    let ntf := tf.getAppFn.constName
    let .some recu := env.constants.find? (Name.str ntf "rec") | continue
    let parTyp ← (inferType (.app (mkAppN (.const recu.name [0]) dtf.params.toArray) mot))
    let steps := (myGetHyps parTyp (dtf.envdata.numCtors))
    --dbg_trace s!"{steps}"
    let newGoals := (← steps.foldlM (fun l t => do let m ← mkFreshExprMVar (.some (t)) ; return m :: l) []).reverse
    liftMetaTactic fun mvarId => do
      mvarId.assign (mkAppN (.const recu.name [0]) (dtf.params ++ [mot] ++ newGoals ++ dtf.indices ++ [f]).toArray)
      --dbg_trace s!"test {← ppExpr (mkAppN (.const recu.name [0]) (dtf.params ++ [mot] ++ newGoals ++ dtf.indices ++ [f]).toArray)}"
      return (newGoals.map Expr.mvarId!)
    break

--#exit

#check Nat.rec

#check @Nat.rec (fun n =>  n + n = 2*n)


--set_option trace.Kernel true
--set_option pp.all true

universe u --u_1

lemma test1 (n : Nat) : n + n = 2*n := by
  TryInduction
  · rfl
  · intro m mdef
    rw [two_mul]

--#print test1

example : ∀ n, n + n = 2*n := by
  intro n
  TryInduction
  · clear n ; rfl
  · clear n
    intro m mdef
    rw [two_mul]

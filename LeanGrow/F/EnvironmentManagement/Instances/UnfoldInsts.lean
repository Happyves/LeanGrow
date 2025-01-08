
import Lean


#check Lean.Meta.isInstanceCore

#check Nat.instCommutativeGcd

open Lean

elab "test_1" : command => do
  let env ← getEnv
  IO.println (Meta.isInstanceCore env `Nat.instDiv)
  IO.println (env.constants.find! `Nat.instDiv).value?
  IO.println (env.constants.find! `Div.div).value?

test_1

#check Nat.instDiv

#reduce Nat.instDiv

set_option pp.all true in
#check Nat.instDiv.div

#reduce Nat.instDiv.div

set_option pp.all true in
#check 1+1

#reduce @Div.div
#reduce @HAdd.hAdd


#check Expr.headBeta


def Lean.Expr.getLamBody : Expr → Expr
| .lam _ _ b _ => b.getLamBody
| e => e


private partial def main (env : Environment) (e : Expr) : Expr :=
  let rec argsHaveInst (as : Array Expr) : Nat → Bool
    | 0 => false
    | n+1 =>
        match (as.get! n).getAppFn with
        | .const N _ =>
            if Meta.isInstanceCore env N
            then true
            else argsHaveInst as n
        | _ => argsHaveInst as n
  --dbg_trace s!"Call on {e}"
  match e with
  | .app _ _=>
      let args := e.getAppArgs
      if argsHaveInst args args.size
      then
        let h := e.getAppFn
        match h with
        | .const n _ =>
            match (env.constants.find! n).value? with
            | .none => e
            | .some V =>
                match V.getLamBody with
                | .proj _ _ _ =>
                    let btd := (Lean.mkAppN V args).headBeta
                    match btd with
                    | .proj _ ind B =>
                        let (H,AS) := (main env B).getAppFnArgs
                        match env.find? H with
                        | .some (.ctorInfo ctorval) =>
                            let idx := ctorval.numParams + ind
                            AS.get! idx
                        | _ => e
                    | _ => e
                | _ => e
        | _ => e
      else
        e
  | _ => e


#check List.instAppend

#check mkAppRev


partial def Lean.Expr.unfoldInstances  (env : Environment) (e : Expr) : Expr :=
  let rec go (e : Expr) : Expr :=
    match e with
    | .app f a => main env (.app (go f) (go a))
    | .lam n f a i => .lam n (go f) (go a) i
    | .forallE n f a i => .forallE n (go f) (go a) i
    | .letE n f a z i => .letE n (go f) (go a) (go z) i
    | .proj n i f => .proj n i (go f)
    | .mdata d f => .mdata d (go f)
    | x => x
  go e

open Elab Term

elab "test_2" t:term : command => do
  let on ← Command.liftTermElabM (elabTermAndSynthesize t .none)
  let env ← getEnv
  let red := on.unfoldInstances env
  IO.println (← Command.liftTermElabM ( Meta.ppExpr red))
  IO.println red

-- test_2 ((fun _ : Unit => [1] ++ [2]) ())

#reduce @instHAdd

test_2 ((fun _ : Unit => 1 + 1) ())

#check instAddNat

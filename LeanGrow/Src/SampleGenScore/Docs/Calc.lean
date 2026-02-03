
import Lean
import Mathlib.Algebra.Ring.Int.Defs
open Lean

#check Lean.Elab.Tactic.evalCalc
-- just seems to wrap steps in
#check Trans.trans


#synth Trans Eq Nat.le Nat.le
#check instTransEq Nat.le
#print instTransEq

#synth Trans (fun x y : Nat => x ≤ y) (fun x y : Nat => x < y) (fun x y : Nat => x < y)
#print Nat.instTransLeLt
#check Nat.lt_of_le_of_lt


theorem test (a b c : Int) : (a + b)^2 + c = a^2 + b^2 + c + 2*a*b := by
  calc
    (a + b)^2 + c = a^2 + 2*a*b + b^2 + c := by
      rw [@add_sq Int]
    _ = a^2 + b^2 + c + 2*b*a := by sorry
    _ = a^2 + b^2 + c + 2*a*b := by sorry


#print test


partial def deClacifyEqs (oldproof : Expr) : MetaM Expr := do
  let (h,as) := oldproof.getAppFnArgs
  if h != ``Trans.trans
  then
    dbg_trace "nope 1"
    return oldproof
  else
    match as[4]!.getAppFn' with
    | .const e? _ =>
        if e? != ``Eq
        then
          dbg_trace "nope 2"
          return oldproof
        else
          let eqP := as[11]!
          let sofar ← deClacifyEqs as[10]!
          let motive := Expr.lam `mot as[1]! (.app (.app as[3]! as[7]!) (.bvar 0)) .default
          Meta.mkEqNDRec motive sofar (← Meta.mkEqSymm eqP)
    | x =>
        dbg_trace s!"nope 3 : {x}"
        return oldproof

#check Eq.ndrec
#check Meta.mkEqNDRec
#check Meta.mkEqSymm


def testDeCalc (n : Name) : MetaM Expr := do
  let .some dec := (← getEnv).find?  n | throwError s!"aaahhh 1"
  Meta.lambdaLetTelescope dec.value! <| fun fvs main => do
    let res ← deClacifyEqs main
    Meta.mkLambdaFVars fvs res

#eval (do Meta.ppExpr <| ← testDeCalc `test : MetaM _)


example (a b c : Int) : (a + b)^2 + c = a^2 + b^2 + c + 2*a*b :=
  Eq.symm (sorry : a ^ 2 + b ^ 2 + c + 2 * b * a = a ^ 2 + b ^ 2 + c + 2 * a * b) ▸
    Eq.symm (sorry : a ^ 2 + 2 * a * b + b ^ 2 + c = a ^ 2 + b ^ 2 + c + 2 * b * a) ▸
      Eq.mpr (id (congrArg (fun _a ↦ _a + c = a ^ 2 + 2 * a * b + b ^ 2 + c) (add_sq a b)))
        (Eq.refl (a ^ 2 + 2 * a * b + b ^ 2 + c))

#check 1

/-
Above isn't really usefull for grow and delab in general, or is it ?
Because we then have to delab the Eq.ndrec's ...
But it illustartes the main idea:
if the calc is about eqs only, we can turn it into a proof in which
the lhs gets successivly rwed, usin the proofs  from the calc steps
-/


#check @Trans.trans ℤ ℤ ℤ Eq Eq Eq (instTransEq Eq)
#reduce (types := true) @Trans.trans ℤ ℤ ℤ Eq Eq Eq (instTransEq Eq)
#print instTransEq


#synth Trans (fun x y : Nat => x = y) (fun x y : Nat => x < y) (fun x y : Nat => x < y)

#synth Trans (fun x y : Nat => x < y) (fun x y : Nat => x = y) (fun x y : Nat => x < y)

#print instTransEq_1

#synth Trans (fun x y : Nat => x < y) (fun x y : Nat => x ≤ y) (fun x y : Nat => x < y)

#print Nat.instTransLtLe

#synth Trans (fun x y : Nat => x ≤ y) (fun x y : Nat => x ≤ y) (fun x y : Nat => x ≤ y)


#print Nat.instTransLe


-- #synth Trans (fun x y : Nat => x ≍ y) (fun x y : Nat => x ≍ y) (fun x y : Nat => x ≍ y)

#print String.instTransOrd
#print instTransIff

#synth Trans (fun x y : String => x ≤ y) (fun x y : String => x ≤ y) (fun x y : String => x ≤ y)

#print Std.instTransLeOfIsPreorder

def testRed_1 :=
  @Trans.trans _ _ _
    (fun x y : Nat => x < y) (fun x y : Nat => x ≤ y) (fun x y : Nat => x < y)
    Nat.instTransLtLe

def testRed_2 :=
  @Trans.trans _ _ _
    (fun x y : String => x ≤ y) (fun x y : String => x ≤ y) (fun x y : String => x ≤ y)
    Std.instTransLeOfIsPreorder

def testRed (n : Name) : MetaM Unit := do
  let .some info := (← getEnv).find? n | throwError "aah"
  let V ← Meta.whnfI info.value!
  IO.println (← Meta.ppExpr V)


#eval testRed `testRed_1

#eval testRed `testRed_2


#print instTransEq

#print instTransEq_1

#synth Trans (fun x y : Nat => x = y) (fun x y : Nat => x = y) (fun x y : Nat => x = y)

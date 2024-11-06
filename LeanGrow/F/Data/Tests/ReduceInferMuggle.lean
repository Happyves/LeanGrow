
import LeanGrow.F.Data.CExpr.ReduceInferMuggle.Control

open Lean Elab Term


def NatInfo : CstInfo := .noVal [] (.sort 1)
def NatZeroInfo : CstInfo := .noVal [] (.const `Nat [])
def NatSuccInfo : CstInfo := .noVal [] (.forallE `x (.const `Nat []) (.const `Nat []) .default)


#check Nat.rec


def fackCstData : CTrie CstInfo := CTrie.ofList
  [("Nat", NatInfo), ("Nat.zero", NatZeroInfo), ("Nat.succ", NatSuccInfo)]

def fakeFixCtx : FixCtx where
  gnodeTypes := []
  gnodeTypesHandler := fun _ => (0,0)
  ltxTypes := []
  current := .none
  cstData := fackCstData


elab "testReduce" t:term : command => do
  let exp ← Command.liftTermElabM (elabTermAndSynthesize t .none)
  let cexp := exp.toCExprF
  let red := CExpr.whnf fakeFixCtx cexp
  IO.println s!"{repr red}"


testReduce (fun x => x) Nat.zero
testReduce (fun x => x) ((fun x => x) Nat.zero)
testReduce (fun x => (fun y => y) x) Nat.zero


testReduce let a := (fun x => x) ; let b := Nat.zero ; a b


elab "testReduceRef" t:term : command => do
  let exp ← Command.liftTermElabM (elabTermAndSynthesize t .none)
  let red ← Command.liftTermElabM (Meta.whnf exp)
  IO.println s!"{repr red}"

testReduceRef (fun x => x) ((fun x => x) Nat.zero)
testReduceRef (fun x => (fun y => y) x) Nat.zero



elab "testInfer" t:term : command => do
  let exp ← Command.liftTermElabM (elabTermAndSynthesize t .none)
  let cexp := exp.toCExprF
  let red := CExpr.inferType fakeFixCtx cexp
  IO.println s!"{repr red}"

testInfer (fun x => x) Nat.zero
testInfer Nat.succ Nat.zero

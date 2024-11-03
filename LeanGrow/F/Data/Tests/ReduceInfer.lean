
import LeanGrow.F.Data.CExpr.ReduceInfer


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
  let red := cexprWhnf fakeFixCtx [] cexp
  IO.println s!"{repr red}"


-- testReduce (fun x => x) Nat.zero

--#eval myTestExternExport
-- seeems to be problem about the extern-export thing


import LeanGrow.Src.SampleGenScore.Gen.TestTools_SampleGen


#check generalizePaInCore

def generalizePaInCoreS
  (l1 : Lean.LocalContext) (l2 : Lean.LocalInstances)
  (genCondition : Nat → Nat → Array Nat → Lean.Expr → Nat → Bool) (freqCondition : Nat → Nat → Array Nat → Nat → Bool)
  (sampleName : Lean.Name) (T : PaIn UInt32Array) (weights : Array Nat) (types : Array Lean.Expr) :=
    @generalizePaInCore
      UInt32Array _  (fun is i f => is.foldl i (fun i s => f i.toNat s)) UInt32Array.empty
      UInt32Array.union UInt32Array.inter UInt32Array.union UInt32Array.diff UInt32Array.isEmpty
      l1 l2 genCondition freqCondition sampleName T weights types

#check 1

open Lean Meta

def testGen (genCondition : Nat → Nat → Array Nat → Lean.Expr → Nat → Bool) (freqCondition : Nat → Nat → Array Nat → Nat → Bool)
  (sampleName : Lean.Name) : Array Expr → Array Expr → MetaM Unit
  | Gnodes, Objs => do
      let mut L := []
      let mut i := 0
      for O in Objs do
        L := (i,O) :: L
        i := i+1
      let ⟨T,l1,l2⟩ ← PaIn.ofList (← getLCtx) (← getLocalInstances) L .dead UInt32Array.empty (fun x => UInt32Array.single x.toUInt32)
        (fun x y => UInt32Array.oInsert y x.toUInt32)
      let .mk _ res types l1 l2 ← generalizePaInCoreS
        l1 l2 genCondition freqCondition sampleName T (Array.replicate i 1) #[]
      withReader (fun ctx => {ctx with lctx := l1, localInstances := l2}) do
        let built := (← res.buildCore l1 l2 [] 0 id UInt32Array.inter UInt32Array.isEmpty).toListOfProd
        let built := ← built.mapM (fun (x,y) => return (← ppExpr x, y))
        IO.println s!"Context: {← types.mapM ppExpr}\n"
        IO.println s!"Result: {built}"

#check 1

declare_syntax_cat lg_lam_let

syntax "("ident ":" term")" : lg_lam_let

open Lean Meta Elab Term Command

@[inline, specialize]
def elabAndLoad (i : Nat) (is : Name) (ts : Syntax) {α : Sort _} (k : Expr → Expr → TermElabM α) : TermElabM α := do
  let todo := ts
  let term ← elabTermAndSynthesize todo .none
  let name := is
  let ltx ← getLCtx
  let linst ← getLocalInstances
  let ltx := ltx.addDecl (.cdecl i ⟨name⟩ name term .default .default)
  let linst ← (do
    if let some c ← isClass? term
    then
      return linst.push { className := c, fvar := (.fvar ⟨name⟩) }
    else
      return linst)
  let mv ← mkMvarStdIndexNoCoE name term 0
  withLCtx ltx linst do
    k term mv



def elabForTest (i : Nat) (cs : TSyntaxArray `lg_lam_let) (doneT doneFv : Array Expr)
  {α : Sort _} (k : Array Expr → Array Expr → TermElabM α) : TermElabM α := do
    if i < cs.size
    then
      let c := cs[i]!
      match c with
      | `(lg_lam_let| ($id : $ter)) => elabAndLoad i id.getId ter <| fun T fv => elabForTest (i+1) cs (doneT.push T) (doneFv.push fv) k
      | _ => throwError "Unexpected syntax ..."
    else
      k doneT doneFv

#check 1


elab "With" "context" cs:lg_lam_let* "and" "objects" ts:term,* "run" metam:ident : command => unsafe do
  let ts := ts.getElems.raw
  liftTermElabM do
    elabForTest 0 cs #[] #[] <| fun _ fv => do
      let mut Ts : Array Expr := #[]
      for t in ts do
        let term ← elabTermAndSynthesize t .none
        let term := term.onAllSubterms (fun | .fvar i => .mvar ⟨i.name⟩ | x => x)
        Ts := Ts.push term
      let action ← evalConst (Array Expr → Array Expr → MetaM Unit) (metam.getId)
      clearMvarAssignments
      action fv Ts


#check mkMvarStdIndexNoCoE

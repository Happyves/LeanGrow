
import Lean

import LeanGrow.F.Utils.Expr.GetHyps
import LeanGrow.F.Data.BuildDAG.ofTypeExpr
import LeanGrow.F.Data.BuildDAG.SinksFirst
import LeanGrow.F.Data.Unification.EmbedRawWInferWUnis

open Lean Elab Meta Command Tactic



def init_FixCtx (env : Environment) (init_gnodeTypes : Array CExpr) : FixCtx :=
  let T := env.constants.fold (fun sofar name info => sofar.insert name.toString (ConstantInfo.toCstInfo env name info)) CTrie.empty
  let handler := fun n : Nat => (n / init_gnodeTypes.size, n % init_gnodeTypes.size)
  ⟨[init_gnodeTypes], handler, [], .none, T⟩


def simpleImportModules (imp : Array Name) : IO Environment :=
  Lean.importModules (imp.map (fun n => ⟨n,false⟩)) {}



structure miniPermiseDict where
  name : Name
  data : Array EmbedData
  order : Array Nat
  goal : CExpr

def Name_to_thmData (env : Environment) (n : Name) : Option miniPermiseDict :=
  let rec mkEmbD : List (ℕ × CExpr × Bool × List ℕ) → (Array EmbedData × Array Nat)
    | [] => (#[],#[])
    | nx :: more =>
        let (E,O) := mkEmbD more
        if nx.2.2.1
        then (E.push (.inst nx.2.1 #[] #[]), O.push nx.1)
        else (E.push (.nonInst nx.2.1 #[] #[]), O.push nx.1)
        -- push is to the right, so order is preserved
        -- parent and child datat turned out useless
  match env.find? n with
  | .none => .none
  | .some info =>
      let (hs,g) := info.type.getHypsGoal
      let (Hs,G) := ThmType_ToDAG hs hs.length g
      let HS := SinksFirst Hs
      let (embD, orda) := mkEmbD HS
      .some ⟨n,embD,orda,G.1⟩

#exit

def LCtx_to_locPermises (ctx : LocalContext) : :=
  let cctx := ctx.decls.toList.tail
  let mkHyps (cctx : List (Option LocalDecl)) : List Expr :=
    cctx.reduceOption.map LocalDecl.type

#exit

elab "grow" "with" "[" prem:ident,* "]" : tactic => do
  let ref ← getRef
  let env ← getEnv
  let pre_premi := prem.getElems.map TSyntax.getId
  Elab.Tactic.withMainContext do
    let ltx ←  getLCtx

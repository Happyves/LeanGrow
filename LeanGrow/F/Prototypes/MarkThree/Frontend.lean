
import Lean

import LeanGrow.F.Utils.Expr.GetHyps
import LeanGrow.F.Data.BuildDAG.ofTypeExpr
import LeanGrow.F.Data.BuildDAG.SinksFirst
import LeanGrow.F.Data.Unification.EmbedRawWInferWUnis
import LeanGrow.F.Prototypes.MarkThree.Search

open Lean Elab Meta Command Tactic



def init_FixCtx (env : Environment) (init_gnodeTypes : Array CExpr) : FixCtx :=
  --let T := env.constants.fold (fun sofar name info => sofar.insert name.toString (ConstantInfo.toCstInfo env name info)) CTrie.empty
  let modules := env.header.moduleNames
  let T := env.constants.map₁.fold
    (fun sofar name info =>
      if (Name.isPrefixOf `Init modules[env.const2ModIdx[name].get! (α := Nat)]!) || (Name.isPrefixOf `LeanGrow.F.Prototypes.MarkOne.TestTypes modules[env.const2ModIdx[name].get! (α := Nat)]!)
      then sofar.insert name.toString (ConstantInfo.toCstInfo env name info)
      else sofar
      )
    CTrie.empty
  let handler := fun n : Nat => (n / init_gnodeTypes.size, n % init_gnodeTypes.size)
  ⟨[init_gnodeTypes], handler, [], .none, T⟩


def simpleImportModules (imp : Array Name) : IO Environment :=
  Lean.importModules (imp.map (fun n => ⟨n,false⟩)) {}




def Name_to_thmData (env : Environment) (n : Name) : Option miniPermiseDict :=
  let rec mkEmbD (thmD : Array EmbedData) (thmO : Array Nat) : List (ℕ × CExpr × Bool × List ℕ) → (Array EmbedData × Array Nat)
    | [] => (thmD, thmO)
    | nx :: more =>
        if nx.2.2.1
        then mkEmbD (thmD.set! nx.1 (.inst nx.2.1 #[] #[])) (thmO.push nx.1) more
        else mkEmbD (thmD.set! nx.1 (.nonInst nx.2.1 #[] #[])) (thmO.push nx.1) more
        -- push is to the right, so order is preserved
        -- parent and child datat turned out useless
  match env.find? n with
  | .none => .none
  | .some info =>
      let (hs,g) := info.type.getHypsGoal
      let (Hs,G) := ThmType_ToDAG hs hs.length g
      let HS := SinksFirst Hs
      let (embD, orda) := mkEmbD (Array.mkArray HS.length default) #[] HS
      .some ⟨n,embD,orda,G.1⟩


def Names_to_thmData (env : Environment) (L : List Name) : List miniPermiseDict :=
  (L.map (Name_to_thmData env)).reduceOption




def Gnodify : CExpr → CExpr
  | .app f a => .app (Gnodify f) (Gnodify a)
  | .lam n f a i => .lam n (Gnodify f) (Gnodify a) i
  | .forallE n f a i => .forallE n (Gnodify f) (Gnodify a) i
  | .letE n f a z i => .letE n (Gnodify f) (Gnodify a) (Gnodify z) i
  | .proj n i e => .proj n i (Gnodify e)
  | .lnode i o _ => .gnode i o
  | x => x

def LCtx_to_ltx_and_goal (ctx : LocalContext) : List (Nat × CExpr) × CExpr :=
  let cctx := ctx.decls.toList.head! -- should be thm type
  match cctx with
  | .none => ([], .failed)
  | .some self =>
      let (hs,g) := self.type.getHypsGoal
      let (Hs,G) := ThmType_ToDAG hs hs.length g
      (Hs.map (fun (a,b,_) => (a,Gnodify b)), Gnodify G.1)




elab "grow" : tactic => do
  let ref ← getRef
  let dEnv ← simpleImportModules #[`LeanGrow.F.Prototypes.MarkOne.TestTypes]
  Elab.Tactic.withMainContext do
    let Ltx ←  getLCtx

    let (ltx, goal) := LCtx_to_ltx_and_goal Ltx
    let forw2 := ltx.foldl
        (fun sofar (idx,exp) => PageingSet sofar (fun x => (x / 42, x % 42)) 42 (.failed) idx exp)
        []
    let fctx := init_FixCtx dEnv (ltx.map Prod.snd).toArray
    --
    let premises :=(Names_to_thmData dEnv [`myAdd_zero, `Eq.trans].reverse)
    let st : SearchState := ⟨⟨0,1,0,[(0,goal)], .ofGoal 0 goal [] [] [] ⟩, ltx, forw2, (fun x => (x / 42, x % 42)), ltx.length, fctx, [], [], [],[],[]⟩
    --logInfoAt ref s!"{repr premises}"
    let res := search 5 premises st
    match res with
    | .none => logInfoAt ref "nope"
    | .some res! => logInfoAt ref s!"Recovered : {repr res!}"


#check Eq.trans

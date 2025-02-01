
import Lean

import LeanGrow.F.Utils.Expr.GetHyps
import LeanGrow.F.Data.BuildDAG.ofTypeExpr
import LeanGrow.F.Data.BuildDAG.SinksFirst
--import LeanGrow.F.Data.Unification.EmbedRawWInferWUnis
import LeanGrow.F.Prototypes.MarkFive.Search

open Lean Elab Meta Command Tactic



def init_FixCtx (env : Environment) (init_gnodeTypes : Array CExpr) : FixCtx :=
  --let T := env.constants.fold (fun sofar name info => sofar.insert name.toString (ConstantInfo.toCstInfo env name info)) CTrie.empty
  let modules := env.header.moduleNames
  let T := env.constants.map₁.fold
    (fun sofar name info =>
      if (Name.isPrefixOf `Init modules[env.const2ModIdx[name].get! (α := Nat)]!) || (Name.isPrefixOf `LeanGrow.F.Prototypes.MarkFive.TestTypes modules[env.const2ModIdx[name].get! (α := Nat)]!)
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
      .some ⟨.ofThm n,embD,orda,G.1⟩


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


-- New: ∀ in hyps interpreted as premises

def CExpr.getHypsGoal (ty : CExpr) : (List (CExpr × Bool)) × CExpr :=
  let rec go (cache : List (CExpr × Bool)) : CExpr → (List (CExpr × Bool)) × CExpr
    | .forallE _ h b i =>
          match i with
          | .instImplicit => go ((h , true) :: cache) b
          | _ => go ((h , false) :: cache) b
    | e => (cache, e)
  go [] ty


partial def cThmType_ToDAG (hyps : List (CExpr × Bool)) (l_len : Nat) (goal : CExpr) : List (Nat × CExpr × Bool × List Nat) × (CExpr × List Nat) :=
  let inc_helper : Option Nat → Option Nat
    | .none => .some 0
    | .some x => .some (x+1)
  let rec abstractBvars_collectParents (E : CExpr) (offset : Nat → Nat) : CExpr × List Nat :=
    let rec go1 (offset : Nat → Nat) (cache_pars : (List Nat)) (dinfo : List (Option Nat)) : List CExpr → (List CExpr) × List Nat
      | [] =>
          ([], cache_pars)
      | e :: more =>
          match e with
          | .app (.app (.const `optParam _) e) _ => go1 offset cache_pars dinfo (e :: more)  -- got wierd problems in source file gen otherwise
          | .app (.app (.const `outParam _) e) _ => go1 offset cache_pars dinfo (e :: more)
          | .bvar i =>
                let (d?,ndi) := List.headD_tail dinfo .none
                match d? with
                | .none =>
                    let (re,rp) := go1 offset (List.orderedInsertOrLeave (· ≤ · ) (offset (i+1)) cache_pars) ndi more
                    (((CExpr.lnode (offset (i+1))) (.ofBvar i) .none) :: re, rp)
                | .some d =>
                    if i ≤ d
                    then
                      let (re,rp) := go1 offset cache_pars ndi more
                      ((.bvar i) :: re, rp)
                    else
                      let (re,rp) := go1 offset (List.orderedInsertOrLeave (· ≤ · ) (offset (i - d)) cache_pars) ndi more
                      (((CExpr.lnode (offset (i - d))) (.ofBvar i) .none) :: re, rp)
          | .app l r => let d? := List.headD dinfo .none
                        let (re,rp) := go1 offset cache_pars (d? :: dinfo) (l :: r :: more)
                        let (L,re2) := List.headD_tail re .failed
                        let (R,re3) := List.headD_tail re2 .failed
                        (.app L R :: re3, rp)
          | .lam n l r B => let (d?,ndi) := List.headD_tail dinfo .none
                            let (re,rp) := go1 offset cache_pars (d? :: (inc_helper d?) :: ndi) (l :: r :: more)
                            let (L,re2) := List.headD_tail re .failed
                            let (R,re3) := List.headD_tail re2 .failed
                            (.lam n L R B :: re3, rp)
          | .forallE n l r B => let (d?,ndi) := List.headD_tail dinfo .none
                                let (re,rp) := go1 offset cache_pars (d? :: (inc_helper d?) :: ndi) (l :: r :: more)
                                let (L,re2) := List.headD_tail re .failed
                                let (R,re3) := List.headD_tail re2 .failed
                                (.forallE n L R B :: re3, rp)
          | .proj n i e => let (re,rp) := go1 offset cache_pars dinfo (e :: more)
                           let (E,r2) :=  List.headD_tail re .failed
                           (.proj n i E :: r2, rp)
          -- we don't expect `let` or mvar or fvars in thm types ...
          | x =>
              let ndi := List.tailD dinfo []
              let (cs, ps) := go1 offset cache_pars ndi (more)
              (x :: cs, ps)
    let (ce, ps) := go1 offset [] [.none] [E]
    (List.headD ce .failed, ps)
  let rec go2 (l : List (CExpr × Bool)) (count : Nat) (cache : List (Nat × CExpr × Bool × List Nat)) : List (Nat × CExpr × Bool × List Nat) × (CExpr × List Nat) :=
    match l with
    | [] =>
        let (res, deps) := abstractBvars_collectParents goal (fun o => l_len - o)
        (cache, (res, deps))
    | h :: rest =>
          let (res, deps) := abstractBvars_collectParents h.1 (fun o => count - o)
          go2 rest (count - 1) (⟨count, res, h.2, deps⟩ :: cache)
  go2 hyps (l_len - 1) []


def AllHyp_to_thmData (gid : Nat) (type : CExpr) : Option miniPermiseDict :=
  let rec mkEmbD (thmD : Array EmbedData) (thmO : Array Nat) : List (ℕ × CExpr × Bool × List ℕ) → (Array EmbedData × Array Nat)
    | [] => (thmD, thmO)
    | nx :: more =>
        if nx.2.2.1
        then mkEmbD (thmD.set! nx.1 (.inst nx.2.1 #[] #[])) (thmO.push nx.1) more
        else mkEmbD (thmD.set! nx.1 (.nonInst nx.2.1 #[] #[])) (thmO.push nx.1) more
        -- push is to the right, so order is preserved
        -- parent and child datat turned out useless
  match type with
  | .forallE _ _ _ _ =>
      let (hs,g) := type.getHypsGoal
      let (Hs,G) := cThmType_ToDAG hs hs.length g
      let HS := SinksFirst Hs
      let (embD, orda) := mkEmbD (Array.mkArray HS.length default) #[] HS
      .some ⟨.ofLocal gid ,embD,orda,G.1⟩
  | _ => .none



elab "grow" : tactic => do
  let ref ← getRef
  let dEnv ← simpleImportModules #[`LeanGrow.F.Prototypes.MarkFive.TestTypes]
  Elab.Tactic.withMainContext do
    let Ltx ←  getLCtx
    --dbg_trace s!"testing : {(Ltx.decls.toList.reduceOption.map LocalDecl.type)}"
    let (ltx, goal) := LCtx_to_ltx_and_goal Ltx
    let forw2 := ltx.foldl
        (fun sofar (idx,exp) => PageingSet sofar (fun x => (x / 42, x % 42)) 42 (.failed) idx exp)
        []
    let fctx := init_FixCtx dEnv (ltx.map Prod.snd).toArray
    --dbg_trace s!"Test {repr (CExpr.inferType fctx (.const `List.sum []))}"
    let outer_premises := (Names_to_thmData dEnv [`Nat.dvd_trans, `PremOne].reverse)
    let inner_premises := (ltx.map (fun (n,ce) => AllHyp_to_thmData n ce)).reduceOption
    let st : SearchState := ⟨⟨0,1,0,[(0,goal)], .ofGoal 0 goal [] [] [] ⟩, .leaf [0] ltx, forw2, (fun x => (x / 42, x % 42)), ltx.length, fctx, [], [], [],[],[]⟩
    --logInfoAt ref s!"{repr premises}"
    let res := search 10 (inner_premises ++ outer_premises) st
    match res with
    | .none => logInfoAt ref "nope"
    | .some res! => logInfoAt ref s!"Recovered : {repr res!}"


#check Eq.trans


elab "growin" : tactic => do
  let ref ← getRef
  let dEnv ← simpleImportModules #[`LeanGrow.F.Prototypes.MarkFive.TestTypes]
  Elab.Tactic.withMainContext do
    let Ltx ←  getLCtx
    --dbg_trace s!"testing : {(Ltx.decls.toList.reduceOption.map LocalDecl.type)}"
    let (ltx, goal) := LCtx_to_ltx_and_goal Ltx
    let forw2 := ltx.foldl
        (fun sofar (idx,exp) => PageingSet sofar (fun x => (x / 42, x % 42)) 42 (.failed) idx exp)
        []
    let fctx := init_FixCtx dEnv (ltx.map Prod.snd).toArray
    --dbg_trace s!"Test {repr (CExpr.inferType fctx (.const `List.sum []))}"
    let outer_premises := (Names_to_thmData dEnv [`Nat.dvd_trans, `PremOne].reverse)
    let inner_premises := (ltx.map (fun (n,ce) => AllHyp_to_thmData n ce)).reduceOption
    let testin := ltx.filter (fun (_,x) => match x with | .forallE _ _ _ _ => false | _ => true)
    let st : SearchState := ⟨⟨0,1,0,[(0,goal)], .ofGoal 0 goal [] [] [] ⟩, .leaf [0] testin, forw2, (fun x => (x / 42, x % 42)), ltx.length, fctx, [], [], [],[],[]⟩
    --logInfoAt ref s!"{repr premises}"
    let res := search 15 (inner_premises ++ outer_premises) st
    match res with
    | .none => logInfoAt ref "nope"
    | .some res! => logInfoAt ref s!"Recovered : {repr res!}"


import LeanGrow.DAGembed
import LeanGrow.ProcessDecl
import LeanGrow.ProcessLocalCtx
import LeanGrow.Blacklisting
import Mathlib

open Lean



def scoring_by_module (env : Environment) (scores : List (Name × Nat)) : Array (Option Nat) :=
  let modules := env.header.moduleNames
  Id.run do
    let mut out := Array.mkArray modules.size (.none : Option Nat)
    let mut idx := 0
    for n in modules do
      let .some (_,s) := scores.find? (fun x => x.1.isPrefixOf n) | pure ()
      out := out.set! idx s
      idx := idx + 1
    return out

-- only last name that is prefix of mudule matters
def test_scores : List (Name × Nat) :=
  [(`Mathlib.Data.Finset, 20), (`Mathlib.Data.Fin, 20), (`Mathlib.Data.Nat, 10), (`Mathlib.Combinatorics, 50), (`Mathlib.Combinatorics.SetFamily, 70), (`Mathlib.Order, 10), (`Init.Prelude, 5), (`Init.Core, 5), (`Init.Data, 5)]


#check matcher

#check NodeCst

#check SizedDAG


def DAG.findNode [BEq β] (D : DAG α β) (k : β) : Option (DAGnode α β) :=
  List.find? (fun N => N.name == k) D

partial def DAGnode.getLevel [BEq β] (D : DAG α β) (N : DAGnode α β) : Nat :=
  match N.parents with
  | [] => 0
  | ps =>
      let ls := (ps.map (DAG.findNode D)).reduceOption.map (DAGnode.getLevel D)
      let max := Id.run do
          let mut out := 0
          for l in ls do
            if l > out
            then
              out := l
          return out
      max+1

--def DAG.getLevels [BEq β] (D : DAG α β) : RBNode Nat (fun _ => Nat) :=

instance : Inhabited (Nat × RBNode Nat (fun _ => Nat)) where default := (0,{})

partial def DAGnode.getLevel' (D : DAG α Nat) (sofar : RBNode Nat (fun _ => Nat)) (N : DAGnode α Nat) : (Nat × RBNode Nat (fun _ => Nat)) :=
  let H := sofar.find instOrdNat.compare N.name
  match H with
  | .some v => (v, sofar)
  | .none =>
      match N.parents with
      | [] => (0, sofar.insert instOrdNat.compare N.name 0)
      | ps => Id.run do
          let mut max := 0
          let mut store := sofar
          for p in ps do
            let l? := store.find instOrdNat.compare p
            match l? with
            | .some l => if l > max then max := l
            | _ =>
                let .some np := DAG.findNode D p | pure ()
                let (nl,ns) := DAGnode.getLevel' D store np
                store := ns
                if nl > max then max := nl
          return (max+1, (store.insert instOrdNat.compare N.name (max+1)))


def DAG.getLevelz (D : DAG α Nat)  : (RBNode Nat (fun _ => Nat)) :=
  List.foldl (fun memo N => (DAGnode.getLevel' D memo N).2) {} D


def test_dag : DAG Unit Nat := [⟨1,(),[2,3]⟩,⟨2,(),[4]⟩,⟨3,(),[4]⟩,⟨4,(),[]⟩]

def Lean.RBNode.toList (t : RBNode α (fun _ => β)) : List (α × β ) := t.revFold (fun ps k v => (k, v)::ps) []

#eval (DAG.getLevelz test_dag).toList



def score_embed_by_applis_depths (embed : Array (Option NodeCst)) (depths : (RBNode Nat (fun _ => Nat))) (cst_score : Nat) (trafo_depth : Nat → Nat) (combine_scores : List Nat → Nat) : Nat :=
  let res := Id.run do
    let mut out := []
    for a in embed do
      match a with
      | .some (.ofCst _) => out := cst_score :: out
      | .some (.ofNode i) =>
          let .some d := depths.find instOrdNat.compare i | pure ()
          out := (trafo_depth d) :: out
      | .none => pure ()
    return out
  combine_scores res


#check PersistentHashMap.insert
#check PersistentHashMap.find?


def score_embed_by_applis_scores (embed : Array (Option NodeCst)) (scores : PersistentHashMap FVarId Nat ) (dict : PersistentHashMap ℕ FVarId)
  (cst_score : Nat) (trafo_score : Nat → Nat) (combine_scores : List Nat → Nat) : Nat :=
  let res := Id.run do
    let mut out := []
    for a in embed do
      match a with
      | .some (.ofCst _) => out := cst_score :: out
      | .some (.ofNode i) =>
          let .some id := dict.find? i | pure ()
          let .some d := scores.find? id | pure ()
          out := (trafo_score d) :: out
      | .none => pure ()
    return out
  combine_scores res


def getIffHead (thm_type : Expr) : Option (Expr × Expr) :=
  let H := Expr.getForallBody thm_type
  let (h,as) := Expr.getAppFnArgs H
  if h = `Iff
  then
    .some (as[0]!, as[1]!)
  else
    .none


def scoring_by_cst_names (scores : List (Name × Nat)) (thm_type : Expr) : Nat :=
  let H := Expr.getForallBody thm_type
  let nz := Expr.getConstNames H
  Id.run do
    let mut out := 0
    for n in nz do
      let .some (_,s) := scores.find? (fun x => x.1 == n) | pure ()
      out := s + out
    return out



open Lean Elab Meta Command Tactic TryThis

def get_consts_allowed_scored (env : Environment) (scores : List (Name × Nat)) : MetaM ((HashMap Name ConstantInfo) × (PersistentHashMap Name Nat)) := do
  let csts := env.constants.map₁
  let sz := scoring_by_module env scores
  HashMap.foldM
    (fun (nEnv, Scores) decName decInfo => do
        let na ← Loogle.isBlackListed decName
        match sz[env.const2ModIdx[decName].get! (α := Nat)]! with
        | .some sc =>
            if (! na) && (ConstantInfo.isThm decInfo)
            then
              return (nEnv.insert decName decInfo, Scores.insert decName sc)
            else
              return (nEnv, Scores)
        | _ => return (nEnv, Scores)
        )
    ({},{})
    csts



#check HashMap.fold

#check ConstMap
#check SMap


inductive iffManage where
| no | left | right
deriving Repr, Inhabited, BEq


def insertHypAtForallHead (main ins_t : Expr) (ins_name : Name := `dummy) (ins_info : BinderInfo := .default) : Expr :=
  match main with
  | .forallE n t b i => .forallE n t (insertHypAtForallHead b ins_t ins_name ins_info) i
  | e => .forallE ins_name ins_t e ins_info

--#exit

def main_loop_get_best_embeds (ltx : Meta.Context) (cumul_scores : PersistentHashMap FVarId ℕ) (cst_infos : HashMap Name ConstantInfo) (module_scores : PersistentHashMap Name Nat) :
  MetaM (PersistentHashMap ℕ FVarId × (Nat × List ( (ConstantInfo × iffManage) × List (Array (Option NodeCst)))) × (Nat × List ((ConstantInfo × iffManage) × List (Array (Option NodeCst)))) × (Nat × List ((ConstantInfo × iffManage) × List (Array (Option NodeCst))))) := do
      let (ltx_dag, _, ltx_dict') := orderHyps_fromLocalCtx ltx.lctx
      let mut best_module_score_embeds : Nat × List ((ConstantInfo × iffManage) × List (Array (Option NodeCst))) := (0,[])
      let mut best_depth_score_embeds : Nat × List ((ConstantInfo × iffManage) × List (Array (Option NodeCst))) := (0,[])
      let mut best_cumul_score_embeds : Nat × List ((ConstantInfo × iffManage) × List (Array (Option NodeCst))) := (0,[])
      for (decName, decInfo) in cst_infos do
        match decInfo with
        | .thmInfo v => do
            let iff? := getIffHead v.type
            match iff? with
            | .none =>
                let hyps := naiveGetHyps v.type
                let thm_dag := SizeDAG.sinks_fst (orderHyps_wBvar hyps)
                let embeds := matcher thm_dag (SizeDAG.sinks_fst ltx_dag)
                if embeds.isEmpty
                then
                  pure ()
                else
                  -- score by module
                  let mod_sco := module_scores.find! decName
                  if mod_sco > best_module_score_embeds.1
                  then
                    best_module_score_embeds := (mod_sco,[((decInfo,.no),embeds)])
                  else
                    if mod_sco = best_module_score_embeds.1
                    then
                      best_module_score_embeds := (mod_sco,((decInfo,.no),embeds) :: best_module_score_embeds.2)
                  -- score by depth
                  let depths := DAG.getLevelz thm_dag.dag
                  let mut max_d := 0
                  let mut best_ds := ([] : List (Array (Option NodeCst)))
                  for e in embeds do
                    let S := score_embed_by_applis_depths e depths 1 (fun x => x^2) List.sum
                    if S > max_d
                    then
                      best_ds := [e]
                    else
                      if S = max_d
                      then
                        best_ds := e :: best_ds
                  if max_d > best_depth_score_embeds.1
                  then
                    best_depth_score_embeds := (max_d,[((decInfo,.no),best_ds)])
                  else
                    if max_d = best_depth_score_embeds.1
                    then
                      best_depth_score_embeds := (max_d,((decInfo,.no),best_ds) :: best_depth_score_embeds.2)
                  -- score by cumul
                  let mut max_c := 0
                  let mut best_cs := ([] : List (Array (Option NodeCst)))
                  for e in embeds do
                    let S := score_embed_by_applis_scores e cumul_scores ltx_dict' 1 id List.sum
                    if S > max_c
                    then
                      best_cs := [e]
                    else
                      if S = max_c
                      then
                        best_cs := e :: best_cs
                  if max_c > best_cumul_score_embeds.1
                  then
                    best_cumul_score_embeds := (max_c,[((decInfo,.no),best_cs)])
                  else
                    if max_c = best_cumul_score_embeds.1
                    then
                      best_cumul_score_embeds := (max_c,((decInfo,.no),best_cs) :: best_cumul_score_embeds.2)
            | .some (L,R) =>
                  let hyps_l := naiveGetHyps (insertHypAtForallHead v.type L)
                  let thm_dag_l := SizeDAG.sinks_fst (orderHyps_wBvar hyps_l)
                  let embeds_l := matcher thm_dag_l (SizeDAG.sinks_fst ltx_dag)
                  if embeds_l.isEmpty
                  then
                    pure ()
                  else
                    -- score by module
                    let mod_sco := module_scores.find! decName
                    if mod_sco > best_module_score_embeds.1
                    then
                      best_module_score_embeds := (mod_sco,[((decInfo,.left),embeds_l)])
                    else
                      if mod_sco = best_module_score_embeds.1
                      then
                        best_module_score_embeds := (mod_sco,((decInfo,.left),embeds_l) :: best_module_score_embeds.2)
                    -- score by depth
                    let depths := DAG.getLevelz thm_dag_l.dag
                    let mut max_d := 0
                    let mut best_ds := ([] : List (Array (Option NodeCst)))
                    for e in embeds_l do
                      let S := score_embed_by_applis_depths e depths 1 (fun x => x^2) List.sum
                      if S > max_d
                      then
                        best_ds := [e]
                      else
                        if S = max_d
                        then
                          best_ds := e :: best_ds
                    if max_d > best_depth_score_embeds.1
                    then
                      best_depth_score_embeds := (max_d,[((decInfo,.left),best_ds)])
                    else
                      if max_d = best_depth_score_embeds.1
                      then
                        best_depth_score_embeds := (max_d,((decInfo,.left),best_ds) :: best_depth_score_embeds.2)
                    -- score by cumul
                    let mut max_c := 0
                    let mut best_cs := ([] : List (Array (Option NodeCst)))
                    for e in embeds_l do
                      let S := score_embed_by_applis_scores e cumul_scores ltx_dict' 1 id List.sum
                      if S > max_c
                      then
                        best_cs := [e]
                      else
                        if S = max_c
                        then
                          best_cs := e :: best_cs
                    if max_c > best_cumul_score_embeds.1
                    then
                      best_cumul_score_embeds := (max_c,[((decInfo,.left),best_cs)])
                    else
                      if max_c = best_cumul_score_embeds.1
                      then
                        best_cumul_score_embeds := (max_c,((decInfo,.left),best_cs) :: best_cumul_score_embeds.2)
                  let hyps_r := naiveGetHyps (insertHypAtForallHead v.type R)
                  let thm_dag_r := SizeDAG.sinks_fst (orderHyps_wBvar hyps_r)
                  let embeds_r := matcher thm_dag_r (SizeDAG.sinks_fst ltx_dag)
                  if embeds_r.isEmpty
                  then
                    pure ()
                  else
                    -- score by module
                    let mod_sco := module_scores.find! decName
                    if mod_sco > best_module_score_embeds.1
                    then
                      best_module_score_embeds := (mod_sco,[((decInfo,.right),embeds_r)])
                    else
                      if mod_sco = best_module_score_embeds.1
                      then
                        best_module_score_embeds := (mod_sco,((decInfo,.right),embeds_r) :: best_module_score_embeds.2)
                    -- score by depth
                    let depths := DAG.getLevelz thm_dag_r.dag
                    let mut max_d := 0
                    let mut best_ds := ([] : List (Array (Option NodeCst)))
                    for e in embeds_r do
                      let S := score_embed_by_applis_depths e depths 1 (fun x => x^2) List.sum
                      if S > max_d
                      then
                        best_ds := [e]
                      else
                        if S = max_d
                        then
                          best_ds := e :: best_ds
                    if max_d > best_depth_score_embeds.1
                    then
                      best_depth_score_embeds := (max_d,[((decInfo,.right),best_ds)])
                    else
                      if max_d = best_depth_score_embeds.1
                      then
                        best_depth_score_embeds := (max_d,((decInfo,.right),best_ds) :: best_depth_score_embeds.2)
                    -- score by cumul
                    let mut max_c := 0
                    let mut best_cs := ([] : List (Array (Option NodeCst)))
                    for e in embeds_r do
                      let S := score_embed_by_applis_scores e cumul_scores ltx_dict' 1 id List.sum
                      if S > max_c
                      then
                        best_cs := [e]
                      else
                        if S = max_c
                        then
                          best_cs := e :: best_cs
                    if max_c > best_cumul_score_embeds.1
                    then
                      best_cumul_score_embeds := (max_c,[((decInfo,.right),best_cs)])
                    else
                      if max_c = best_cumul_score_embeds.1
                      then
                        best_cumul_score_embeds := (max_c,((decInfo,.right),best_cs) :: best_cumul_score_embeds.2)
        | _ => pure ()
      return (ltx_dict', best_module_score_embeds, best_depth_score_embeds, best_cumul_score_embeds)

-- final step : add to ltx, update cumul scores

#check ConstMap
#check SMap



open Data

def scored_embeds_dedup_main (seen : Trie (List (Array (Option NodeCst))))
  (can : Nat × (ConstantInfo × iffManage) × List (Array (Option NodeCst))) (built :  List (Nat × (ConstantInfo × iffManage) × List (Array (Option NodeCst)))) :
  Trie (List (Array (Option NodeCst))) × List (Nat × (ConstantInfo × iffManage) × List (Array (Option NodeCst))) :=
  let N := can.2.1.1.name.toString
  let Es := can.2.2
  match seen.find? N with
  | .some L => Id.run do
      let mut dump? := true
      for e in Es do
        let mut dif? := true
        for l in L do
          if e == l then dif? := false
        if dif? then dump? := false -- ie. e is not in L
      if dump?
      then
        return (seen, built)
      else
        let nseen := seen.insert N (Es ++ L)
        let new := can :: built
        return (nseen, new)
  | .none =>
      let nseen := seen.insert N Es
      let new := can :: built
      (nseen, new)


def scored_embeds_dedup (built :  List (Nat × (ConstantInfo × iffManage) × List (Array (Option NodeCst)))) :
  List (Nat × (ConstantInfo × iffManage) × List (Array (Option NodeCst))) :=
  (built.foldl (fun (T,L) can => scored_embeds_dedup_main T can L) (Trie.empty, [])).2


def embed_to_expr (embed : Array (Option NodeCst)) --(impInfo : List miniBind)
  (size : Nat) (dict : PersistentHashMap ℕ FVarId) (info : ConstantInfo) : MetaM Expr := do
  let proArg ← ((List.range size).foldl (fun l i => (embed.getD i .none) :: l) []).mapM
      (fun x => match x with
                | .none => return .some (← Meta.mkFreshExprMVar .none)
                | .some (.ofCst e) =>
                      match (CExpr.toExpr e) with
                      | .none => return .none
                      | .some ex => return .some ex
                | .some (.ofNode im) => return .some (Expr.fvar (dict.find! im))
      )
  dbg_trace s!"Ready for Printing ; proArgg: {proArg}"
  --let args : List Expr := ((List.map₂ (proArg) impInfo (fun x i => match i with | .inst => .none | _ => x)).reduceOption).reverse
  -- TODO : replace instances with mvars, without fucking up, which is gonna be hard
  let args : List Expr := ((proArg).reduceOption).reverse
  return mkAppN (.const info.name (info.levelParams.map Level.param)) args.toArray


def add_embed_to_ltx (info : ConstantInfo) (score : Nat) (embed : Array (Option NodeCst)) (dict : PersistentHashMap ℕ FVarId) (userName : Name) (ltx : Meta.Context) (cumul_scores : PersistentHashMap FVarId ℕ) : MetaM (Meta.Context × (PersistentHashMap FVarId ℕ)) := do
  let fvId ← (Meta.withLCtx ltx.lctx ltx.localInstances mkFreshFVarId)
  let args ←  embed.toList.mapM
      (fun x => do match x with
                    | .none => return .none
                    | .some (.ofCst e) =>
                          match (CExpr.toExpr e) with
                          | .none => return .none
                          | .some ex => return .some ex
                    | .some (.ofNode im) => return .some (Expr.fvar (dict.find! im))
      )
  let val ← (Meta.withLCtx ltx.lctx ltx.localInstances ( mkAppM info.name args.reduceOption.toArray))
  let typ ← (Meta.withLCtx ltx.lctx ltx.localInstances (inferType val))
  let nltx := LocalContext.mkLetDecl ltx.lctx fvId userName typ val
  let new_cumul := cumul_scores.insert fvId score
  return ({ltx with lctx := nltx}, new_cumul)


-- ↓ test with mvar assignement

#check Meta.Context

#check List.cons

#check Term.elabTermAndSynthesize

#eval do
  let stx ←  `(term| 1+1)
  let elabed ← Term.elabTermAndSynthesize stx .none
  IO.println elabed

#check 1

def testing_mvar_instanciation : TermElabM Unit := do
  let mv_t ← Meta.mkFreshExprMVar .none
  let head ← Term.elabTermAndSynthesize (← `(term| 42)) .none
  let tail ← Term.elabTermAndSynthesize (← `(term| [37])) .none
  let cons := (Expr.app (Expr.app (Expr.app (.const `List.cons [.zero]) mv_t) head) tail)
  let _ ← inferType cons
  let A? ← mv_t.mvarId!.isAssigned
  logInfo s!"{A?}"

#eval testing_mvar_instanciation

#check MVarId.instantiateMVarsInType
#check MVarId.inferInstance

#check instantiateMVars

def testing_mvar_instanciation_2 : TermElabM Unit := do
  let mv_t ← Meta.mkFreshExprMVar .none
  let head ← Term.elabTermAndSynthesize (← `(term| 42)) .none
  --dbg_trace head
  let tail ← Term.elabTermAndSynthesize (← `(term| [37])) .none
  let cons ←  instantiateMVars (Expr.app (Expr.app (Expr.app (.const `List.cons [.zero]) mv_t) head) tail)
  let _ ← inferType cons
  let _ ←  instantiateMVars cons
  let A? ← mv_t.mvarId!.isAssigned
  logInfo s!"{A?}"

#eval testing_mvar_instanciation_2

#check mkAppM
#check Meta.synthInstance

def testing_mvar_instanciation_3 : TermElabM Unit := do
  let head ← Term.elabTermAndSynthesize (← `(term| 42)) .none
  let tail ← Term.elabTermAndSynthesize (← `(term| [37])) .none
  let cons ← mkAppM `List.cons #[head,tail]
  --let T ← inferType cons
  logInfo s!"{cons}"

#eval testing_mvar_instanciation_3


def add_embed_to_ltx_iff_left (info : ConstantInfo) (score : Nat) (embed : Array (Option NodeCst)) (dict : PersistentHashMap ℕ FVarId) (userName : Name) (ltx : Meta.Context) (cumul_scores : PersistentHashMap FVarId ℕ) : MetaM (Meta.Context × (PersistentHashMap FVarId ℕ)) := do
  let fvId ← (Meta.withLCtx ltx.lctx ltx.localInstances mkFreshFVarId)
  let args ←  embed.toList.mapM
      (fun x => do match x with
                    | .none => return .none
                    | .some (.ofCst e) =>
                          match (CExpr.toExpr e) with
                          | .none => return .none
                          | .some ex => return .some ex
                    | .some (.ofNode im) => return .some (Expr.fvar (dict.find! im))
      )
  let val ← (Meta.withLCtx ltx.lctx ltx.localInstances (mkAppM info.name args.dropLast.reduceOption.toArray))
  match args.getLast! with
  | .some a =>
      let iffed ← (Meta.withLCtx ltx.lctx ltx.localInstances (mkAppM `Iff.mp #[val]))
      let typ ← (Meta.withLCtx ltx.lctx ltx.localInstances (inferType (.app iffed a)))
      let nltx := LocalContext.mkLetDecl ltx.lctx fvId userName typ (.app iffed a)
      let new_cumul := cumul_scores.insert fvId score
      return ({ltx with lctx := nltx}, new_cumul)
  | _=> return (ltx, cumul_scores)

#check Iff.mpr
#check Iff

def add_embed_to_ltx_iff_right (info : ConstantInfo) (score : Nat) (embed : Array (Option NodeCst)) (dict : PersistentHashMap ℕ FVarId) (userName : Name) (ltx : Meta.Context) (cumul_scores : PersistentHashMap FVarId ℕ) : MetaM (Meta.Context × (PersistentHashMap FVarId ℕ)) := do
  let fvId ← (Meta.withLCtx ltx.lctx ltx.localInstances mkFreshFVarId)
  let args ←  embed.toList.mapM
      (fun x => do match x with
                    | .none => return .none
                    | .some (.ofCst e) =>
                          match (CExpr.toExpr e) with
                          | .none => return .none
                          | .some ex => return .some ex
                    | .some (.ofNode im) => return .some (Expr.fvar (dict.find! im))
      )
  let val ← (Meta.withLCtx ltx.lctx ltx.localInstances (mkAppM info.name args.dropLast.reduceOption.toArray))
  match args.getLast! with
  | .some a =>
      let iffed ← (Meta.withLCtx ltx.lctx ltx.localInstances (mkAppM `Iff.mpr #[val]))
      let typ ← (Meta.withLCtx ltx.lctx ltx.localInstances (inferType (.app iffed a)))
      let nltx := LocalContext.mkLetDecl ltx.lctx fvId userName typ (.app iffed a)
      let new_cumul := cumul_scores.insert fvId score
      return ({ltx with lctx := nltx}, new_cumul)
  | _=> return (ltx, cumul_scores)

--#exit

def main_loop (gen : Nat) (ctx : Meta.Context)
  (cumul_scores : PersistentHashMap FVarId ℕ) (cst_infos : HashMap Name ConstantInfo) (module_scores : PersistentHashMap Name Nat)
  : MetaM (PersistentHashMap FVarId ℕ × Meta.Context)  := do
  let (dict, one, two, three) ← main_loop_get_best_embeds ctx cumul_scores cst_infos module_scores
  let joined := (one.2.map (fun x => (one.1,x))) ++ (two.2.map (fun x => (two.1,x))) ++ (three.2.map (fun x => (three.1,x)))
  let cleaned := scored_embeds_dedup joined
  let mut C := ctx
  let mut S := cumul_scores
  let mut name_idx := 0
  for k in cleaned do
    match k.2.1.2 with
    | .no =>
      for q in k.2.2 do
        let (nc, ns) ← add_embed_to_ltx k.2.1.1 k.1 q dict (Name.mkSimple s!"gen_{gen}_idx_{name_idx}" ) C S
        C := nc
        S := ns
        name_idx := name_idx + 1
    | .right =>
      for q in k.2.2 do
        let (nc, ns) ← add_embed_to_ltx_iff_right k.2.1.1 k.1 q dict (Name.mkSimple s!"gen_{gen}_idx_{name_idx}" ) C S
        C := nc
        S := ns
        name_idx := name_idx + 1
    | .left =>
      for q in k.2.2 do
        let (nc, ns) ← add_embed_to_ltx_iff_left k.2.1.1 k.1 q dict (Name.mkSimple s!"gen_{gen}_idx_{name_idx}" ) C S
        C := nc
        S := ns
        name_idx := name_idx + 1
  return (S,C)


def mini_max (S : PersistentHashMap FVarId ℕ) : Option (FVarId × Nat) :=
  S.foldl (fun c k v => match c with | .some (f,s) => if v > s then .some (k,v) else .some (f,s) | _ => .some (k,v)) .none

def to_the_moon_impl : TacticM Unit := do
  let fuel := 3
  let env ← getEnv
  let (cst_info, module_scores) ← get_consts_allowed_scored env test_scores
  let pre_ctx ← getLCtx
  let ctx : Meta.Context := ⟨{}, pre_ctx, #[], .none, 0, .none, false, false⟩
  let cumul_init : PersistentHashMap FVarId ℕ := (pre_ctx.getFVarIds).foldl (fun hm id => hm.insert id 0 ) {}
  let (S,C) ← (List.range fuel).foldlM (fun (s,c) g => main_loop g c s cst_info module_scores) (cumul_init, ctx)
  let .some (f,_) := mini_max S | throwError "oh nooo"
  let res ← (Meta.withLCtx C.lctx C.localInstances (inferType (.fvar f)))
  let p ← (Meta.withLCtx C.lctx C.localInstances (ppExpr res))
  logInfo p


#check Meta.Context

#check LocalContext.getFVarIds

#check PersistentHashMap

elab "to_the_moon" : tactic => to_the_moon_impl


example (A B : Finset Nat) (main : A.card < B.card) : True := by
  --to_the_moon
  sorry

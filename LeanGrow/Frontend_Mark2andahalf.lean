
import LeanGrow.ProcessLocalCtx

import LeanGrow.Caches.mark2clusters_v2

open Lean


def List.map₂ (l : List α) (L : List β) (f : α → β → γ) : List γ :=
  match l, L with
  | xl :: rl, xL :: rL => (f xl xL) :: (List.map₂ rl rL f)
  | _, _ => []

--#exit

def embed_to_expr (embed : Array (Option NodeCst)) --(impInfo : List miniBind)
  (size : Nat) (dict : PersistentHashMap ℕ FVarId) (n_info : Name) (l_info : List Name) : MetaM Expr := do
  let proArg ← ((List.range size).foldl (fun l i => (embed.getD i .none) :: l) []).mapM
      (fun x => match x with
                | .none => return .some (← Meta.mkFreshExprMVar .none)
                | .some (.ofCst e) =>
                      match (CExpr.toExpr e) with
                      | .none => return .none
                      | .some ex => return .some ex
                | .some (.ofNode im) => return .some (Expr.fvar (dict.find! im))
      )
  --dbg_trace s!"Ready for Printing ; proArgg: {proArg}"
  --let args : List Expr := ((List.map₂ (proArg) impInfo (fun x i => match i with | .inst => .none | _ => x)).reduceOption).reverse
  -- TODO : replace instances with mvars, without fucking up, which is gonna be hard
  let args : List Expr := ((proArg).reduceOption).reverse
  return mkAppN (.const n_info (l_info.map Level.param)) args.toArray


--#exit

open Lean Elab Meta Command Tactic TryThis


def Lean.Meta.Tactic.TryThis.delabToEmbellishedRefinableSuggestion (depPreInfo : Expr → MetaM (Option String)) (depPostInfo : Expr → MetaM (Option String)) (e : Expr)  : MetaM Suggestion :=
  return { suggestion := ← delabToRefinableSyntax e, messageData? := e, preInfo? := ← depPreInfo e, postInfo? := ← depPostInfo e }


def Lean.Meta.Tactic.TryThis.addEmbellishedTermSuggestions (ref : Syntax) (es : Array Expr)
    (origSpan? : Option Syntax := none) (header : String := "Try these:")
    (depPreInfo : Expr → MetaM (Option String) := fun _ => do return .none) (depPostInfo : Expr → MetaM (Option String) := fun _ => do return .none)
    (codeActionPrefix? : Option String := none) : MetaM Unit := do
  addSuggestions ref (← es.mapM (delabToEmbellishedRefinableSuggestion depPreInfo depPostInfo))
    (origSpan? := origSpan?) (header := header) (codeActionPrefix? := codeActionPrefix?)

--#exit


elab "grow"  : tactic => do
        let ref ← getRef
        Elab.Tactic.withMainContext do
          let ltx ←  getLCtx
          let (ltx_dag, ltx_dict, ltx_dict') := orderHyps_fromLocalCtx ltx
          let sink_names := (((DAG.find_sinks ltx_dag true).map DAGnode.data).map CExpr.getConstNames).join.map Name.toString
          dbg_trace s!"Sink names: {sink_names}"
          let psn := SortedTrieFormList' sink_names
          for (t, clust) in cl_L do
              let inter := Trie.CountCommon psn t
              if inter ≠ 0
              then
                dbg_trace "Match!"
                for dag in clust do
                  let embeds := matcher dag.dag (SizeDAG.sinks_fst ltx_dag)
                  match embeds with
                  | [] => pure ()
                  | _ =>  do
                          let P ← (embeds.mapM (fun e => embed_to_expr e --(hyps.map Prod.snd)
                            dag.dag.size ltx_dict' dag.cst_name  dag.cst_level_params))
                          addEmbellishedTermSuggestions ref P.toArray
                            (depPostInfo := fun e => do return s!"\n{← ppExpr (← inferType e)}")


elab "growin"  : tactic => do
        let ref ← getRef
        Elab.Tactic.withMainContext do
          let ltx ←  getLCtx
          let (ltx_dag, ltx_dict, ltx_dict') := orderHyps_fromLocalCtx ltx
          let sink_names := (((DAG.find_sinks ltx_dag true).map DAGnode.data).map CExpr.getConstNames).join.map Name.toString
          let psn := SortedTrieFormList' sink_names
          for (t, clust) in cl_L do
              let inter := Trie.CountCommon psn t
              if inter ≠ 0 ∧ ( ((Nat.toFloat inter) / (Nat.toFloat sink_names.length))≥ 0.5)
              then
                dbg_trace "Match!"
                for dag in clust do
                  let embeds := matcher dag.dag (SizeDAG.sinks_fst ltx_dag)
                  match embeds with
                  | [] => pure ()
                  | _ =>  do
                          let P ← (embeds.mapM (fun e => embed_to_expr e --(hyps.map Prod.snd)
                            dag.dag.size ltx_dict' dag.cst_name  dag.cst_level_params))
                          addEmbellishedTermSuggestions ref P.toArray
                            (depPostInfo := fun e => do return s!"\n{← ppExpr (← inferType e)}")


--#exit

elab "print_cluster_cst_names" : command => do
  for c in cl_L do
    IO.println s!"Cluster: {String.intercalate ", " (Trie.print_keys ⟨#[]⟩ c.1)}"
    IO.println "\n"

print_cluster_cst_names

#eval (0 : Float) / (0 : Float)
#eval (0 : Float) / (0 : Float) ≥ 0.33
#eval (0 : Float) / (0 : Float) < 0.33

def focusHyps (ty : Expr) : Expr :=
  match ty with
  | .forallE n h b i => .forallE n h (focusHyps b) i
  | .mdata  _ e => focusHyps e
  | _ => .const `GOAL []


elab "print_cluster_thms" : command => do
  let env ← getEnv
  for c in cl_L do
    IO.println s!"Cluster:"
    for thm in c.2 do
      let thmdata := env.constants.find! thm.cst_name
      IO.println s!"{thmdata.name} : {instToStringFormat.toString (← liftTermElabM (ppExpr (focusHyps thmdata.type)))}"
    IO.println "\n\n\n"



print_cluster_thms
-- in output of ↑, crtl+F for ∈ and whatach successful clustering

--#exit


set_option linter.unusedTactic false

example (l : List ℕ) (a : ℕ) (h : a ∈ l) : True :=
  by
  grow
  trivial

example (l : List ℕ) (a : ℕ) (h : a ∈ l) : True :=
  by
  growin
  trivial

#check List.length_erase_add_one

--#exit

example (l L : List ℕ) (h : 0 < l.length) : True :=
  by
  grow
  trivial

example (l L : List ℕ) (h : 0 < l.length) : True :=
  by
  growin
  trivial

--#exit
example {α : Type u} (l₁ : List α) {l₂ : List α} : True :=
  by
  grow
  trivial

#check List.head?_append_of_ne_nil
-- fail


example {α : Type u} (l₁ : List α) {l₂ : List α} (h : l₁ ≠ [])  : True :=
  by
  grow
  trivial

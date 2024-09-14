
import LeanGrow.Caches.EmpScoreSmol
import LeanGrow.ProcessLocalCtx


open Lean Data

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

def RBNode.getTotalWeight (rbt : RBNode ℕ (fun _ ↦ ℕ)) : ℕ :=
  rbt.fold (fun s _ v => s + v) 0

def RBNode.normalisze (rbt : RBNode ℕ (fun _ ↦ ℕ)) : RBNode ℕ (fun _ ↦ Float) :=
  let totalWeight := Nat.toFloat (RBNode.getTotalWeight rbt)
  RBNode.map (fun _ v => (Nat.toFloat v) / totalWeight) rbt

partial def QueryTree.query_big_subset (Q : Trie Unit) (pre_computed_query_size count : Nat) (T : QueryTree (BS α)) : List α :=
  match T with
  | .root c => (c.map (QueryTree.query_big_subset Q pre_computed_query_size count)).join
  | .node t c => if Trie.CountCommon t Q = Trie.size t then (c.map (QueryTree.query_big_subset Q pre_computed_query_size (count + Trie.size t))).join else []
  | .leaf (.ofVal a) => if (Nat.toFloat count) / (Nat.toFloat pre_computed_query_size) ≥ 0.5 then [a] else []
                          -- for a ratio of 0.66 the first test used to not return anything
  | .leaf (.ofPoint t) => QueryTree.query_big_subset Q pre_computed_query_size count t




partial def Trie.destratify : Trie (tBS α) → Trie α
| .leaf x =>
      match x with
      | .some (.ofPoint p) => Trie.destratify p
      | .some (.ofVal x) => .leaf (.some x)
      | _ => .leaf .none
| .node1 x a t =>
      match x with
      | .some (.ofVal x) => .node1 (.some x) a (Trie.destratify t)
      | .none => .node1 .none a (Trie.destratify t)
      | _ => .leaf .none -- shouldn't happen
| .node x as ts =>
      match x with
      | .some (.ofVal x) => .node (.some x) as (ts.map Trie.destratify)
      | .none => .node .none as (ts.map Trie.destratify)
      | _ => .leaf .none

def RBNode.destratify : RBNode α (fun _ => (rBS α β)) → RBNode α (fun _ => β)
| .leaf => .leaf
| .node c l k v r =>
    match v with
    | .ofVal w => .node c (RBNode.destratify l) k w (RBNode.destratify r)
    | .ofPoint p => RBNode.destratify p



elab "grow"  : tactic => do
  let ref ← getRef
  Elab.Tactic.withMainContext do
    let ltx ←  getLCtx
    let (ltx_dag, _, ltx_dict') := orderHyps_fromLocalCtx ltx
    let sink_names := (((DAG.find_sinks ltx_dag true).map DAGnode.data).map CExpr.getConstNames).join.map Name.toString
    let psn := SortedTrieFormList' sink_names
    let qch := QueryTree.query psn LinkTreeTop
    let mut final : List (Float × pdata) := []
    for (nr, clust) in qch do
      for pd in clust do
        let pdn := pd.cst_name.toString
        let .some proba_thm := Trie.find? (Trie.destratify thm_appearances) pdn | final := (0,pd) :: final
        let .some entry := Trie.find? (Trie.destratify empirical_score_data) pdn | final := (0,pd) :: final
        let .some proba_clu_cond_thm := RBNode.find instOrdNat.compare entry.hyp_cl nr | final := (0,pd) :: final
        let .some proba_clu := RBNode.find instOrdNat.compare (RBNode.destratify hyp_clust_appearances) nr | final := (0,pd) :: final
        if proba_clu == 0
        then
          final := (0,pd) :: final
        else
          let gcs := (QueryTree.query pd.goal_cst_names g_LinkTreeTop).map Prod.fst
          -- ↓ max goal cluster proba
          -- let mut max_g_score := (0 : Float)
          -- for gc in gcs do
          --   let .some proba_clu_cond_thm_g := RBNode.find instOrdNat.compare entry.g_cl gc | pure ()
          --   let .some proba_clu_g := RBNode.find instOrdNat.compare (RBNode.destratify goal_clust_appearances) gc | pure ()
          --   if !(proba_clu_g == 0)
          --   then
          --     let can := (proba_clu_cond_thm_g * proba_thm ) / proba_clu_g
          --     if can > max_g_score
          --     then
          --       max_g_score := can
          -- final := ((max_g_score + ((proba_clu_cond_thm * proba_thm ) / proba_clu))/2, pd) :: final
          -- ↓ average goal cluster proba
          let mut sum_g_score := (0 : Float)
          for gc in gcs do
            let .some proba_clu_cond_thm_g := RBNode.find instOrdNat.compare entry.g_cl gc | pure ()
            let .some proba_clu_g := RBNode.find instOrdNat.compare (RBNode.destratify goal_clust_appearances) gc | pure ()
            if !(proba_clu_g == 0)
            then
              sum_g_score := sum_g_score + ((proba_clu_cond_thm_g * proba_thm ) / proba_clu_g)
          final := ((if gcs.isEmpty then 0 else ((sum_g_score / (Nat.toFloat gcs.length)) + ((proba_clu_cond_thm * proba_thm ) / proba_clu))/2), pd) :: final
    let finaly := List.mergeSort (fun n m => n.1 ≥ m.1) final
    for (sc, dag) in finaly do
      let embeds := matcher dag.dag (SizeDAG.sinks_fst ltx_dag)
      match embeds with
      | [] => pure ()
      | _ =>  do
              let P ← (embeds.mapM (fun e => embed_to_expr e --(hyps.map Prod.snd)
                dag.dag.size ltx_dict' dag.cst_name  dag.cst_level_params))
              addEmbellishedTermSuggestions ref P.toArray
                (depPostInfo := fun e => do return s!"\nScore {sc}\n{← ppExpr (← inferType e)}")

--#exit

set_option linter.unusedTactic false

example (l : List ℕ) (a : ℕ) (h : a ∈ l) : insert a l = l :=
  by
  --grow
  sorry

#check List.insert_pos
-- via average goal cluster probas is better, but both are absolutely terrible

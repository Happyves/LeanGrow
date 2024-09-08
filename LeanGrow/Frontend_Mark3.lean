
import LeanGrow.ProcessLocalCtx

import LeanGrow.Caches.QueryTreeSmoothClusters_wL_col2
import LeanGrow.Caches.QueryTreeSmoothClustersGoal_wL_col2
import LeanGrow.Caches.LargeTransitionGraphClosure_clos_3

--import LeanGrow.Caches.SmolTransitionGraphs

import LeanGrow.Transitions_QueTreClus

import LeanGrow.NameListCompare

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



elab "grow"  : tactic => do
  let ref ← getRef
  Elab.Tactic.withMainContext do
    let ltx ←  getLCtx
    let (ltx_dag, _, ltx_dict') := orderHyps_fromLocalCtx ltx
    let sink_names := (((DAG.find_sinks ltx_dag true).map DAGnode.data).map CExpr.getConstNames).join.map Name.toString
    let psn := SortedTrieFormList' sink_names
    let gcn := SortedTrieFormList' (List.dedup ((Expr.getConstNames (← getMainTarget)).map Name.toString))
    let qch := QueryTree.query psn LinkTreeTop
    let qcg := QueryTree.query_big_subset gcn (Trie.size gcn) 0 g_LinkTreeTop
    let qt := QueryTree.query psn RTreeTop
    let mut final : List (Float × pdata) := []
    for (nr, clust) in qch do
      dbg_trace "wtf 1"
      let .some (_,nei) := qt.find? (fun (n,_) => n == nr) | throwError "aahh 1"
      for (gnr, _) in qcg do
        let score := match (RBNode.normalisze nei).find instOrdNat.compare gnr with | .some v => v | _ => 0
        final := (clust.map (score, ·)) ++ final
    let finaly := List.mergeSort (fun n m => n.1 ≥ m.1) final
    for (sc, dag) in finaly do
      dbg_trace "wtf"
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
-- found with highest cluster score !

example (l : List ℕ) (a : ℕ) (h : a ∈ l) :  (l.erase a).length + 1 = l.length :=
  by
  --grow
  sorry

#check List.length_erase_add_one
--found with subobtimal score 0.009577 with best score 0.011353

example (l : List ℕ) (a : ℕ) (h : a ∈ l) : l[List.indexOf a l]? = some a :=
  by
  --grow
  sorry

-- No clue what is going on here ; first I got stack overflows due to merge sort, then the infoview freezes and refuses to print the score part
#check List.getElem?_indexOf


#exit

partial def QueryTree.query (Q : Trie Unit) (T : QueryTree (BS α)) : List α :=
  match T with
  | .root c => (c.map (QueryTree.query Q)).join
  | .node t c => if Trie.CountCommon t Q = Trie.size t then (c.map (QueryTree.query Q)).join else []
  | .leaf (.ofVal a) => [a]
  | .leaf (.ofPoint t) => QueryTree.query Q t


elab "grow_mini"  : tactic => do
  let ref ← getRef
  Elab.Tactic.withMainContext do
    let ltx ←  getLCtx
    let (ltx_dag, _, ltx_dict') := orderHyps_fromLocalCtx ltx
    let sink_names := (((DAG.find_sinks ltx_dag true).map DAGnode.data).map CExpr.getConstNames).join.map Name.toString
    let psn := SortedTrieFormList' sink_names
    let gcn := SortedTrieFormList' (List.dedup ((Expr.getConstNames (← getMainTarget)).map Name.toString))
    let qch := QueryTree.query psn LinkTreeTop
    let qcg := QueryTree.query gcn g_LinkTreeTop
    let qt := QueryTree.query psn OTreeTop
    let mut final : List (Nat × pdata) := []
    for (nr, clust) in qch do
      let .some (_,nei) := qt.find? (fun (n,_) => n == nr) | throwError "aahh 1"
      for (gnr, _) in qcg do
        let score := match nei.find instOrdNat.compare gnr with | .some v => v | _ => 0
        final := (clust.map (score, ·)) ++ final
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


example (l : List ℕ) (a : ℕ) (h : a ∈ l) : insert a l = l :=
  by
  --grow_mini
  sorry

#check List.insert_pos

#eval Trie.print_keys ⟨ #[]⟩  PDATA.List.insert_pos.goal_cst_names

example (l : List ℕ) (a : ℕ) (h : a ∈ l) :  (l.erase a).length + 1 = l.length :=
  by
  --grow_mini
  sorry

#check List.length_erase_add_one

example (l : List ℕ) (a : ℕ) (h : a ∈ l) : l[List.indexOf a l]? = some a :=
  by
  --grow_mini
  sorry

#check List.getElem?_indexOf

#exit

elab "grow_screw_transions"  : tactic => do
  let ref ← getRef
  Elab.Tactic.withMainContext do
    let ltx ←  getLCtx
    let (ltx_dag, _, ltx_dict') := orderHyps_fromLocalCtx ltx
    let sink_names := (((DAG.find_sinks ltx_dag true).map DAGnode.data).map CExpr.getConstNames).join.map Name.toString
    let psn := SortedTrieFormList' sink_names
    let gcn := SortedTrieFormList' (List.dedup ((Expr.getConstNames (← getMainTarget)).map Name.toString))
    IO.println ("DBG  " ++ s!"{List.dedup  ((Expr.getConstNames (← getMainTarget)).map Name.toString)}")
    let qch := QueryTree.query psn LinkTreeTop
    let qcg := (QueryTree.query gcn g_LinkTreeTop).map Prod.fst
    let mut final : List (Float × pdata) := []
    for (_, clust) in qch do
      for pd in clust do
        let gcs := (QueryTree.query pd.goal_cst_names g_LinkTreeTop).map Prod.fst
        let score : Float := Id.run do
          let mut inter := 0
          for n in qcg do
            if gcs.contains n then inter := inter + 1
          return (Nat.toFloat inter) / (Nat.toFloat gcs.length)
        final := ((score, pd)) :: final
    let finaly := List.mergeSort (fun n m => n.1 ≥ m.1) final
    for (sc, dag) in finaly do
      let embeds := matcher dag.dag (SizeDAG.sinks_fst ltx_dag)
      match embeds with
      | [] => pure ()
      | _ =>  do
              let P ← (embeds.mapM (fun e => embed_to_expr e --(hyps.map Prod.snd)
                dag.dag.size ltx_dict' dag.cst_name  dag.cst_level_params))
              addEmbellishedTermSuggestions ref P.toArray
                (depPostInfo := fun e => do return s!"\nScore {sc}\n{Trie.print_keys ⟨#[]⟩ dag.goal_cst_names}\n{← ppExpr (← inferType e)}")




example (l : List α) [DecidableEq α] (a : α) (h : a ∈ l) : insert a l = l :=
  by
  grow_screw_transions
  sorry
  -- Eq, List, Insert.insert, List, List.instInsertOfDecidableEq_mathlib

#eval List.dedup ["Eq", "List", "Insert.insert", "List", "List.instInsertOfDecidableEq_mathlib"]

#check List.insert_pos

#eval Trie.print_keys ⟨ #[]⟩  PDATA.List.insert_pos.goal_cst_names

example (l : List ℕ) (a : ℕ) (h : a ∈ l) :  (l.erase a).length + 1 = l.length :=
  by
  --grow_screw_transions
  sorry

#check List.length_erase_add_one

example (l : List ℕ) (a : ℕ) (h : a ∈ l) : l[List.indexOf a l]? = some a :=
  by
  --grow_screw_transions
  sorry

#check List.getElem?_indexOf



#exit

example (l L : List ℕ) (h : 0 < l.length) : True :=
  by
  grow
  trivial


#check List.ne_nil_of_length_pos


example {α : Type u} (l₁ : List α) {l₂ : List α} (h : l₁ ≠ [])  : True :=
  by
  grow
  trivial

#check List.head?_append_of_ne_nil

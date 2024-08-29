
import LeanGrow.ProcessLocalCtx

import LeanGrow.Caches.QueryTreeSmoothClusters_wL_col2
import LeanGrow.Caches.QueryTreeSmoothClustersGoal_wL_col2
import LeanGrow.Caches.LargeTransitionGraphClosure_clos_3

import LeanGrow.Transitions_QueTreClus

open Lean

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
    let (ltx_dag, _, ltx_dict') := orderHyps_fromLocalCtx ltx
    let sink_names := (((DAG.find_sinks ltx_dag true).map DAGnode.data).map CExpr.getConstNames).join.map Name.toString
    let psn := SortedTrieFormList' sink_names
    let qch := QueryTree.query psn LinkTreeTop
    let qcg := QueryTree.query psn g_LinkTreeTop
    let qt := QueryTree.query psn RTreeTop
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



set_option linter.unusedTactic false

example (l : List ℕ) (a : ℕ) (h : a ∈ l) : insert a l = l :=
  by
  --grow
  sorry

#check List.insert_pos

example (l : List ℕ) (a : ℕ) (h : a ∈ l) :  (l.erase a).length + 1 = l.length :=
  by
  --grow
  sorry

#check List.length_erase_add_one

example (l : List ℕ) (a : ℕ) (h : a ∈ l) : l[List.indexOf a l]? = some a :=
  by
  --grow
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

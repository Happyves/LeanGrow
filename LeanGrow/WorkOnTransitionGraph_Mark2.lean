
import LeanGrow.Caches.ProcessedTransitionGraphs
import LeanGrow.Caches.ProcessedTransitionGraphsGolas
import LeanGrow.Caches.mark2clusters_v2
import LeanGrow.Caches.mark1goalClusters
import LeanGrow.LtxManagement.Iffs
import LeanGrow.LtxManagement.TryInduction
import LeanGrow.PathCounter
import LeanGrow.ProcessLocalCtx
import LeanGrow.NameListCompare


open Lean



-- haven't tested this one ; arrays might be faster anyway
elab "makePathCountGraph" : command => do
  let res := QT_build 0 (joined_trans_hyp.size - 1) 0 (joined_trans_hyp_goal.size - 1) (weighted_walk_counter joined_trans_hyp joined_trans_hyp_goal) 3
  let source := s!"import LeanGrow.Quadtree\n" ++ (String.intercalate "\n" (res.map (fun (n,qt) => s!"def {n} : QT Nat Nat Wrap := {QT.toString instToStringNat.toString instToStringNat.toString ValPost.toStringTrick qt}")))
  IO.FS.writeFile ⟨"/./home/yves/Desktop/CodeWorkspace/Lean4_General/LeanGrow/LeanGrow/Caches/PathCountGraph.lean"⟩ (source)

--makePathCountGraph


elab "makePathCountGraph2" : command => do
  let mut a_o_as := #[]
  let split_param := 10
  let num_splits := (joined_trans_hyp.size * joined_trans_hyp_goal.size) / split_param
  for ca in [0:(num_splits)] do
    let mut A := Array.mkArray split_param 0
    for spc in [0:(split_param)] do
      let unpacked_index := ca*split_param + spc
      let res := weighted_walk_counter joined_trans_hyp joined_trans_hyp_goal (unpacked_index / joined_trans_hyp.size) (unpacked_index % joined_trans_hyp.size)
      A := A.set! spc res
    a_o_as := a_o_as.push A
  let mut A := Array.mkArray split_param 0
  for spc in [0:((joined_trans_hyp.size * joined_trans_hyp_goal.size) % split_param)] do
    let unpacked_index := num_splits*split_param + spc
    let res := weighted_walk_counter joined_trans_hyp joined_trans_hyp_goal (unpacked_index / joined_trans_hyp.size) (unpacked_index % joined_trans_hyp.size)
    A := A.set! spc res
  a_o_as := a_o_as.push A
  -- print
  let mut toSource := []
  let mut co := 0
  for a in a_o_as do
    toSource := s!"\ndef final_trans_{co} : Array Nat := {a}" :: toSource
    co := co+1
  toSource := toSource.reverse
  let source := (String.join toSource) ++ s!"\ndef final_trans := {String.intercalate " ++ " ((List.range (num_splits + 1)).map (s!"final_trans_{·}"))}"
  IO.FS.writeFile ⟨"/./home/yves/Desktop/CodeWorkspace/Lean4_General/LeanGrow/LeanGrow/Caches/PathCountGraph.lean"⟩ (source)

-- unsuccessfully ran on ↓ many nodes ... may just be infeasible to cache ...
#eval (joined_trans_hyp.size * joined_trans_hyp_goal.size)

--makePathCountGraph2


open Lean Data Meta Elab Tactic

def find_initial_clusters (sink_names : Trie Unit) : TacticM (List (Nat × List pdata)) := do
  let mut res := []
  let mut count := 0
  for (t, clust) in cl_L_a do
    let inter := Trie.CountCommon sink_names t
    if inter ≠ 0 ∨ (Trie.size t == 0) ∧ ( ((Nat.toFloat inter) / (Nat.toFloat (Trie.size sink_names)))≥ 0.5)
    then res := (count, clust) :: res ; count := count + 1
    else count := count + 1
  return res


def embed_to_expr (embed : Array (Option NodeCst))
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
  let args : List Expr := ((proArg).reduceOption).reverse
  return ← instantiateMVars (mkAppN (.const n_info (l_info.map Level.param)) args.toArray)

#check Term.elabLetDecl
#check Term.synthesizeInstMVarCore
-- hopefully instantiation does TC ?!?!?!?!


/-- remobve breaks to add all lemmata, makes for increadibly slow tactic though-/
def explore_cluster (clu : List pdata) (ltx_dag : SizedDAG CExpr ℕ) (ltx_dict' : PersistentHashMap ℕ FVarId) (signature : Name) : TacticM Unit := do
  let mut breaks := 3
  for dag in clu do
    if breaks > 0
    then
      let embeds := matcher dag.dag (SizeDAG.sinks_fst ltx_dag)
      withMainContext do
        for emb in embeds do
          try
            let res ← embed_to_expr emb dag.dag.size ltx_dict' dag.cst_name  dag.cst_level_params
            let resT ← inferType res
            liftMetaTactic fun mvarId => do
              let mvarIdNew ← mvarId.define (signature ++ dag.cst_name ++ mvarId.name) resT res
              let (_, mvarIdNew) ← mvarIdNew.intro1P
              return [mvarIdNew]
          catch | _ => pure ()
    else
      break



def find_goal_cluster (cst_names : Trie Unit) : TacticM ((Nat)) := do
  let mut res := 0
  let mut count := 0
  let mut ma := 0
  for (t, _) in g_cl_L_a do
    let inter := Trie.CountCommon cst_names t
    if inter > ma
    then  ma := inter
          res := (count) ; count := count + 1
    else  count := count + 1
  return res


def selectNextCluster (nei : List (Nat)) (gnc : Nat) : Option Nat :=
  let weights := (nei.take 3).map (weighted_walk_counter joined_trans_hyp joined_trans_hyp_goal · gnc)
  let mw := match List.maximum? weights with | .some m => m | _ => 0
  let mwi := weights.findIdx (· == mw)
  if mw == 0 then .none else .some mwi



def walk_the_walk (sink_names : Trie Unit) : TacticM Unit := do
  let init ← find_initial_clusters sink_names
  let g ← getMainTarget
  let names := (Expr.getConstNames g).map Name.toString
  let psn := SortedTrieFormList' names
  let gc ← find_goal_cluster psn
  for (pos, data) in init do
    let mut p := pos
    let mut d := data
    for i in List.range 3 do
      let (op, od) ← withMainContext do
        let ltx ←  getLCtx
        let (ltx_dag, _, ltx_dict') := orderHyps_fromLocalCtx ltx
        explore_cluster d ltx_dag ltx_dict' (Name.mkSimple s!"p{p}i{i}")
        let nei := joined_trans_hyp.get! p
        let next := match selectNextCluster (nei.map Prod.fst) gc with | .some n => n | _ => p
        let next_c := cl_L.get! next
        return (next, next_c.2)
      p := op
      d := od



elab "grow" : tactic => do
  let ref ← getRef
  Elab.Tactic.withMainContext do
    let ltx ←  getLCtx
    let (ltx_dag, ltx_dict, ltx_dict') := orderHyps_fromLocalCtx ltx
    let sink_names := (((DAG.find_sinks ltx_dag true).map DAGnode.data).map CExpr.getConstNames).join.map Name.toString
    let psn := SortedTrieFormList' sink_names
    walk_the_walk psn



example (l L : List α) (h : 0 < l.length) : True := by
  --grow
  trivial

/-
Got wierd error to investigate, even the embed to expr handles failure:

invalid occurrence of universe level 'u' at '_example', it does not occur at the declaration type, nor it is explicit universe level provided by the user, occurring at expression
  Function.Bijective.{u + 1, u + 1} List.reverse.{u}
at declaration body
  fun {α : Type u_1} (l L : List α) (h : 0 < l.length) ↦
    let p145i0.List.reverse_bijective._uniq.13241 : Function.Bijective List.reverse := List.reverse_bijective;
    ?m.17083 l L h p145i0.List.reverse_bijective._uniq.13241

-/

#check List.reverse_bijective
#check Function.Bijective

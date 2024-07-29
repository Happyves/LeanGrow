
import LeanGrow.Caches.ProcessedTransitionGraphs
import LeanGrow.Caches.ProcessedTransitionGraphsGolas
import LeanGrow.LtxManagement.Iffs
import LeanGrow.LtxManagement.TryInduction
import LeanGrow.PathCounter

open Lean


def randSelectCluster (data : List (Nat × Nat)) : IO Nat := do
  let (cumulate, count) : (List (Nat × Nat)) × Nat := (data.foldl (fun (C,c) (clu,tran) => ((clu, c + tran):: C, c + tran)) ([],0))
  let cumul' := cumulate.reverse
  let r ← IO.rand 0 count
  let mut ret := 0
  for (cl,c) in cumul' do
    if c ≥ r then ret := cl ; break
  return ret


-- make array of arrays via ++, also in source ?
elab "makePathCountGraph" : command => do
  let res := QT_build 0 (cl_L_a.size - 1) 0 (g_cl_L_a.size - 1) (weighted_walk_counter cl_L_a g_cl_L_a) 3
  let source := s!"import LeanGrow.Quadtree\n" ++ (String.intercalate "\n" (res.map (fun (n,qt) => s!"def {n} : QT Nat Nat Wrap := {QT.toString instToStringNat.toString instToStringNat.toString ValPost.toStringTrick qt}")))
  IO.FS.writeFile ⟨"/./home/yves/Desktop/CodeWorkspace/Lean4_General/LeanGrow/LeanGrow/Caches/PathCountGraph.lean"⟩ (source)

--makePathCountGraph

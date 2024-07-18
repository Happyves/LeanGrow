
import LeanGrow.Caches.mark1goalClusters

open Lean


elab "trace_hyp_names" : command => do
  for d in goal_cluster_list do
    IO.println s!"\n{d.cst_name}\nSink names: {String.intercalate ", " (Trie.print_keys ⟨#[]⟩ d.name_list)}\nType : {← Elab.Command.liftTermElabM (Meta.ppExpr ((← getEnv).constants.find! d.cst_name).type)}\n"

trace_hyp_names

#check Nat
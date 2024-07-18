
import LeanGrow.Caches.mark2cache_v2

open Lean

def focusHyps (ty : Expr) : Expr :=
  match ty with
  | .forallE n h b i => .forallE n h (focusHyps b) i
  | .mdata  _ e => focusHyps e
  | _ => .const `GOAL []

elab "trace_hyp_names" : command => do
  for d in cluster_list do
    IO.println s!"\n{d.cst_name}\nSink names: {String.intercalate ", " (Trie.print_keys ⟨#[]⟩ d.sink_cst_names)}\nType : {← Elab.Command.liftTermElabM (Meta.ppExpr ((← getEnv).constants.find! d.cst_name).type)}\n"

trace_hyp_names

#check Nat

-- List.splitOn_nil has no sink names

/-
TODO:
- for frontends, allow thms from cluster with empty trie to be applied! they currently aren't tried since the intersection is trivially 0
- implement the second phase clustering
- switch to a ration where denom is max of trie sizes, to prevent bad clusters du to size... or sort thms by name list size before ?
-/


import LeanGrow.F.Utils.DAG.Query
import Lean.Data.RBTree -- for RBTree ; delete if not used

open Lean



#exit

-- haven't really tested this
partial def DAG.topo_sort (d : SizedDAG α Nat) (discard : RBTree Nat (instOrdNat.compare)) (count : Nat) : (List (DAGnode α Nat)) :=
  dbg_trace s!"On count {count}, discarded {discard.toList}"
  let rec find_sources (d : List (DAGnode α Nat)) (discard : RBTree Nat (instOrdNat.compare)) : (List (DAGnode α Nat)) × (RBTree Nat (instOrdNat.compare)) :=
    match d with
    | [] => ([], discard)
    | n :: rest => if n.parents.filter (fun x => !(discard.contains x)) = []
                   then let (da, di) := find_sources rest (discard.insert n.name) ; (n :: da, di)
                   else find_sources rest discard
  if count ≥ d.size
  then []
  else let (pass_da, pass_di) := find_sources d.dag discard
       ((DAG.topo_sort d pass_di (count + pass_da.length)) ++  pass_da.reverse)



-- dags are already topologically sorted (but in wrong order), also in the lctx
def SizeDAG.sinks_fst (d : SizedDAG α β) : SizedDAG α β :=
 {d with dag := List.reverse d.dag}



-- def DAG.find_sinks [Inhabited α] (D : SizedDAG α Nat) : (List (DAGnode α Nat)) :=
--   let rec go (d : List (DAGnode α Nat)) (ref : Array (DAGnode α Nat) ) (candidates : RBTree Nat (instOrdNat.compare)) : List (DAGnode α Nat) :=
--     match d with
--     | [] => ((candidates.val.map (fun k _ => ref.get! k)).toArray.map (Sigma.snd)).toList
--             -- massive hoop jumping. either get as array, or write API for RBMap.map
--     | n :: rest =>
--         dbg_trace s!"Looking at node {n.name}"
--         dbg_trace s!"Deleting parents {n.parents} from the candidates"
--         let del_p := n.parents.foldl (fun (r) k => RBTree.erase r k) candidates
--         go rest ref (RBTree.insert del_p n.name)
--   go D.dag D.dag.toArray {}

-- ↑ I blame the heat

def DAG.find_sinks [Inhabited α] (D : SizedDAG α Nat) (ltx? : Bool) : (List (DAGnode α Nat)) :=
  let candidates : RBTree Nat (instOrdNat.compare) := RBTree.ofList (if ltx? then (List.range D.size).map (· + 1) else List.range D.size)
  let trimed := (D.dag.foldl (fun r n => (n.parents.foldl (fun r' k => RBTree.erase r' k) r)) candidates)
  D.dag.filter (fun x => trimed.contains x.name)

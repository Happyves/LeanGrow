
import LeanGrow.F.Utils.DAG.Types
import Mathlib.Data.List.Sort
import LeanGrow.F.Utils.List

open Lean

-- # Sinks


def pDAG.find_sinks (d : pDAG α β) [BEq β] [BEq α] [Inhabited α] (r : β → β → Prop) [DecidableRel r] : List (pDAGnode α β) :=
  let R := fun a b : pDAGnode α β =>  r a.label b.label
  let rec go (candidates blacklist : List (pDAGnode α β)): List (pDAGnode α β) → List (pDAGnode α β)
  | [] => candidates
  | node :: more =>
      let pass? := List.orderedContains R node blacklist
      if pass?
      then
        let nb := node.parents.foldl (fun s n => List.orderedInsertOrLeave R ⟨n, default, []⟩ s) blacklist
        let nc := node.parents.foldl (fun s n => List.orderedEraseOrLeave R ⟨n, default, []⟩  s) candidates
        go nc nb more
      else
        let nb := node.parents.foldl (fun s n => List.orderedInsertOrLeave R ⟨n, default, []⟩  s) blacklist
        let nc := node.parents.foldl (fun s n => List.orderedEraseOrLeave R ⟨n, default, []⟩  s) candidates
        go (node :: nc) nb more
  go [] [] d

def pDAG.find_sinks_noOrder (d : pDAG α β) [BEq β] [BEq α] [Inhabited α] : List (pDAGnode α β) :=
  let rec go (candidates blacklist : List (pDAGnode α β)): List (pDAGnode α β) → List (pDAGnode α β)
  | [] => candidates
  | node :: more =>
      let pass? := List.contains blacklist node
      if pass?
      then
        let nb := node.parents.foldl (fun s n => List.insertOrLeave ⟨n, default, []⟩ s) blacklist
        let nc := node.parents.foldl (fun s n => List.eraseOrLeave  ⟨n, default, []⟩  s) candidates
        go nc nb more
      else
        let nb := node.parents.foldl (fun s n => List.insertOrLeave ⟨n, default, []⟩ s) blacklist
        let nc := node.parents.foldl (fun s n => List.eraseOrLeave  ⟨n, default, []⟩  s) candidates
        go (node :: nc) nb more
  go [] [] d



def pDAG.find_sinks_uniqLabels (d : pDAG α β) [BEq β] [Inhabited α] (r : β → β → Prop) [DecidableRel r] : List (pDAGnode α β) :=
  let R := fun a b : pDAGnode α β =>  r a.label b.label
  let rec go (candidates blacklist : List (pDAGnode α β)): List (pDAGnode α β) → List (pDAGnode α β)
  | [] => candidates
  | node :: more =>
      let pass? := @List.orderedContains _ ⟨pDAGnode.lbeq⟩ R _ node blacklist
      if pass?
      then
        let nb := node.parents.foldl (fun s n => @List.orderedInsertOrLeave _ ⟨pDAGnode.lbeq⟩ R _  ⟨n, default, []⟩ s) blacklist
        let nc := node.parents.foldl (fun s n => @List.orderedEraseOrLeave _ ⟨pDAGnode.lbeq⟩ R _ ⟨n, default, []⟩  s) candidates
        go nc nb more
      else
        let nb := node.parents.foldl (fun s n => @List.orderedInsertOrLeave _ ⟨pDAGnode.lbeq⟩ R _  ⟨n, default, []⟩ s) blacklist
        let nc := node.parents.foldl (fun s n => @List.orderedEraseOrLeave _ ⟨pDAGnode.lbeq⟩ R _ ⟨n, default, []⟩  s) candidates
        go (node :: nc) nb more
  go [] [] d


def DAG.find_sinks (d : DAG α β) : List (DAGnode α β) :=
  List.filter (fun node => node.children.isEmpty) d


def sDAG.find_sinks {store : Type _ → Type _} [ToIdx β store] [Inhabited α] [Inhabited β]
  [Repr (store β)] [Inhabited (store β)] [BEq (store β)] (d : sDAG α β store) : List (sDAGnode α β) :=
  (List.range d.size).foldl
    (fun s i =>
      let node := d.dag.get! i
      if node.children.isEmpty then node :: s else s
    ) []



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

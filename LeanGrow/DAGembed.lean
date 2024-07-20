
import LeanGrow.CExpr
import LeanGrow.DAGstruct
import Batteries.Data.List.Basic
--import Mathlib.Data.List.Alist

open Lean

/-
Idea:
If there are unassigned nodes, assign one and then enter the propagation phase.
In the propagation phase, we take an element of the frontier of assigned nodes, look at its parents and attempt to
assign them. If an assignment is contradictory, we dump this embedding attempt. Otherwise, we add the parents to
the frontier, and delet the node we expanded on.
-/


-- Replace embedding from Hashmap to Array of options of capacity the number of nodes in thm-dag
-- assignement corresponds to setting the entry to `.some image`

#check Array.mkEmpty
-- or initialize as List of .none, then cast to Array via
#check Array.mk

-- Consider
#check_failure AList
-- in `Mathlib.Data.List.AList`, which seems to be in new mathlib version ???????



def merge_if_compatible (embed : Array (Option NodeCst)) (assignOutput : List (Nat × NodeCst)) :
  Option (Array (Option NodeCst)) :=
  dbg_trace s!"Attempting to merge:\n{embed}\n{assignOutput}" ;
  match assignOutput with
  | [] => .some embed
  | (t,l) :: rest =>
      let im := embed.get! t -- thm-nodes start as 0, like array indices, so we're good ?
      match im with
      | .none => merge_if_compatible (embed.set! t l) rest
      | .some i => if i == l then merge_if_compatible embed rest else .none


def embed_next (thm ltx : DAG CExpr Nat) (embedSofar : Array (Option NodeCst)) (todo : Nat × CExpr) : List ((Array (Option NodeCst)) × (List (Nat × CExpr))) :=
  let candidates := ltx.nameDataList.foldl (init := []) fun r (k, v) =>
      dbg_trace s!"CExpr matching :\n{todo.2}\n{v}" ;
      match CExpr.MatchAssign todo.2 v with
      | .none => r
      | .some l => (k,l) :: r
  dbg_trace s!"Expantion candidates (with parent embed): {candidates}"
  candidates.foldl (fun L e =>
    match merge_if_compatible (embedSofar.set! todo.1 (.some ( .ofNode e.1))) e.2 with
    | .none => L
    | .some E => dbg_trace s!"Expantion phase interim embedding: {E}"
        (E, (e.2.map Prod.fst).zip ((e.2.map (fun p => thm.dataName p.1)).reduceOption)) :: L
    ) []


--#exit


def propagate (ltx : DAG CExpr Nat) (embedSofar :  Array (Option NodeCst)) (todo : Nat × CExpr) : Option ((Array (Option NodeCst)) × (List (Nat × CExpr))) :=
  match embedSofar.get! todo.1 with
  | .none => .none
  | .some (.ofCst _) => .some (embedSofar, [])
  | .some (.ofNode im) =>
      match ltx.DataParentsList im with
      | .none => .none
      | .some (ce, ps) =>
          match CExpr.MatchAssign todo.2 ce with
          | .none => .none
          | .some l =>
              let pc := (ps.map (fun p => ltx.dataName p)).reduceOption
              .some ((l.foldl (fun r e => r.set! e.1 e.2) embedSofar), ps.zip pc)

--#exit

partial def matcher (thm ltx : SizedDAG CExpr Nat) : List (Array (Option NodeCst)) :=
  let rec main (thm ltx : DAG CExpr Nat) (embedSofar :  Array (Option NodeCst)) (unassignedNodes : List (Nat × CExpr)) (assignedFrontier : List (Nat × CExpr)) : List ( Array (Option NodeCst)) :=
    match assignedFrontier with
    | [] => dbg_trace s!"Empty frontier encountered for embed {embedSofar}"
        match unassignedNodes with
        | [] => dbg_trace "Returning embeding" ;
            [embedSofar]
        | n :: l =>
          match n.2 with
          | .wrapInst _ => main thm ltx embedSofar l [] -- skip instances
          | _ =>  dbg_trace s!"Expaning on {n}"
                  let L := embed_next thm ltx embedSofar n
                  dbg_trace s!"Expansion options: {L.map (fun c => c.1)}"
                  --if L empty, keep going on l : cases of an implicit param not found for example
                  match L with
                  | [] =>   match n.2 with
                            | .sort Level.zero => [] -- couldn't embed the property → halt
                                -- might be bad idea, as some terms also depend on proofs such as List.get
                                -- maybe don't halt until done, then discard if non-instances aren't *all* assigned
                                -- Note : skipping implicit args is risky, since so thms have all implicit hyps, which should be infered from goal ... (kind of a bad design idea)
                            | .sort _ =>
                                dbg_trace "Proceeding, since we hope to assing type later"
                                main thm ltx embedSofar l [] -- is probably an implicit type, which is a constant (like ℕ) which we'll find durring the propagation phase
                                -- maybe, if we order nodes to embed so as to have sinks first, this part
                                -- inst't necessary as the nodes assigned to constants will already be asigned
                            | _ => [] -- coudn't embed a concrete object → halt
                  | _ => (L.map (fun (embed, front) => main thm ltx embed l front)).join
    | n :: l =>
        dbg_trace "Entering propagation for assigned {n.1} in assogned frontier"
        match propagate ltx embedSofar  n with
        | .none => dbg_trace "Propagation failed" ;
            []
        | .some (emb, toFront) => dbg_trace s!"Propagation succeded.\nCurrent embedding: {emb}\nCurrent unassigned: {(n :: toFront).foldl (fun r e => r.erase e) unassignedNodes}\nCurrent front: {(List.union (toFront) l)}\ntrace: {toFront}"
                main thm ltx emb ((n :: toFront).foldl (fun r e => r.erase e) unassignedNodes) (List.union toFront l) -- no duplicates

  dbg_trace "Running main matcher"
  main thm.dag ltx.dag (List.replicate thm.size .none).toArray (thm.nameDataList) []



import LeanGrow.F.Utils.DAG.Query
import LeanGrow.F.Data.Unification.CExprMatch

#check 1

-- return partial embeedings too, this time ; this time, handle instances differently 8maybe report them as missing args, but distinct from actual missing args)





def merge_if_compatible_A (embed : Array (Option NodeExpr)) (assignOutput : Array (Nat × NodeExpr)) :
  Option (Array (Option NodeExpr)) :=
    assignOutput.foldl
      (fun A (t,l) =>
        match A with
        | .some a =>
            let im := embed.get! t
            match im with
            | .none => .some (a.set! t l)
            | .some i => if i == l then .some a else .none
        | _ => .none
        )
      (.some embed)


def merge_if_compatible (embed : Array (Option EmbedData)) (assignOutput : List (Nat × NodeExpr)) :
  Option (Array (Option EmbedData)) :=
    match assignOutput with
    | [] => .some embed
    | (t,l) :: rest =>
        let im := embed.get! t
        match im with
        | .none => merge_if_compatible (embed.set! t l) rest
        | .some i => if i == l then merge_if_compatible embed rest else .none
                    -- do efficient == here for EmbedData ??



def pDAG.embed_next (thm_data  : Array EmbedData) (ltx_L : List (Nat × CExpr × List Nat))
  -- actually, ltx_l should be a structure from Search (discrimi tree) ? should make search for nex embed easier then trying all options
  (embedSofar : Array (Option NodeExpr)) (todo_idx : Nat) (todo_data : EmbedData) :
  List ((Array (Option NodeExpr)) × (List (Nat × NodeExpr))) :=
  let candidates := ltx_L.foldl (init := []) (fun r (k, v) =>
      match CExpr.MatchAssignLFF todo_data.cexpr v.1 with
      | .none => r
      | .some l => (k,l) :: r
      )
  candidates.foldl (fun L e =>
    match merge_if_compatible embedSofar ((todo_idx , ( .ofNode e.1)) :: e.2) with
    | .none => L
    | .some E =>
        (E, (e.2.map Prod.fst).zip ((e.2.map (fun p => thm.dataName p.1)).reduceOption)) :: L
    ) []


#check Array.foldl



#check Array.set!












/-
*Notes*

- Theorems like `List.get!` may apply, even if the instance they require (here `Inhabited`),
  may not be among the ltx, nor may it be derived from any sort of propagation. For example,
  if we have `(l : List Int)` and `(i : Nat)`, then `α := Int` can be obtained from propagation,
  but `Inhabited Int` will require instance synthesis.

- We shouldn't skip instance assignement as a default. If grow is run on a query where say,
  an `Inhabited` is an actual assumption given by the user, then we can assign instances.

- `(l : List α) (i : Nat) (h₁ : i < l.length) (h₂ : l.get ⟨i,h₁⟩ = 42)`

-/

#check List.get!

#check List.get

#exit

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
  --dbg_trace s!"Attempting to merge:\n{embed}\n{assignOutput}" ;
  match assignOutput with
  | [] => .some embed
  | (t,l) :: rest =>
      let im := embed.get! t -- thm-nodes start as 0, like array indices, so we're good ?
      match im with
      | .none => merge_if_compatible (embed.set! t l) rest
      | .some i => if i == l then merge_if_compatible embed rest else .none

-- can't be bothered to show decidable eq
def custom_dedup (l : List (Nat × NodeCst)) : List (Nat × NodeCst) :=
    l.foldr (fun x IH => if ∀ y ∈ IH,  !(x == y) then x :: IH else IH) []

--#exit

def embed_next (thm ltx : DAG CExpr Nat) (embedSofar : Array (Option NodeCst)) (todo : Nat × CExpr) : List ((Array (Option NodeCst)) × (List (Nat × CExpr))) :=
  let candidates' := ltx.nameDataList.foldl (init := []) fun r (k, v) =>
      --dbg_trace s!"CExpr matching :\n{todo.2}\n{v}" ;
      match CExpr.MatchAssign todo.2 v with
      | .none => r
      | .some l => (k,l) :: r
  let candidates := candidates'.map (fun p => (p.1, custom_dedup p.2)) -- added custom_dedup in an attempt to fix bug, but didn't, so investigate whether to keep, for performance
  --dbg_trace s!"Expantion candidates (with parent embed): {candidates}"
  candidates.foldl (fun L e =>
    match merge_if_compatible (embedSofar.set! todo.1 (.some ( .ofNode e.1))) e.2 with
    | .none => L
    | .some E => --dbg_trace s!"Expantion phase interim embedding: {E}"
        (E, (e.2.map Prod.fst).zip ((e.2.map (fun p => thm.dataName p.1)).reduceOption)) :: L
    ) []


--#exit


def propagate (ltx : DAG CExpr Nat) (embedSofar :  Array (Option NodeCst)) (todo : Nat × CExpr) : Option ((Array (Option NodeCst)) × (List (Nat × CExpr))) :=
  match embedSofar.get! todo.1 with
  | .none => .none
  | .some (.ofCst _) =>
        --dbg_trace "Propagiting constant : do nothing"
        .some (embedSofar, [])
  | .some (.ofNode im) =>
      --dbg_trace "Propagiting node"
      match ltx.DataParentsList im with
      | .none => .none
      | .some (ce, ps) =>
          --dbg_trace s!"CExpr: {ce} ; Parents: {ps}\nRunning match assign"
          match CExpr.MatchAssign todo.2 ce with
          | .none => .none
          | .some l =>
              --dbg_trace s!"Match result updates : {l}"
              match merge_if_compatible embedSofar l with
              | .none => .none
              | .some enew => --dbg_trace s!"test! {enew}"
                    let help := (l.map (fun (i,x) => match x with | .ofCst c => .some (i,c) | .ofNode d => (match ltx.dataName d with | .none => .none | .some stuff => (i,stuff)))).reduceOption
                    .some (enew,help)
                    -- let pc := (ps.map (fun p => ltx.dataName p)).reduceOption
                    -- .some ((l.foldl (fun r e => r.set! e.1 e.2) embedSofar), ps.zip pc)

--#exit

partial def matcher (thm ltx : SizedDAG CExpr Nat) : List (Array (Option NodeCst)) :=
  let rec main (thm ltx : DAG CExpr Nat) (embedSofar :  Array (Option NodeCst)) (unassignedNodes : List (Nat × CExpr)) (assignedFrontier : List (Nat × CExpr)) : List ( Array (Option NodeCst)) :=
    match assignedFrontier with
    | [] => --dbg_trace s!"Empty frontier encountered for embed {embedSofar}"
        match unassignedNodes with
        | [] => --dbg_trace "Returning embeding" ;
            [embedSofar]
        | n :: l =>
          match n.2 with
          | .wrapInst _ => main thm ltx embedSofar l [] -- skip instances
          | _ =>  --dbg_trace s!"Expaning on {n}"
                  let L := embed_next thm ltx embedSofar n
                  --dbg_trace s!"Expansion options: {L.map (fun c => s!"{c.1} with front {c.2}")}"
                  --if L empty, keep going on l : cases of an implicit param not found for example
                  match L with
                  | [] =>   match n.2 with
                            | .sort Level.zero => [] -- couldn't embed the property → halt
                                -- might be bad idea, as some terms also depend on proofs such as List.get
                                -- maybe don't halt until done, then discard if non-instances aren't *all* assigned
                                -- Note : skipping implicit args is risky, since so thms have all implicit hyps, which should be infered from goal ... (kind of a bad design idea)
                            | .sort _ =>
                                --dbg_trace "Proceeding, since we hope to assing type later"
                                main thm ltx embedSofar l [] -- is probably an implicit type, which is a constant (like ℕ) which we'll find durring the propagation phase
                                -- maybe, if we order nodes to embed so as to have sinks first, this part
                                -- inst't necessary as the nodes assigned to constants will already be asigned
                            | _ => [] -- coudn't embed a concrete object → halt
                  | _ => (L.map (fun (embed, front) => main thm ltx embed (l.filter (fun x => !(front.contains x))) front)).join
    | n :: l =>
        --dbg_trace "Entering propagation for assigned {n.1} in assogned frontier"
        match propagate ltx embedSofar  n with
        | .none => --dbg_trace "Propagation failed" ;
            []
        | .some (emb, toFront) => --dbg_trace s!"Propagation succeded.\nCurrent embedding: {emb}\nCurrent unassigned: {(n :: toFront).foldl (fun r e => r.filter (fun x => !(x == e))) unassignedNodes}\nCurrent front: {(List.union (toFront) l)}\ntrace: {toFront}"
                main thm ltx emb ((n :: toFront).foldl (fun r e => r.filter (fun x => !(x == e))) unassignedNodes) (List.union toFront l) -- no duplicates

  --dbg_trace "Running main matcher"
  main thm.dag ltx.dag (List.replicate thm.size .none).toArray (thm.nameDataList) []

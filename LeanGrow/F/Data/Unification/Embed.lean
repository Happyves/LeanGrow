

import LeanGrow.F.Utils.DAG.Query
import LeanGrow.F.Data.Unification.CExprMatch
import Mathlib.Data.List.Sort
import LeanGrow.F.Utils.List




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


def merge_if_compatible (embed : Array (Option NodeExpr)) (assignOutput : List (Nat × NodeExpr)) :
  Option (Array (Option NodeExpr) × List Nat) :=
  let rec go (embed : Array (Option NodeExpr)) (toPropagate : List Nat) : List (Nat × NodeExpr) → Option (Array (Option NodeExpr) × List Nat)
    | [] => .some (embed, toPropagate)
    | (t,l) :: rest =>
        let im := embed.get! t
        match im with
        | .none => go (embed.set! t l) (t :: toPropagate) rest
        | .some i => if i == l then go embed toPropagate rest else .none
  go embed [] assignOutput


def embed_next_raw (ltx : List (Nat × CExpr)) -- sofar, parents not needed
  -- actually, ltx_l should be a structure from Search (discrimi tree) ? should make search for nex embed easier then trying all options
  (embedSofar : Array (Option NodeExpr)) (todo_idx : Nat) (todo_data : EmbedData) :
  List ((Array (Option NodeExpr)) × (List Nat)) :=
  -- find matchinf ltx expressions
  let candidates := ltx.foldl (init := []) (fun r (k, v) =>
      match CExpr.MatchAssignLFF todo_data.cexpr v with
      | .none => r
      | .some l => (k,l) :: r
      )
  -- find those that are compatible with the embedding so far
  (candidates.map (fun (e, tp) => merge_if_compatible (embedSofar.set! todo_idx (.some (.ofNode e))) tp)).reduceOption




def propagate_raw (ltx : List (Nat × CExpr)) -- sofar, parents not needed
  (embedSofar :  Array (Option NodeExpr)) (todo_idx : Nat) (todo_thm_type : CExpr) : Option ((Array (Option NodeExpr)) × (List Nat)) :=
  match embedSofar.get! todo_idx with
  | .none => .none
  | .some (.ofCExpr _) =>
        .some (embedSofar, [])
  | .some (.ofNode im) =>
      match ltx.find? (fun x => x.1 == im) with
      | .none => .none
      | .some (_, ce) =>
          match CExpr.MatchAssignLFF todo_thm_type ce with
          | .none => .none
          | .some l => merge_if_compatible embedSofar l


structure EmbedStruct where
  embed : Array (Option NodeExpr)
  unassigned_instances : List Nat
deriving BEq, Inhabited, Repr


partial def full_matcher_raw (thm_data : Array EmbedData) (thm_order : Array Nat) (ltx : List (Nat × CExpr)) : List EmbedStruct :=
  let rec main (embedSofar :  Array (Option NodeExpr)) (instances : List Nat) (unassignedNodes : List Nat) (assignedFrontier : List Nat) : List EmbedStruct :=
    match assignedFrontier with
    | [] =>
        match unassignedNodes with
        | [] => [⟨embedSofar,instances⟩]
        | n :: l =>
          let nd := thm_data.get! n
          match nd with
          | .inst _ _ =>
                let L := embed_next_raw ltx embedSofar n nd
                match L with
                | [] => main embedSofar (n :: instances) l assignedFrontier
                        -- if we fail to embed an intance, we proceed
                | _ => (L.map (fun (embed, front) => main embed instances l front)).join
          | .nonInst _ _ =>
                let L := embed_next_raw ltx embedSofar n nd
                (L.map (fun (embed, front) => main embed instances l front)).join
    | n :: l =>
        let nd := thm_data.get! n
        match propagate_raw ltx embedSofar n nd.cexpr with
        | .none => []
        | .some (emb, toFront) => main emb instances (unassignedNodes.filter (fun x => x ∈ (n :: toFront))) (List.union toFront l) -- no duplicates
  main (Array.mkArray thm_data.size .none) [] thm_order.toList []




private structure Data where
  embedSofar :  Array (Option NodeExpr)
  instances : List Nat
  unassignedNodes : List Nat
  assignedFrontier : List Nat

partial def full_matcher_rawF (thm_data : Array EmbedData) (thm_order : Array Nat) (ltx : List (Nat × CExpr)) : List EmbedStruct :=
  let rec main (todo : List Data) (done : List EmbedStruct) : List EmbedStruct :=
    match todo with
    | [] => done
    | ⟨embedSofar, instances, unassignedNodes, assignedFrontier⟩ :: more =>
        match assignedFrontier with
        | [] =>
            match unassignedNodes with
            | [] => main more (⟨embedSofar,instances⟩ :: done)
            | n :: l =>
              let nd := thm_data.get! n
              match nd with
              | .inst _ _ =>
                    let L := embed_next_raw ltx embedSofar n nd
                    match L with
                    | [] => main (⟨embedSofar, (n :: instances), l, assignedFrontier⟩ :: more) done
                            -- if we fail to embed an instance, we proceed
                    | _ =>  let add := L.map (fun (embed, front) => ⟨embed, instances, l, front.mergeSort (· ≤ ·)⟩)
                            main (add ++ more) done
              | .nonInst _ _ =>
                    let L := embed_next_raw ltx embedSofar n nd
                    let add := L.map (fun (embed, front) => ⟨embed, instances, l, front.mergeSort (· ≤ ·)⟩ )
                    main (add ++ more) done
        | n :: l =>
            let nd := thm_data.get! n
            match propagate_raw ltx embedSofar n nd.cexpr with
            | .none => main more done
            | .some (emb, toFront) => main (⟨emb, instances, (unassignedNodes.filter (fun x => x ∈ (n :: toFront))), (toFront.foldl (fun x y => List.orderedInsertOrLeave (· ≤ ·) y x) l)⟩ :: more) done  -- no duplicates
      main [⟨(Array.mkArray thm_data.size .none), [], thm_order.toList, []⟩] []



structure PartialEmbedStruct where
  embed : Array (Option NodeExpr)
  unassigned_hyps : List Nat
  unassigned_instances : List Nat
deriving BEq, Inhabited, Repr


private structure PartialData where
  embedSofar :  Array (Option NodeExpr)
  instances : List Nat
  unembedable : List Nat
  unassignedNodes : List Nat
  assignedFrontier : List Nat

#exit

partial def partial_matcher_rawF (thm_data : Array EmbedData) (thm_order : Array Nat) (ltx : List (Nat × CExpr)) : List PartialEmbedStruct :=
  let rec main (todo : List PartialData) (done : List PartialEmbedStruct) : List PartialEmbedStruct :=
    match todo with
    | [] => done
    | ⟨embedSofar, instances, unembedable, unassignedNodes, assignedFrontier⟩ :: more =>
        match assignedFrontier with
        | [] =>
            match unassignedNodes with
            | [] => main more (⟨embedSofar,instances,unembedable⟩ :: done)
            | n :: l =>
              let nd := thm_data.get! n
              match nd with
              | .inst _ _ =>
                    let L := embed_next_raw ltx embedSofar n nd
                    match L with
                    | [] => main (⟨embedSofar, (n :: instances), unembedable, l, assignedFrontier⟩ :: more) done
                            -- if we fail to embed an instance, we proceed
                    | _ =>  let add := L.map (fun (embed, front) => ⟨embed, instances, unembedable, l, front.mergeSort (· ≤ ·)⟩)
                            main (add ++ more) done
              | .nonInst _ _ =>
                    let L := embed_next_raw ltx embedSofar n nd
                    match L with
                    | [] => main (⟨embedSofar, instances, (n :: unembedable), l, assignedFrontier⟩ :: more) done
                            -- if we fail to embed an instance, we proceed
                    | _ =>  let add := L.map (fun (embed, front) => ⟨embed, instances, unembedable, l, front.mergeSort (· ≤ ·)⟩)
                            main (add ++ more) done
        | n :: l =>
            let nd := thm_data.get! n
            match propagate_raw ltx embedSofar n nd.cexpr with
            | .none => main more done
            | .some (emb, toFront) => main (⟨emb, instances, ((n :: toFront).foldl (fun r e => r.erase e) unassignedNodes), (toFront.foldl (fun x y => List.orderedInsertOrLeave (· ≤ ·) y x) l)⟩ :: more) done  -- no duplicates
      main [⟨(Array.mkArray thm_data.size .none), [], thm_order.toList, []⟩] []


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

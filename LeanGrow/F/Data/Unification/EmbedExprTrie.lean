

import LeanGrow.F.Utils.ExprTrie.Build
import LeanGrow.F.Data.Unification.CExprMatch
import Mathlib.Data.List.Sort
import LeanGrow.F.Utils.List
import LeanGrow.F.Utils.Tracing






def merge_if_compatible (embed : Array (Option CExpr)) (assignOutput : List (Nat × CExpr)) :
  Option (Array (Option CExpr) × List (Nat × CExpr)) :=
  let rec go (embed : Array (Option CExpr)) (toPropagate : List (Nat × CExpr)) : List (Nat × CExpr) → Option (Array (Option CExpr) × List (Nat × CExpr))
    | [] => .some (embed, toPropagate)
    | (t,l) :: rest =>
        let im := embed.get! t
        match im with
        | .none => go (embed.set! t l) ((t,l) :: toPropagate) rest
        | .some i => if i == l then go embed toPropagate rest else .none
  with_lTrace [TraceFlags.zero] in
  let res := go embed [] assignOutput
  lTrace TraceFlags.zero & s!"Running merge_if_compatible.\nOn embed:{repr embed}\nOn assignOuput:{repr assignOutput}\nReturn:{repr res}\n\n" & res



def embed_next_smooth (ltx : CExprTrie Nat)
  (embedSofar : Array (Option CExpr)) (todo_idx : Nat) (todo_data : EmbedData) :
  List ((Array (Option CExpr)) × (List (Nat × CExpr))) :=
  with_lTrace [TraceFlags.zero, .one] in
  -- find matching ltx expressions
  let candidates := CExprTrie.unify_reconstruct (· ≤ ·) (ltx.unify_candidates (· ≤ ·) todo_data.cexpr)
  -- find those that are compatible with the embedding so far
  let res := ((lTrace TraceFlags.zero & s!"Intermediate candidates in embed_next_raw: {repr candidates}" & candidates).map
      (fun (e, tp) => merge_if_compatible (embedSofar.set! todo_idx (.some (.node e (.ofBvar 42)))) tp)).reduceOption
  lTrace TraceFlags.one & s!"Ran embed_next_raw.\nOn embed:{repr embedSofar}\nOn todo id {todo_idx} with cexpr {repr todo_data.cexpr}\nReturn:{repr res}\n\n" & res
-- **Big Pitfall** the `(.ofBvar 42)` might come back to haunt me at some point!!!



def propagate_smooth (ltx : CExprTrie Nat)
  (embedSofar :  Array (Option CExpr)) (todo_idx : Nat) (todo_thm_type : CExpr) : Option ((Array (Option CExpr)) × (List (Nat × CExpr))) :=
  let res :=
    match embedSofar.get! todo_idx with
    | .none => .none
    | .some (.node im _) =>
        match ltx.find? (fun x => x.1 == im) with
        | .none => .none
        | .some (_, ce) =>
            match CExpr.MatchAssignLFF todo_thm_type ce with
            | .none => .none
            | .some l => merge_if_compatible embedSofar l
    | .some _ =>
          .some (embedSofar, [])
  with_lTrace [TraceFlags.zero] in
  lTrace TraceFlags.zero & s!"Ran embed_next_raw.\nOn embed:{repr embedSofar}\nOn todo id {todo_idx} with cexpr {repr todo_thm_type}\nReturn:{repr res}\n\n" & res

#exit

structure EmbedStruct where
  embed : Array (Option NodeExpr)
  unassigned_instances : List Nat
deriving BEq, Inhabited, Repr


partial def full_matcher_raw (thm_data : Array EmbedData) (thm_order : Array Nat) (ltx : List (Nat × CExpr)) : List EmbedStruct :=
  with_lTrace [TraceFlags.zero, .one, .two] in
  let rec main (embedSofar :  Array (Option NodeExpr)) (instances : List Nat) (unassignedNodes : List Nat) (assignedFrontier : List Nat) : List EmbedStruct :=
    lTrace TraceFlags.two & s!"Call to main with {repr embedSofar}, {instances}, {unassignedNodes}, {assignedFrontier}.\n\n" &
    match assignedFrontier with
    | [] =>
        match unassignedNodes with
        | [] =>
            let res := [⟨embedSofar,instances⟩]
            lTrace TraceFlags.zero & s!"Empty frontier and no unassigned nodes. Returning:\n{repr res}\n\n" & res
        | n :: l =>
          let nd := thm_data.get! n
          match nd with
          | .inst _ _ =>
                let L := embed_next_raw ltx embedSofar n nd
                match L with
                | [] => lTrace TraceFlags.zero & s!"Empty frontier. Tried emebedding {repr n}\nFailed to embed instance. Take note of it and proceed.\n\n" & main embedSofar (n :: instances) l assignedFrontier
                        -- if we fail to embed an intance, we proceed
                | _ => lTrace TraceFlags.zero & s!"Empty frontier. Tried emebedding {repr n}\nSuccess!! Proceed on each possibility\n\n" &(L.map (fun (embed, front) => main embed instances l front)).join
          | .nonInst _ _ =>
                let L := embed_next_raw ltx embedSofar n nd
                lTrace TraceFlags.zero & s!"Empty frontier. Tried to emebedding {repr n}" & (L.map (fun (embed, front) => main embed instances l front)).join
    | n :: l =>
        let nd := thm_data.get! n
        lTrace TraceFlags.one & s!"Trying to propagate {n} of cexpr {repr nd}.\n\n" &
        match propagate_raw ltx embedSofar n nd.cexpr with
        | .none => lTrace TraceFlags.zero & s!"Propagation failed, returning [].\n\n" & []
        | .some (emb, toFront) => lTrace TraceFlags.zero & s!"Propagation succeded!" & main emb instances (unassignedNodes.filter (fun x => x ∈ (n :: toFront))) (List.union toFront l) -- no duplicates
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



partial def partial_matcher_rawF (thm_data : Array EmbedData) (thm_order : Array Nat) (ltx : List (Nat × CExpr)) : List PartialEmbedStruct :=
  let rec main (todo : List PartialData) (propagationFlag : Option (Nat × Nat × PartialData)) (done : List PartialEmbedStruct) : List PartialEmbedStruct :=
    match todo with
    | [] => done
    | ⟨embedSofar, instances, unembedable, unassignedNodes, assignedFrontier⟩ :: more =>
        match assignedFrontier with
        | [] =>
            match unassignedNodes with
            | [] => main more .none (⟨embedSofar,instances,unembedable⟩ :: done)
            | n :: l =>
              let nd := thm_data.get! n
              match nd with
              | .inst _ _ =>
                    let L := embed_next_raw ltx embedSofar n nd
                    match L with
                    | [] => main (⟨embedSofar, (n :: instances), unembedable, l, assignedFrontier⟩ :: more) .none done
                            -- if we fail to embed an instance, we proceed
                    | _ =>  let add := L.map (fun (embed, front) => ⟨embed, instances, unembedable, l, front.mergeSort (· ≤ ·)⟩)
                            main (add ++ more) (.some (n, add.length, ⟨embedSofar, instances, unembedable, l, []⟩)) done
              | .nonInst _ _ =>
                    let L := embed_next_raw ltx embedSofar n nd
                    match L with
                    | [] => main (⟨embedSofar, instances, (n :: unembedable), l, assignedFrontier⟩ :: more) .none done
                            -- if we fail to embed, we take note of it and proceed
                    | _ =>  let add := L.map (fun (embed, front) => ⟨embed, instances, unembedable, l, front.mergeSort (· ≤ ·)⟩)
                            main (add ++ more) (.some (n, add.length, ⟨embedSofar, instances, unembedable, l, []⟩)) done
        | n :: l =>
            let nd := thm_data.get! n
            match propagate_raw ltx embedSofar n nd.cexpr with
            | .none =>
                match propagationFlag with
                | .none => main more .none done -- shouldn't occure durring propagation phase
                | .some (m,0, ⟨ini_embedSofar, ini_instances, ini_unembedable, ini_unassignedNodes, ini_assignedFrontier⟩) =>
                      main (⟨ini_embedSofar, ini_instances, m :: ini_unembedable, ini_unassignedNodes, ini_assignedFrontier⟩ :: more) .none done
                | .some (m,c+1,ini) =>
                      main more (m,c,ini) done
            | .some (emb, toFront) => main (⟨emb, instances, unembedable, (unassignedNodes.filter (fun x => x ∈ (n :: toFront))), (toFront.foldl (fun x y => List.orderedInsertOrLeave (· ≤ ·) y x) l)⟩ :: more) propagationFlag done
      main [⟨(Array.mkArray thm_data.size .none), [], [], thm_order.toList, []⟩] .none []




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

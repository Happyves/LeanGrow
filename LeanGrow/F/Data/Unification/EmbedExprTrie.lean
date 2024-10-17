

import LeanGrow.F.Utils.ExprTrie.Build
import LeanGrow.F.Data.Unification.CExprMatch
import Mathlib.Data.List.Sort
import LeanGrow.F.Utils.List
import LeanGrow.F.Utils.Tracing






def merge_if_compatible (embed : Array (Option NodeExpr)) (assignOutput : List (Nat × NodeExpr)) :
  Option (Array (Option NodeExpr) × List Nat) :=
  let rec go (embed : Array (Option NodeExpr)) (toPropagate : List Nat) : List (Nat × NodeExpr) → Option (Array (Option NodeExpr) × List Nat)
    | [] => .some (embed, toPropagate)
    | (t,l) :: rest =>
        let im := embed.get! t
        match im with
        | .none => go (embed.set! t l) (t :: toPropagate) rest
        | .some i => if i == l then go embed toPropagate rest else .none
  with_lTrace [TraceFlags.zero] in
  let res := go embed [] assignOutput
  lTrace TraceFlags.zero & s!"Running merge_if_compatible.\nOn embed:{repr embed}\nOn assignOuput:{repr assignOutput}\nReturn:{repr res}\n\n" & res


def CExpr.toNodeExpr : CExpr → NodeExpr
| .lnode i _ t => .ofLNode i t
| .gnode i _ => .ofGNode i
| ce => .ofCExpr ce


def embed_next_smooth (ltx : CExprTrie Nat)
  (embedSofar : Array (Option NodeExpr)) (todo_idx : Nat) (todo_data : EmbedData) :
  List ((Array (Option NodeExpr)) × (List Nat)) :=
  with_lTrace [TraceFlags.zero, .one] in
  let candidates := CExprTrie.unify_reconstruct (· ≤ ·) (ltx.unify_candidates (· ≤ ·) todo_data.cexpr)
  match candidates with
  | [] => -- maybe merge this with `unify_candidates` somehow ?
      let cst_embed := ltx.find? todo_data.cexpr (· ≤ ·)
      cst_embed.map (fun n => ((embedSofar.set! todo_idx (.some (.ofGNode n))), []))
  | _ =>
      let res := ((lTrace TraceFlags.zero & s!"Intermediate candidates in embed_next_raw: {repr candidates}" & candidates).map
          (fun (e, tp) => merge_if_compatible (embedSofar.set! todo_idx (.some (.ofGNode e))) (tp.map (fun (n,ce) => (n, ce.toNodeExpr))))).reduceOption
      lTrace TraceFlags.one & s!"Ran embed_next_raw.\nOn embed:{repr embedSofar}\nOn todo id {todo_idx} with cexpr {repr todo_data.cexpr}\nReturn:{repr res}\n\n" & res


def propagate_smooth (ltx : List (Array CExpr)) (ltx_handler : Nat → (Nat × Nat))
  (embedSofar :  Array (Option NodeExpr)) (todo_idx : Nat) (todo_thm_type : CExpr) : Option ((Array (Option NodeExpr)) × (List Nat)) :=
  let res :=
    match embedSofar.get! todo_idx with
    | .none => .none
    | .some (.ofGNode im) =>
        let (page, idx) := ltx_handler im
        match ltx.get? page with
        | .none => .none
        | .some A =>
            let ce := A.get! idx
            match CExpr.MatchAssignLFF todo_thm_type ce with
            | .none => .none
            | .some l => merge_if_compatible embedSofar l
    | .some _ =>
          .some (embedSofar, [])
  with_lTrace [TraceFlags.zero] in
  lTrace TraceFlags.zero & s!"Ran embed_next_raw.\nOn embed:{repr embedSofar}\nOn todo id {todo_idx} with cexpr {repr todo_thm_type}\nReturn:{repr res}\n\n" & res



structure EmbedStruct where
  embed : Array (Option NodeExpr)
  unassigned_instances : List Nat
deriving BEq, Inhabited, Repr


private structure Data where
  embedSofar :  Array (Option NodeExpr)
  instances : List Nat
  unassignedNodes : List Nat
  assignedFrontier : List Nat

partial def full_matcher_smoothF (thm_data : Array EmbedData) (thm_order : Array Nat)
  (ltx_cexpr_idx : CExprTrie Nat) (ltx_idx_cexpr : List (Array CExpr)) (ltx_handler : Nat → (Nat × Nat)) : List EmbedStruct :=
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
              | .inst _ _ _ =>
                    let L := embed_next_smooth ltx_cexpr_idx embedSofar n nd
                    match L with
                    | [] => main (⟨embedSofar, (n :: instances), l, assignedFrontier⟩ :: more) done
                            -- if we fail to embed an instance, we proceed
                    | _ =>  let add := L.map (fun (embed, front) => ⟨embed, instances, l, front.mergeSort (· ≤ ·)⟩)
                            main (add ++ more) done
              | .nonInst _ _ _ =>
                    let L := embed_next_smooth ltx_cexpr_idx embedSofar n nd
                    let add := L.map (fun (embed, front) => ⟨embed, instances, l, front.mergeSort (· ≤ ·)⟩ )
                    main (add ++ more) done
        | n :: l =>
            let nd := thm_data.get! n
            match propagate_smooth ltx_idx_cexpr ltx_handler embedSofar n nd.cexpr with
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



partial def partial_matcher_smoothF (thm_data : Array EmbedData) (thm_order : Array Nat)
  (ltx_cexpr_idx : CExprTrie Nat) (ltx_idx_cexpr : List (Array CExpr)) (ltx_handler : Nat → (Nat × Nat)) : List PartialEmbedStruct :=
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
              | .inst _ _ _ =>
                    let L := embed_next_smooth ltx_cexpr_idx embedSofar n nd
                    match L with
                    | [] => main (⟨embedSofar, (n :: instances), unembedable, l, assignedFrontier⟩ :: more) .none done
                            -- if we fail to embed an instance, we proceed
                    | _ =>  let add := L.map (fun (embed, front) => ⟨embed, instances, unembedable, l, front.mergeSort (· ≤ ·)⟩)
                            main (add ++ more) (.some (n, add.length, ⟨embedSofar, instances, unembedable, l, []⟩)) done
              | .nonInst _ _ _ =>
                    let L := embed_next_smooth ltx_cexpr_idx embedSofar n nd
                    match L with
                    | [] => main (⟨embedSofar, instances, (n :: unembedable), l, assignedFrontier⟩ :: more) .none done
                            -- if we fail to embed, we take note of it and proceed
                    | _ =>  let add := L.map (fun (embed, front) => ⟨embed, instances, unembedable, l, front.mergeSort (· ≤ ·)⟩)
                            main (add ++ more) (.some (n, add.length, ⟨embedSofar, instances, unembedable, l, []⟩)) done
        | n :: l =>
            let nd := thm_data.get! n
            match propagate_smooth ltx_idx_cexpr ltx_handler embedSofar n nd.cexpr with
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

- Propagation is necessary, "well-foundedness" of the ltx isn't enough. For instance, the sinks
  of `le_trans` would embed in `(x : 1 ≤ 2) (y : 3 ≤ 4)`, but failure of propagation is what
  causes us to realize we can't embed! The first propagtion of the first sink should however
  always succeed in a "well-foundedness" of the ltx.

- `(l : List α) (i : Nat) (h₁ : i < l.length) (h₂ : l.get ⟨i,h₁⟩ = 42)` no idea why I added this

-/

#check List.get!

#check List.get

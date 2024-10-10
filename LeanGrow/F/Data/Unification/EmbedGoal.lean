

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


def propagate_smooth (ltx : List (Array CExpr)) (ltx_handler : Nat → (Nat × Nat))
  (embedSofar :  Array (Option NodeExpr)) (todo_idx : Nat) (todo_thm_type : CExpr) : Option ((Array (Option NodeExpr)) × (List Nat)) :=
  let res :=
    match embedSofar.get! todo_idx with
    | .none => .none
    | .some (.ofNode im) =>
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



partial def match_goal (thm_data : Array EmbedData) (ltx_idx_cexpr : List (Array CExpr)) (ltx_handler : Nat → (Nat × Nat))
  (thm_hyp_num : Nat) (thm_goal real_goal : CExpr) : Option (Array (Option NodeExpr)) :=
    let rec gop (embed : Array (Option NodeExpr)) : List Nat → Option (Array (Option NodeExpr))
      | [] => .some embed
      | n :: l =>
            let nd := thm_data.get! n
            match propagate_smooth ltx_idx_cexpr ltx_handler embed n nd.cexpr with
            | .none => .none
            | .some (emb, toFront) => gop emb (toFront ++ l)
    match CExpr.MatchAssignLFF thm_goal real_goal with -- real_goal is a cexpr wrt. ltx
    | .none => .none
    | .some l =>
          let emb := l.foldl (fun A (i,v) => (A.set! i (Option.some v))) (Array.mkArray thm_hyp_num .none)
          gop emb (l.map Prod.fst)

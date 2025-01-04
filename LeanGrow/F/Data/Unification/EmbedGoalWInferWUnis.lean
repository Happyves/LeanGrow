

import LeanGrow.F.Utils.ExprTrie.Build
import LeanGrow.F.Data.Unification.CExprMatch
import Mathlib.Data.List.Sort
import LeanGrow.F.Utils.List
import LeanGrow.F.Utils.Tracing
import LeanGrow.F.Utils.ExprTrie.Build
import LeanGrow.F.Data.CExpr.ReduceInferMuggle.Control





def merge_if_compatibleG (embed : Array (Option CExpr)) (assignOutput : List (Nat × CExpr)) :
  Option (Array (Option CExpr) × List Nat) :=
  let rec go (embed : Array (Option CExpr)) (toPropagate : List Nat) : List (Nat × CExpr) → Option (Array (Option CExpr) × List Nat)
    | [] => .some (embed, toPropagate)
    | (t,l) :: rest =>
        let im := embed.get! t
        match im with
        | .none => go (embed.set! t l) (t :: toPropagate) rest
        | .some i => if i == l then go embed toPropagate rest else .none
  with_lTrace [TraceFlags.zero] in
  let res := go embed [] assignOutput
  lTrace TraceFlags.zero & s!"Running merge_if_compatibleG.\nOn embed:{repr embed}\nOn assignOuput:{repr assignOutput}\nReturn:{repr res}\n\n" & res

open Lean

def propagate_goal (fctx : FixCtx)
  (embedSofar :  Array (Option CExpr)) (paramsSofar : List (Name × Level))
  (todo_idx : Nat) (todo_thm_type : CExpr) : Option (((Array (Option CExpr)) × (List Nat)) × List (Name × Level)) :=
  let res :=
    match embedSofar.get! todo_idx with
    | .none => .none
    | .some ce =>
        let cet := CExpr.inferType fctx ce
        match CExpr.MatchAssignLFFCU todo_thm_type cet with
        | .none => .none
        | .some (l,u) =>
              let exp := merge_if_compatibleG embedSofar l
              let us := univsMerge (.some paramsSofar) (.some u)
              match exp, us with
              | .some exp', .some us' => .some (exp',us')
              | _, _ => .none
  with_lTrace TraceFlags.off in
  lTrace TraceFlags.zero & s!"Ran embed_next_raw.\nOn embed:{repr embedSofar}\nOn todo id {todo_idx} with cexpr {repr todo_thm_type}\nReturn:{repr res}\n\n" & res



partial def match_goal (fctx : FixCtx)
  (thm_data : Array EmbedData)
  (thm_hyp_num : Nat) (thm_goal real_goal : CExpr) : Option (Array (Option CExpr)) :=
    let rec gop (embed : Array (Option CExpr)) (paramsSofar : List (Name × Level)) : List Nat → Option (Array (Option CExpr))
      | [] => .some embed
      | n :: l =>
            let nd := thm_data.get! n
            match propagate_goal fctx embed paramsSofar n nd.cexpr with
            | .none => .none
            | .some ((emb, toFront), us) => gop emb us (toFront ++ l)
    with_lTrace TraceFlags.off in
    match CExpr.MatchAssignLFFCU thm_goal real_goal with -- real_goal is a cexpr wrt. ltx
    | .none => .none
    | .some (l, u) =>
          lTrace TraceFlags.zero & s!"Matched thm goal and real goal" &
          let emb := l.foldl (fun A (i,v) => (A.set! i (Option.some v))) (Array.mkArray thm_hyp_num .none)
          gop emb u (l.map Prod.fst)


#exit

/-
↓ should be similar to ↑
thm_goal_trie should be an ExprTrie made of thm types, so that we may
efficiently query which thms apply
-/
partial def match_goal_wCExprTrie (ltx_idx_cexpr : List (Array CExpr)) (ltx_handler : Nat → (Nat × Nat))
  (thm_goal_trie : CExprTrie sorry) (real_goal : CExpr) : Option (Array (Option CExpr)) :=
    let rec gop (embed : Array (Option CExpr)) (thm_data : Array EmbedData) : List Nat → Option (Array (Option CExpr))
      | [] => .some embed
      | n :: l =>
            let nd := thm_data.get! n
            match propagate_goal ltx_idx_cexpr ltx_handler embed n nd.cexpr with
            | .none => .none
            | .some (emb, toFront) => gop emb thm_data (toFront ++ l)
    sorry

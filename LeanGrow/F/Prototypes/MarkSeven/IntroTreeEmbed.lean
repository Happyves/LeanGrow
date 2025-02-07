

import LeanGrow.F.Prototypes.MarkSeven.IntroTree
import LeanGrow.F.Utils.DAG.Query
import LeanGrow.F.Data.Unification.CExprMatch
import Mathlib.Data.List.Sort
import LeanGrow.F.Utils.List
import LeanGrow.F.Utils.Tracing
import LeanGrow.F.Data.CExpr.ReduceInferMuggle.Control





def merge_if_compatible_A (embed : Array (Option CExpr)) (assignOutput : Array (Nat × CExpr)) :
  Option (Array (Option CExpr)) :=
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


def merge_if_compatible (embed : Array (Option CExpr)) (assignOutput : List (Nat × CExpr)) :
  Option (Array (Option CExpr) × List Nat) :=
  let rec go (embed : Array (Option CExpr)) (toPropagate : List Nat) : List (Nat × CExpr) → Option (Array (Option CExpr) × List Nat)
    | [] => .some (embed, toPropagate)
    | (t,l) :: rest =>
        let im := embed.get! t
        match im with
        | .none => go (embed.set! t l) (t :: toPropagate) rest
        | .some i => if i == l then go embed toPropagate rest else .none
  with_lTrace TraceFlags.off in
  let res := go embed [] assignOutput
  lTrace TraceFlags.zero & s!"Running merge_if_compatible.\nOn embed:{repr embed}\nOn assignOuput:{repr assignOutput}\nReturn:{repr res}\n\n" & res


open Lean


structure candidate where
  gnodeIdx : Nat
  toPropa : List (ℕ × CExpr)
  params : List (Name × Level)
  ancestors : List (List (ℕ × CExpr)) -- including own generation
  topGoals : List Nat
  extentions : List IntroTree
deriving Inhabited, Repr, BEq



partial def getEmbCandidates (ltx : IntroTree) (todo : CExpr) : List candidate :=
  let rec go (done : List candidate) : List (IntroTree × List (List (ℕ × CExpr))) →  List candidate
    | [] => done
    | (t,ans) :: ts =>
        match t with
        | .leaf gids lltx =>
              let candidates := lltx.foldl (init := done) (fun r (k, v) =>
                match CExpr.MatchAssignLFFCU todo v with
                | .none => r
                | .some (l,u) => ⟨k,l,u, lltx :: ans,gids,[]⟩ :: r
                )
              go (candidates ++ done) ts
        | .node gids lltx kidsWdirs =>
              let candidates := lltx.foldl (init := done) (fun r (k, v) =>
                match CExpr.MatchAssignLFFCU todo v with
                | .none => r
                | .some (l,u) => ⟨k,l,u, lltx :: ans,gids,kidsWdirs.map Prod.snd⟩ :: r
                )
              go (candidates ++ done) ((kidsWdirs.map (fun (_,x) => (x, lltx :: ans))) ++ ts)
  go [] [(ltx,[])]


structure candidateEmb where
  emb : Array (Option CExpr)
  toPropa : List Nat
  params : List (Name × Level)
  ancestors : List (List (ℕ × CExpr)) -- including own generation
  topGoals : List Nat
  extentions : List IntroTree
deriving Inhabited, Repr, BEq



def embed_next_raw (ltx : IntroTree)
  -- actually, ltx_l should be a structure from Search (discrimi tree) ? should make search for nex embed easier then trying all options
  (embedSofar : Array (Option CExpr)) (paramsSofar : List (Name × Level)) (todo_idx : Nat) (todo_data : EmbedData) :
  List candidateEmb :=
  with_lTrace TraceFlags.off in
  -- find matching ltx expressions
  let candidates := getEmbCandidates ltx todo_data.cexpr
  -- find those that are compatible with the embedding so far
  let res := candidates.foldl (fun sofar ⟨i,tp,p,a,tg,e⟩ =>
    let exp := merge_if_compatible (embedSofar.set! todo_idx (.some (.gnode i (.ofBvar 42)))) tp
    let us := univsMerge (.some paramsSofar) (.some p)
    match exp, us with
    | .some (em, tP), .some us' => ⟨em, tP, us',a,tg,e⟩ :: sofar
    | _, _ => sofar
    ) []
  res



def embed_next_raw' (extens : List IntroTree) (ans : List (List (ℕ × CExpr))) (gids_here : List Nat)
  (embedSofar : Array (Option CExpr)) (paramsSofar : List (Name × Level)) (todo_idx : Nat) (todo_data : EmbedData) :
  List candidateEmb :=
  with_lTrace TraceFlags.off in
  let ans_candid := ans.foldl (fun sofar L =>
    let loc : List candidate := L.foldl (init := []) (fun r (k, v) =>
      match CExpr.MatchAssignLFFCU todo_data.cexpr v with
      | .none => r
      | .some (l,u) => ⟨k,l,u,ans,gids_here,extens⟩ :: r
      )
    loc ++ sofar
    ) []
  let candidates := extens.map (getEmbCandidates · todo_data.cexpr)
  let res := (ans_candid ++ candidates.join).foldl (fun sofar ⟨i,tp,p,a,tg,e⟩ =>
    let exp := merge_if_compatible (embedSofar.set! todo_idx (.some (.gnode i (.ofBvar 42)))) tp
    let us := univsMerge (.some paramsSofar) (.some p)
    match exp, us with
    | .some (em, tP), .some us' => ⟨em, tP, us',a,tg,e⟩ :: sofar
    | _, _ => sofar
    ) []
  res




-- should roughly do the same
def propagate_raw (fctx : FixCtx)
  (embedSofar :  Array (Option CExpr)) (paramsSofar : List (Name × Level))
  (todo_idx : Nat) (todo_thm_type : CExpr)
  :  Option (((Array (Option CExpr)) × (List Nat)) × List (Name × Level))  :=
  let res :=
    match embedSofar.get! todo_idx with
    | .none => .none
    | .some ce =>
          let cet := CExpr.inferType fctx ce
          match CExpr.MatchAssignLFFCU todo_thm_type cet with
          | .none => .none
          | .some (l,u) =>
              let exp := merge_if_compatible embedSofar l
              let us := univsMerge (.some paramsSofar) (.some u)
              match exp, us with
              | .some exp', .some us' => .some (exp',us')
              | _, _ => .none
  with_lTrace TraceFlags.off in
  lTrace TraceFlags.zero & s!"Ran embed_next_raw.\nOn embed:{repr embedSofar}\nOn todo id {todo_idx} with cexpr {repr todo_thm_type}\nReturn:{repr res}\n\n" & res



structure EmbedStruct where
  embed : Array (Option CExpr)
  unassigned_instances : List Nat
  param : List (Name × Level)
  topGoals : List Nat
deriving BEq, Inhabited, Repr


private structure Data where
  embedSofar :  Array (Option CExpr)
  paramsSofar : List (Name × Level)
  instances : List Nat
  unassignedNodes : List Nat
  assignedFrontier : List Nat
  ancestors : List (List (ℕ × CExpr)) -- including own generation
  topGoals : List Nat
  extentions : List IntroTree
deriving BEq, Inhabited, Repr


partial def full_matcher_rawF (fctx : FixCtx)
  (thm_data : Array EmbedData) (thm_order : Array Nat) (ltx : IntroTree) : List EmbedStruct :=
  let rec main (todo : List Data) (done : List EmbedStruct) : List EmbedStruct :=
    match todo with
    | [] => done
    | ⟨embedSofar, paramsSofar, instances, unassignedNodes, assignedFrontier,ans,topG,exte⟩ :: more =>
        match assignedFrontier with
        | [] =>
            match unassignedNodes with
            | [] => main more (⟨embedSofar, instances, paramsSofar,topG⟩ :: done)
            | n :: l =>
              let nd := thm_data.get! n
              match nd with
              | .inst _ _ _ =>
                    let L := embed_next_raw' exte ans topG embedSofar paramsSofar n nd
                    match L with
                    | [] => main (⟨embedSofar, paramsSofar, (n :: instances), l, assignedFrontier,ans,topG,exte⟩ :: more) done
                    | _ =>  let add := L.map (fun ⟨emb, front, para, anc, tGo, Ex⟩ => ⟨emb, para, instances, l, front.mergeSort (· ≤ ·), anc, tGo, Ex⟩)
                            main (add ++ more) done
              /-
              The difference now is that we should embed the next, given a Data context,
              only among the ancestors and extention IntroTree !
              -/
              | .nonInst _ _ _ =>
                    let L := embed_next_raw' exte ans topG embedSofar paramsSofar n nd
                    let add := L.map (fun ⟨emb, front, para, anc, tGo, Ex⟩ => ⟨emb, para, instances, l, front.mergeSort (· ≤ ·), anc, tGo, Ex⟩)
                    main (add ++ more) done
        | n :: l =>
            let nd := thm_data.get! n
            match propagate_raw fctx embedSofar paramsSofar n nd.cexpr with
            | .none => main more done
            | .some ((emb, toFront), us) => main (⟨emb, us, instances, (unassignedNodes.filter (fun x => ¬ x ∈ (n :: toFront))), (toFront.foldl (fun x y => List.orderedInsertOrLeave (· ≤ ·) y x) l),ans,topG,exte⟩ :: more) done  -- no duplicates
      --dbg_trace "(DEBUG full_matcher_rawF)"
      main [⟨(Array.mkArray thm_data.size .none), [], [], thm_order.toList, [],[],[],[ltx]⟩] []

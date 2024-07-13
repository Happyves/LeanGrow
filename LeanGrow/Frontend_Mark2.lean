
import LeanGrow.ProcessEnv_forFrontEnd_2
import LeanGrow.ProcessLocalCtx


open Lean


def List.map₂ (l : List α) (L : List β) (f : α → β → γ) : List γ :=
  match l, L with
  | xl :: rl, xL :: rL => (f xl xL) :: (List.map₂ rl rL f)
  | _, _ => []

--#exit

def embed_to_expr (embed : Array (Option NodeCst)) --(impInfo : List miniBind)
  (size : Nat) (dict : PersistentHashMap ℕ FVarId) (info : ConstantInfo) : MetaM Expr := do
  let proArg ← ((List.range size).foldl (fun l i => (embed.getD i .none) :: l) []).mapM
      (fun x => match x with
                | .none => return .some (← Meta.mkFreshExprMVar .none)
                | .some (.ofCst e) =>
                      match (CExpr.toExpr e) with
                      | .none => return .none
                      | .some ex => return .some ex
                | .some (.ofNode im) => return .some (Expr.fvar (dict.find! im))
      )
  --dbg_trace s!"Ready for Printing ; proArgg: {proArg}"
  --let args : List Expr := ((List.map₂ (proArg) impInfo (fun x i => match i with | .inst => .none | _ => x)).reduceOption).reverse
  -- TODO : replace instances with mvars, without fucking up, which is gonna be hard
  let args : List Expr := ((proArg).reduceOption).reverse
  return mkAppN (.const info.name (info.levelParams.map Level.param)) args.toArray


--#exit

open Lean Elab Meta Command Tactic TryThis


def Lean.Meta.Tactic.TryThis.delabToEmbellishedRefinableSuggestion (depPreInfo : Expr → MetaM (Option String)) (depPostInfo : Expr → MetaM (Option String)) (e : Expr)  : MetaM Suggestion :=
  return { suggestion := ← delabToRefinableSyntax e, messageData? := e, preInfo? := ← depPreInfo e, postInfo? := ← depPostInfo e }


def Lean.Meta.Tactic.TryThis.addEmbellishedTermSuggestions (ref : Syntax) (es : Array Expr)
    (origSpan? : Option Syntax := none) (header : String := "Try these:")
    (depPreInfo : Expr → MetaM (Option String) := fun _ => do return .none) (depPostInfo : Expr → MetaM (Option String) := fun _ => do return .none)
    (codeActionPrefix? : Option String := none) : MetaM Unit := do
  addSuggestions ref (← es.mapM (delabToEmbellishedRefinableSuggestion depPreInfo depPostInfo))
    (origSpan? := origSpan?) (header := header) (codeActionPrefix? := codeActionPrefix?)

--#exit


elab "grow"  : tactic => do
        let (md, _) ← readModuleData ⟨"/./home/yves/Desktop/CodeWorkspace/Lean4_General/LeanGrow/LeanGrow/Caches/mark2cache"⟩
        let ref ← getRef
        Elab.Tactic.withMainContext do
          let ltx ←  getLCtx
          let (ltx_dag, ltx_dict, ltx_dict') := orderHyps_fromLocalCtx ltx
          md.constants.forM (fun decInfo => do
              let na ← Loogle.isBlackListed decInfo.name
              if (! na)
              then match decInfo with
                   |  .defnInfo v  => do
                        if v.type == .const `pdata []
                        then
                          let thm_dag := v.value
                          let embeds := matcher thm_dag (SizeDAG.sinks_fst ltx_dag)
                          match embeds with
                          | [] => pure ()
                          | _ =>  do
                                  let P ← (embeds.mapM (fun e => embed_to_expr e --(hyps.map Prod.snd)
                                    thm_dag.size ltx_dict' decInfo))
                                  addEmbellishedTermSuggestions ref P.toArray
                                    (depPostInfo := fun e => do return s!"\n{← ppExpr (← inferType e)}")
                        else return ()
                   | _ => pure ()
              else return ())

#check unsafeCast

#exit

example (l L : List ℕ) (h : 0 < l.length) : True :=
  by
  grow
  trivial


#check List.splitOnP.go_ne_nil

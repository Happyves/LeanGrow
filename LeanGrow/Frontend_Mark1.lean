
import LeanGrow.DAGembed
import LeanGrow.ProcessDecl
import LeanGrow.ProcessLocalCtx
import LeanGrow.Blacklisting
import Mathlib

open Lean


def List.map₂ (l : List α) (L : List β) (f : α → β → γ) : List γ :=
  match l, L with
  | xl :: rl, xL :: rL => (f xl xL) :: (List.map₂ rl rL f)
  | _, _ => []

--#exit

def embed_to_expr (embed : Array (Option NodeCst)) --(impInfo : List miniBind)
  (size : Nat) (dict : PersistentHashMap ℕ FVarId) (info : ConstantInfo) : Expr :=
  let proArg := ((List.range size).foldl (fun l i => (embed.getD i .none) :: l) []).map
      (fun x => match x with
                | .none => .none
                | .some (.ofCst e) =>
                      match (CExpr.toExpr e) with
                      | .none => .none
                      | .some ex => .some ex
                | .some (.ofNode im) => .some (Expr.fvar (dict.find! im))
      )
  dbg_trace s!"Ready for Printing ; proArgg: {proArg}"
  --let args : List Expr := ((List.map₂ (proArg) impInfo (fun x i => match i with | .inst => .none | _ => x)).reduceOption).reverse
  -- TODO : replace instances with mvars, without fucking up, which is gonna be hard
  let args : List Expr := ((proArg).reduceOption).reverse
  mkAppN (.const info.name (info.levelParams.map Level.param)) args.toArray


#exit

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


elab "grow" n:name : tactic =>
  match (Lean.Syntax.isNameLit? n.raw) with
  | none => throwError s!"Error : please enter the correct name of a module to search theorems in."
  | some N => do
        dbg_trace "running 1 !"
        let env ← getEnv
        let ref ← getRef
        dbg_trace "running 2 !"
        let modules := env.header.moduleNames.map (N.isPrefixOf ·)
        Elab.Tactic.withMainContext do
          dbg_trace "running 3 !"
          let ltx ←  getLCtx
          let (ltx_dag, ltx_dict, ltx_dict') := orderHyps_fromLocalCtx ltx
          dbg_trace s!"Local context dag :\n{instToStringFormat.toString (repr ltx_dag)}\n"
          env.constants.map₁.forM (fun decName decInfo => do
              let na ← Loogle.isBlackListed decName
              if modules[env.const2ModIdx[decName].get! (α := Nat)]! && (! na)
              then match decInfo with
                   | .thmInfo v | .defnInfo v => do
                        dbg_trace s!"Looking at {v.name}"
                        let hyps := naiveGetHyps v.type
                        let thm_dag := orderHyps_wBvar hyps
                        dbg_trace s!"Thm dag :\n{instToStringFormat.toString (repr thm_dag)}\n"
                        let embeds := matcher thm_dag ltx_dag
                        dbg_trace s!"Embeddings : {embeds}\n"
                        match embeds with
                        | [] => pure ()
                        | _ => do
                            addEmbellishedTermSuggestions ref (embeds.map (fun e => embed_to_expr e --(hyps.map Prod.snd)
                              thm_dag.size ltx_dict' decInfo)).toArray
                              (depPostInfo := fun e => do return s!"\n{← ppExpr (← inferType e)}")
                   | _ => pure ()
              else return ())




elab "testing" n:name : tactic =>
  match (Lean.Syntax.isNameLit? n.raw) with
  | none => throwError s!"Error : please enter the correct name of a module to search theorems in."
  | some N => do
        dbg_trace "running 1 !"
        let env ← getEnv
        let ref ← getRef
        dbg_trace "running 2 !"
        Elab.Tactic.withMainContext do
          dbg_trace "running 3 !"
          let ltx ←  getLCtx
          let (ltx_dag, ltx_dict, ltx_dict') := orderHyps_fromLocalCtx ltx
          dbg_trace s!"Local context dag :\n{instToStringFormat.toString (repr ltx_dag)}\n"
          env.constants.map₁.forM (fun decName decInfo => do
              if decName = N
              then do
                   let hyps := naiveGetHyps decInfo.type
                   let thm_dag := orderHyps_wBvar (hyps)
                   dbg_trace s!"Thm dag :\n{instToStringFormat.toString (repr thm_dag)}\n"
                   let embeds := matcher thm_dag ltx_dag
                   dbg_trace s!"Embeddings : {embeds}\n"
                   addEmbellishedTermSuggestions ref (embeds.map (fun e => embed_to_expr e --(hyps.map Prod.snd)
                    thm_dag.size ltx_dict' decInfo)).toArray
                    (depPostInfo := fun e => do return s!"\n{← ppExpr (← inferType e)}")
               else return ())




--#exit

example {m n : ℕ} (h1 : m ≤ n) (h2 : n ≤ n) : True :=
  by
  testing `Nat.gcd_sub_self_left
  trivial

--#exit

example (l L : List ℕ) (h : 0 < l.length) : True :=
  by
  grow `Mathlib.Data.List.Basic
  trivial

#check Nat
#check List.ne_nil_of_length_pos
#check List.splitOn_nil


#exit


example {m n : ℕ} (h : m ≤ n) : True :=
  by
  grow `Mathlib.Data.Nat.GCD
  trivial

example (m n : ℕ) (h : m ≤ n) : True :=
  by
  grow `Mathlib.Data.Nat.GCD
  trivial

#check Nat.gcd_sub_self_left
#check Nat.Coprime.lcm_eq_mul

#check Nat.not_coprime_zero_zero
#check Nat.Coprime.symmetric



#exit

-- TODO Fix and do more testing

universe u

example {α β : Type u} (d : Dict α β)  (key : α) (val : β)  : True :=
  by
  grow `MyProject.Utils.Dict
  trivial

#check Dict.modify_or_leave._rarg._closed_1._cstage2

/-
↑ required getting rid of universe equality in `CExpr.MatchAssign` ...
-/

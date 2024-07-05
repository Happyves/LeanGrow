
import LeanGrow.DAGembed
import LeanGrow.ProcessDecl
import LeanGrow.ProcessLocalCtx
import LeanGrow.Blacklisting
import Mathlib

open Lean


-- TODO: use second list from `naiveGetHyps` to add only default args
def embed_to_expr (embed : Array (Option Nat)) (size : Nat) (dict : PersistentHashMap ℕ FVarId) (info : ConstantInfo) : Expr :=
  let args : List Expr := (((List.range size).foldl (fun l i => (embed.get! i) :: l) []).reduceOption.map (fun x => Expr.fvar (dict.find! x))).reverse
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
                        let thm_dag := orderHyps_wBvar (naiveGetHyps v.type)
                        dbg_trace s!"Thm dag :\n{instToStringFormat.toString (repr thm_dag)}\n"
                        let embeds := matcher thm_dag ltx_dag
                        dbg_trace s!"Embeddings : {embeds}\n"
                        match embeds with
                        | [] => pure ()
                        | _ => do
                            addEmbellishedTermSuggestions ref (embeds.map (fun e => embed_to_expr e thm_dag.size ltx_dict' decInfo)).toArray
                              (depPostInfo := fun e => do return s!"\n{← ppExpr (← inferType e)}")
                            -- logInfo decName
                            -- for e in embeds do
                            --   let comp := embed_to_expr e thm_dag.size ltx_dict' decInfo
                            --   let t ← Meta.inferType comp
                            --   logInfo m!"As {← Meta.ppExpr comp}\nOf type: {← Meta.ppExpr t}"
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
      --let modules := env.header.moduleNames.map (N.isPrefixOf ·)
      Elab.Tactic.withMainContext do
        dbg_trace "running 3 !"
        let ltx ←  getLCtx
        let (ltx_dag, ltx_dict, ltx_dict') := orderHyps_fromLocalCtx ltx
        dbg_trace s!"Local context dag :\n{instToStringFormat.toString (repr ltx_dag)}\n"
        env.constants.map₁.forM (fun decName decInfo =>
            if decName = N
            then do
                 let thm_dag := orderHyps_wBvar (naiveGetHyps decInfo.type)
                 dbg_trace s!"Thm dag :\n{instToStringFormat.toString (repr thm_dag)}\n"
                 let embeds := matcher thm_dag ltx_dag
                 dbg_trace s!"Embeddings : {embeds}\n"
                 addEmbellishedTermSuggestions ref (embeds.map (fun e => embed_to_expr e thm_dag.size ltx_dict' decInfo)).toArray
                      (depPostInfo := fun e => do return s!"\n{← ppExpr (← inferType e)}")
                --  logInfo decName
                --  for e in embeds do
                --    let comp := embed_to_expr e thm_dag.size ltx_dict' decInfo
                --    let t ← Meta.inferType comp
                --    logInfo m!"As {← Meta.ppExpr comp}\nOf type: {← Meta.ppExpr t}"
            else return ()
        )





#exit

example (l L : List ℕ) (h : l ≤ L) : True :=
  by
  grow `Mathlib.Data.List
  trivial


#exit

example {m n : ℕ} (h : m ≤ n) : True :=
  by
  testing `Nat.gcd_sub_self_left
  trivial



--#exit


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

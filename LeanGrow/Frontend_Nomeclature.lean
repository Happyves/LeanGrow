
import LeanGrow.DAGembed
import LeanGrow.ProcessDecl
import LeanGrow.ProcessLocalCtx
import LeanGrow.Blacklisting
import LeanGrow.Nomeclature

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
  dbg_trace s!"Ready for Printing ; proArgg: {proArg}"
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

elab "no_grow" e:num n:num h:name "with" s:ident+ : tactic => do
  let akward : Syntax → TacticM String :=
    fun x : Syntax => match x with
                      | Syntax.ident _ rawVal _ _   => return rawVal.toString
                      | _ => throwError "Something went wrong when elaborating the keywords"
  let S ← s.mapM (akward ∘ TSyntax.raw)
  let Sm := if e.getNat = 0 then S.toList else merge S.toList what_I_meant_compiled
  let env ← getEnv
  let ref ← getRef
  let modules := env.header.moduleNames.map (h.getName.isPrefixOf ·)
  Elab.Tactic.withMainContext do
    dbg_trace "running 3 !"
    let ltx ←  getLCtx
    let (ltx_dag, ltx_dict, ltx_dict') := orderHyps_fromLocalCtx ltx
    env.constants.map₁.forM (fun declName declInfo => do
      let na ← Loogle.isBlackListed declName
      if modules[env.const2ModIdx[declName].get! (α := Nat)]! && (! na)
      then  if declInfo.isThm
            then
              let data :=  (List.join ((Name.getStringList declName).map thm_parse)) -- List.dedup makes Lean lose it...
              let mut count := n.getNat
              let mut good? := false
              for d in data do
                if d ∈ Sm
                then
                  if count ≠ 0
                  then
                    count := count - 1
                  else
                    good? := true
                    break
              if (count = 0) || good?
              then match declInfo with
                    | .thmInfo v | .defnInfo v | .axiomInfo v | .ctorInfo v | .quotInfo v | .recInfo v => do
                        dbg_trace s!"Looking at {v.name}"
                        let hyps := naiveGetHyps v.type
                        let thm_dag := orderHyps_wBvar hyps
                        dbg_trace s!"Thm dag :\n{instToStringFormat.toString (repr thm_dag)}\n"
                        let embeds := matcher thm_dag ltx_dag
                        dbg_trace s!"Embeddings : {embeds}\n"
                        match embeds with
                        | [] => pure ()
                        | _ =>  do
                                let P ← (embeds.mapM (fun e => embed_to_expr e --(hyps.map Prod.snd)
                                  thm_dag.size ltx_dict' declInfo))
                                addEmbellishedTermSuggestions ref P.toArray
                                  (depPostInfo := fun e => do return s!"\n{← ppExpr (← inferType e)}")
                    | _ => pure ()

              else return ()
            else return ()
      else return ())






--#exit


example (l L : List ℕ) (h : 0 < l.length) : True :=
  by
  no_grow 1 1 `Mathlib.Data.List with nil
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

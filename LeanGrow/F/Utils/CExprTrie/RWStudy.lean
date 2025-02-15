
import Mathlib.Tactic


open Lean Meta Mathlib Elab Tactic

-- # todo


#check CC.CCM.mkCongrProofCore


#check TermCongr.mkCongrOf


#check MVarId.congrN

#check withRWRulesSeq

#check MVarId.congrCore

#check Conv.congr

#check evalRewriteSeq
#check MVarId.rewrite
#check Meta.kabstract

-- # congr

#check MVarId.congrCore!
-- repeatedly applyies passes replacing goal mvar with new one, adding internmediate goal ones ?
#check MVarId.congrPasses!
-- The passes are applications *some* of the following thms:

#check implies_congr
#check pi_congr
#check forall_prop_domain_congr
#check let_congr
-- and more fancier stuff, like:
#check MVarId.smartHCongr?
-- which is based on
#check mkRichHCongr
-- which gets dependecies via
#check getFunInfoNArgs



elab "testin_HCongr" t:term : tactic => do
  let ter ← Tactic.elabTerm t .none
  let f := ter.getAppFn
  let as := ter.getAppArgs
  let T ← inferType f
  let info ← getFunInfoNArgs f (as.size + 1)
  let cthm ← mkRichHCongr (forceHEq := true) T info (fixedFun := false) (fixedParams := #[])
  logInfoAt (← getRef) s!"{← ppExpr cthm.type}"

--#exit

set_option trace.Meta.CongrTheorems true in
noncomputable
def test33 {α : Sort _} {β γ: α → Sort _} {δ : (a : α) → β a → γ a → Sort _}
  {a : α} {b : β a} {c : γ a} {d : δ a b c}
  {motive : (w : α) → (x : β w) → (y : γ w) → (z : δ w x y) →  Sort _} (H : motive a b c d)
  {e : α} {f : β e} {g : γ e} {h : δ e f g}
  (ta : a = e) (tb : HEq b f) (tc : HEq c g) (td : HEq d h) : motive e f g h :=
  by
  testin_HCongr (motive a b c d)
  sorry



-- # convert

#check MVarId.convert
-- is just an Eq.mp or Eq.mpr on top of the eq shown via congr

-- # unrelated

-- `initialize registerTraceClass `Meta.CongrTheorems`
-- for `trace[Meta.CongrTheorems] "ftype: {fType}"` in do block of MetaM

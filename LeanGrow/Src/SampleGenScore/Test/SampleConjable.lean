

import LeanGrow.Src.SampleGenScore.Sample
import LeanGrow.Src.SampleGenScore.Gen.ConjecturableBuild
import LeanGrow.Src.Caching.Score.ConjecturableProcess

import Mathlib.Data.List.Dedup
import Mathlib.Data.List.Lemmas

open Lean Meta

set_option linter.style.longLine false


#check Name.blackListCaching

def mkConjableTrie_envModules (modules : Array Name) : MetaM (CTrie (List Nat)) := do
  let env ← getEnv
  let mids := Array.reduceOption <| modules.map (fun n => env.getModuleIdx? n)
  let mut out := CTrie.empty
  for (cn,ci) in env.constants do
    match (env.getModuleIdxFor? cn) with
    | .none => continue
    | .some cmi =>
      if mids.contains cmi
      then
        match ci with
        | .thmInfo .. =>
          if !(cn.blackListCaching env)
          then
            let res ← getConjecturablePos ci.type
            match res with
            | [] => continue
            | _ => out := out.insert cn.toString.toUTF8 res
        | _ => continue
  return out

#check 1



#check Eq.trans
#check Classical.byCases
#check Nat.le_trans

def mods := #[`Init.Prelude, `Init.Classical]

-- #eval (do let res ← mkConjableTrie_envModules mods ; IO.println res.toList)

#check 1


def test (printLift? : Bool) (modules : Array Name) (thmName : Name) (depthDig depthStart depthStop : Nat) : MetaM Unit := do
  let .some (.thmInfo I) := (← getEnv).find? thmName | throwError "Bad name"
  lambdaTelescope I.value <| fun fvs p => do
    let preS ← mkPreProCongr
    let cjs ← mkConjableTrie_envModules modules
    let .mk res haves l1 l2 ← sampleCoreBack preS cjs (← getLCtx) (← getLocalInstances) depthDig depthStart depthStop .none .none (.cons (.raw p) (fvs.map Expr.fvarId!).toList .nil) .nil .nil
    withLCtx l1 l2 <| do
      res.foldlM () (fun kind fvs goal hyps _ => do
        IO.println "\nSample (back):\nLifted:"
        if printLift?
          then fvs.foldlM (fun _ fv => do IO.println s!" {← fv.getUserName} : {← ppExpr (← fv.getType)}") ()
        IO.println s! "Goal: {← ppExpr goal}"
        IO.println "Hyps:"
        hyps.foldlM (fun _ subp => do IO.println s!" · {← ppExpr subp}") ()
        IO.println s!"Kind: {← kind.pp}"
        )
      haves.foldlM () (fun pat goal hyps _ => do
        IO.println s!"\nSample (have):\nStatement: {← ppExpr pat}"
        IO.println s! "Goal: {← ppExpr goal}"
        IO.println "Hyps:"
        hyps.foldlM (fun _ subp => do IO.println s!" · {← ppExpr subp}") ()
        )


def testStd (printLift? : Bool) (thmName : Name) (depthDig depthStart depthStop : Nat) : MetaM Unit := do
  test printLift? mods thmName depthDig depthStart depthStop

#exit

theorem test_1 (n m : Nat) : n*m + 1 ≤ 2 + (m*n) := by
  calc
    n*m + 1 = m*n + 1 := by
      rw [Nat.mul_comm]
    _ = 1 + (m*n) := by
      rw [Nat.add_comm]
    _ ≤ 2 + (m*n) := by
      apply Nat.add_le_add_right
      decide


-- #eval testStd false `test_1 1 1 1


theorem test_2 (n m : Nat) : n*m + 1 ≤ 2 + (m*n) := by
  have fst : n*m + 1 = m*n + 1 := by
    rw [Nat.mul_comm]
  have snd : m*n + 1 = 1 + (m*n) := by
    rw [Nat.add_comm]
  have thd : 1 + (m*n) ≤ 2 + (m*n) := by
    apply Nat.add_le_add_right
    decide
  rw [fst,snd]
  apply thd


-- tracing_mode .std
-- tracing_flags [(`sampleCoreBack, TracingFlags.all),
--                (`digExpr.go, TracingFlags.all),
--                (`digExpr.inner, TracingFlags.all),
--                ]

-- #eval testStd false `test_2 1 1 1
-- For the have-samples, the fact that we "inline" ahves at `delabDig_HaveLet_core`
-- means that they won't become hypotheses in the samples ...

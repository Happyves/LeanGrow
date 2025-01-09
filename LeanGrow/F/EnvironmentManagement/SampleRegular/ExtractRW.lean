
import LeanGrow.F.EnvironmentManagement.SampleRegular.API

open Lean Meta


inductive rwPartType where
| ofThm (subproof : Expr) (name : Name) (rel_args : List Expr)
| ofLocal (subproof : Expr)
| none
deriving Inhabited, Repr, BEq

def extractRW_main (proof : Expr) : MetaM rwPartType := -- subproof, thm name and args
  match proof with
  | .app _ _ =>
      let (h,as) := proof.getAppFnArgs
      if h == `Eq.mp || h == `Eq.mpr
      then
        let rwPart := as.get! 2
        let subproof := as.get! 3
        match rwPart with
        | .app _ (.app _ core) => -- id and congrArd, assuming no reduction
            match core with
            | .app _ _ | .const _ _ => -- are there equalities that require not arguements ??
              let (H,AS) := core.getAppFnArgs
              if H == `Eq.symm
              then
                let final := AS.get! 3
                match final with
                | .app _ _ | .const _ _ => -- are there equalities that require not arguements ??
                  let (n,args) := final.getAppFnArgs
                  do
                    let relArgs ← getRelevantArgsOTypes args
                    return .ofThm subproof n relArgs
                | _ => pure (.ofLocal subproof)
              else
                do
                  let relArgs ← getRelevantArgsOTypes AS
                  return .ofThm subproof H relArgs
            | _ => pure (.ofLocal subproof)
        | _ => pure .none
      else pure .none
  | _ => pure .none




#check Eq.mp
#check Eq.mpr
#check Eq.symm

#exit

theorem test (n m : Nat) (hnm : n = m) (hn : n = 42) : m = 42 := by
  rw [← hnm]
  exact hn


#print test


#check Eq.mp
#check Eq.mpr
#check Eq.symm

#check id
#check congrArg

#check Eq.ndrec
#check Eq.rec
#check Eq.recOn
#check Eq.casesOn

#check eq_of_heq

#check eq_of_beq

#check of_eq_true
#check eq_true

#check congrArg

/-


import Mathlib.Tactic

theorem test (n m : Nat) (hnm : n = m) (hn : n = 42) : m = 42 := by
  rw [← hnm]
  exact hn


#print test


theorem test2 (n m : Nat) (hnm : n = m) (hn : n = 42) : m = 42 := by
  convert hn
  exact hnm.symm


#print test2


theorem test3 (n m p: Nat) (hnm : n = m) (hmp : m = p) (hn : n = 42) : p = 42 := by
  rw [← hmp, ← hnm]
  exact hn


#print test3


theorem test4 (n m : Nat) (hnm : n = m) (hn : n = 42) : m = 42 := by
  nth_rewrite 1 [← hnm]
  exact hn

#print test4


theorem test5 (n m : Nat) (hnm : n = m) (hn : n = 42) : m = 42 := by
  cc

#print test5

theorem test6 (n m : Nat) (hnm : n = m) (f : Nat → Nat) : f m = f n := by
  rw [hnm]

#print test6


theorem test7 (n m : Nat) (hnm : n = m) (f : Nat → Nat) : f m = f n := by
  congr
  exact hnm.symm

#print test7

theorem test8 (n m : Nat → Nat) (hnm : n = m) (f : Nat ) : m f = n f := by
  apply congrFun
  exact hnm.symm

#print test8

theorem test2 (n m p: Nat) : (n + m) + p = p + (n + m) := by
  rw [add_comm]

#print test2


-/

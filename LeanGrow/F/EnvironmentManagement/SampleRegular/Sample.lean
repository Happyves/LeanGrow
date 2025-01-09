
import LeanGrow.F.EnvironmentManagement.SampleRegular.API


open Lean Meta


def sample_ofProof (proof : Expr) : MetaM (List SampleTypeRaw) :=
  sorry


#check lambdaLetTelescope
#check lambdaTelescope

#check LocalContext.addDecl

#check inferType

def sample_self (n : Name) (type : Expr) : SampleTypeRaw :=
  sorry

#check getLocalInstances

def getRelevantArgs (proof : Expr) : MetaM (List Expr × List Expr) :=
  match proof with
  | .app _ _ => do
    let as := proof.getAppArgs
    let mut L := []
    let mut Ts := []
    for e in as do
      match e with
      | .fvar _ => continue
      | _ =>
        let T ← inferType e
        let TT ← inferType T
        if TT.isProp
        then
          L := e :: L
          Ts := T :: Ts
    return (L,Ts)
  | _ => return ([],[])


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

-/

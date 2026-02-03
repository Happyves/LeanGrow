
import Lean


open Lean Meta Elab Tactic


#check_failure evalInductionCore
#check Elab.Tactic.ElimApp.Alt
-- ↑ link ; Elab/Tactic/Induction

#check getElimInfo
#check getElimExprInfo

-- To tell if inductive
#check Name.getPrefix -- on type head name
#check isInductive

#check getCustomEliminator?

#check mkRecName
#check mkCasesOnName

#check FunInd.isFunInductName
#check_failure FunInd.isFunCasesName -- private. just below ↑


def testElimInfo (n : Name) : MetaM Unit := do
  if FunInd.isFunInductName (← getEnv) n then -- add cases too
    let _ ← realizeGlobalConstNoOverloadCore n
  let info ← getElimInfo n
  forallTelescopeReducing info.elimType fun xs _ => do
    for h : i in *...xs.size do
      let x := xs[i]
      let xDecl ← x.fvarId!.getDecl
      if xDecl.binderInfo.isExplicit then
        let name := xDecl.userName
        match info.altsInfo.find? (fun x => x.name == name) with
        | .some a =>
            if a.provesMotive then
              IO.println s!"{← ppExpr xDecl.type}"
        | _ => continue


#eval testElimInfo `Nat.casesOn
#eval testElimInfo `Nat.rec
#eval testElimInfo `Fin.induction
#eval testElimInfo `Nat.casesAuxOn
#eval testElimInfo `Nat.recAux
#eval testElimInfo `List.map.induct
#eval testElimInfo `Eq.rec
#eval testElimInfo `Eq.ndrec
#eval testElimInfo `False.elim



#check Fin.induction

#check Nat.casesAuxOn
#check List.map.induct
#check False.elim

-- #eval testElimInfo `Nat.add
-- fails but not because not induction principle

/-

funcases
| (casesCore : ∀ ...) terms* -- from generalise

casesCore
| (casesCore : ∀ ...) terms* -- from generalizeVars via revert
| elim alts*

alts
| term -- tactic
| fun _ => alts
| unifyEq

unifyEq
| substCore
| acyclic
| Nat.elimOffset (4 × _) (injectionCore <|> ((mvar : ∀ _) fvar))

funinduct
| (inductioCore : ∀ ...) terms* -- from generalise


inductioCore
| (inductioCore : ∀ ...) terms* -- from generalize
| elim terms*

-/

-- #exit
#check MVarId.cases
#check MVarId.induction

/-

cases
| (cases : ∀ ...) terms* -- generalizeIndices
| induction

induction
| ((fun _ =>)* induction) terms* -- from revert + intro major & indices ; is this beta'd by a later whnf
| recursor terms*
-/


#check mkRecursorInfo

def getElabElims (module : Name) : CoreM (Array Name) := do
  let env ← getEnv
  let .some midx := env.getModuleIdx? module | throwError s!"[getElabElims] was queried with odule {module}, but env doesn't have it in header"
  return (TagAttribute.ext Lean.Elab.Term.elabAsElim).getModuleEntries env midx

-- #eval getElabElims `Init.Data.Fin.Lemmas
#check Except.ok.elim


def getCustomElims (module : Name) : CoreM (Array (Array Name × Name)) := do
  let env ← getEnv
  let .some midx := env.getModuleIdx? module | throwError s!"[getCustomElims] was queried with odule {module}, but env doesn't have it in header"
  let elims := customEliminatorExt.getState env |>.map
  let res ← elims.foldM (fun A (rec?, key) val => do
    if rec?
    then
      let .some didx := env.getModuleIdxFor? val | throwError s!"[getCustomElims] {val} has no module index in this env"
      if didx == midx
      then
        return A.push (key,val)
      else
        return A
    else
      return A
    ) #[]
  return res

-- #eval getCustomElims `Init.Data.Fin.Lemmas

#exit

theorem test_1 (n : Nat) (x : Fin n) (h : x.val = 42) : 42 = x.val := by
  induction n with
  | zero => exact h.symm
  | succ n ih => exact h.symm

#print test_1


theorem test_2 (n : Nat) (x : Fin n) (h : x.val = 42) : 42 = x.val := by
  cases n with
  | zero => exact h.symm
  | succ n => exact h.symm

#print test_2
-- wierd Eq.ndrec ... from subst ? in alts ?


theorem test_3 (l : List Nat) (h : l = [42]) : [42] = l := by
  cases l with
  | nil => exact h.symm
  | cons n ns => exact h.symm

#print test_3

theorem test_4 (l : List Nat) (h : l.Nodup) : l.Nodup := by
  cases l with
  | nil => exact h
  | cons n ns => exact h

#print test_4

theorem test_5 (l : List Nat) (h : l.Nodup) : l.Nodup := by
  induction l with
  | nil => exact h
  | cons n ns ih => exact h

#print test_5


theorem test_6 (l : List Nat) (x : Nat) (h : x = 42) : l.contains x := by
  induction l generalizing x with
  | nil => sorry
  | cons n ns ih => sorry

#print test_6

theorem test_7 (l : List Nat) (x : Nat) (h : x = 42) : l.contains x := by
  induction l using List.map.induct generalizing x with
  | case1 => sorry
  | case2 n ns ih => sorry

#print test_7


theorem test_8 (n : Nat) (x : Fin (n+1)) (h : x.val = 42) : 42 = x.val := by
  induction x using Fin.induction with
  | zero => exact h.symm
  | succ n => exact h.symm

#print test_8


#check List.Perm


theorem test_9 (l : List Nat) (h : l = 42 :: l) : 42 = 37 := by
  cases h

#print test_9

theorem test_10 (h : List.Perm [] [1,2]) : 42 = 37 := by
  cases h with
  | trans a b =>
      sorry

#print test_10


inductive somePred : List Nat → Prop where
| only (l : List Nat) : somePred (42 :: l)

theorem test_11 (h : somePred []) : 42 = 37 := by
  cases h

#print test_11


theorem test_12 (h : somePred [37]) : 42 = 37 := by
  cases h

#print test_12

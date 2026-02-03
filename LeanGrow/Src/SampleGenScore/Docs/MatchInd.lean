

import Lean


open Lean Meta Elab Term


#check elabMatch
#check getMatcherInfo?
-- there were quite a few PRs that changed it, so fix in next version

#print MatcherInfo
#print Match.DiscrInfo

def printMatcherInfo (declName : Name)  : MetaM Unit := do
  let .some info ← getMatcherInfo? declName | throwError "aaahh"
  IO.println s!"numParams {info.numParams}"
  IO.println s!"numDiscrs {info.numDiscrs}"
  IO.println s!"altNumParams {info.altNumParams}"
  IO.println s!"uElimPos?  {info.uElimPos? }"
  IO.println s!"discrInfos {info.discrInfos.map Match.DiscrInfo.hName? }"
  IO.println s!"getFirstAltPos {info.getFirstAltPos}"
  IO.println s!"getAltRange {info.getAltRange.toArray}"
  IO.println s!"getDiscrRange {info.getDiscrRange.toArray}"



theorem test_1 (x : Nat) : 42 = 42 := by
  match x with
  | 0 => rfl
  | n+1 => rfl

#print test_1
#print test_1.match_1_1
#eval printMatcherInfo `test_1.match_1_1

theorem test_2 (x : Nat) : 42 = 42 := by
  match x with
  | 0 => rfl
  | 1
  | n+2 => rfl

#print test_2
#print test_2.match_1_1
#eval printMatcherInfo `test_2.match_1_1



theorem test_3 (x : List Nat) : 42 = 42 := by
  match x with
  | [] => rfl
  | 42 :: l => rfl
  | 37 :: 42 :: l => rfl
  | _ :: _ => rfl

#print test_3
#print test_3.match_1_1
#eval printMatcherInfo `test_3.match_1_1
-- matcher branch has Eq.ndrec



theorem test_4 (x y : Nat) : 42 = 42 := by
  match x, y with
  | 0, 0 => rfl
  | n+1, m+1 => rfl
  | _, _ => rfl

#print test_4
#print test_4.match_1_1
#eval printMatcherInfo `test_4.match_1_1




theorem test_5 (x : Nat) (h : x = 37) : 42 = 42 := by
  match x with
  | 0 => rfl
  | n+1 => rfl

#print test_5
#print test_5.match_1_1
#eval printMatcherInfo `test_5.match_1_1


theorem test_6 (x : Nat) (h : x = 37) : 42 = 42 := by
  match D : x with
  | 0 => contradiction
  | n+1 => rfl

#print test_6
#print test_6.match_1_1
#eval printMatcherInfo `test_6.match_1_1
-- matcher should be headBeta'd

theorem test_7 (n : Nat) (x : Fin n) (h : x.val = 37) : 42 = 42 := by
  match D : x.val with
  | 0 => rw [D] at h
  | n+1 => rfl

#print test_7
#print test_7.match_1_1
#eval printMatcherInfo `test_7.match_1_1

inductive FinList (n : Nat) where
| nil | cons (x : Fin n) (_ : FinList n)


theorem test_8 (n : Nat) (x : FinList n) (h1 : n = 37) (h2 : x ≠ .nil) : 42 = 42 := by
  match D : x with
  | .nil => rfl
  | .cons _ _ => rfl

#print test_8
#print test_8.match_1_1
#eval printMatcherInfo `test_8.match_1_1


inductive FinListSized (n : Nat) : Nat → Type where
| nil : FinListSized n 0
| cons (x : Fin n) (_ : FinListSized n i) : FinListSized n (i+1)

theorem test_9 (n : Nat) (x : FinListSized n n) (h1 : n = 37) (h2 : HEq x (@FinListSized.nil )) : 42 = 42 := by
  match D : x with
  | .nil => rfl
  | .cons _ _ => rfl

#print test_9
#print test_9.match_1_1
#eval printMatcherInfo `test_9.match_1_1


/-

match
| let _ := _ in _
| matcher (motive (term)) (dsicrs (term))* (rhss (term))*

-/


#check Structural.mkBRecOnApp

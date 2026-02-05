

import Mathlib.Tactic

open Lean Meta Elab Tactic


#check evalSplit

#check_failure Mathlib.Tactic.splitIfsCore


theorem test_1 (n : Nat) :
  (match n with
  | 0 => 1
  | 1 => 37
  | n+2 => n
    ) = 42 := by
      split
      all_goals sorry

set_option pp.privateNames true in
#print test_1
#print test_1.match_1.splitter

set_option pp.privateNames true in
#check test_1

#print MatcherInfo
#print Match.MatchEqns

#eval ((do let env ← getEnv ; return Match.isMatchEqnTheorem env `test_1.match_1.splitter) : CoreM Bool)

def isMatchSpliiter (env : Environment) : Array (Name × Name) := Id.run do
  return (Match.matchEqnsExt.getState (asyncMode := .async .asyncEnv)  env).map.toArray.map (fun (x,y) => (x,y.splitterName))


#eval ((do let env ← getEnv ; return isMatchSpliiter env ) : CoreM _)

#check 1

#eval ((do let eqs ← Match.getEquationsFor `test_1.match_1 ; return eqs.splitterName) : MetaM _)

#eval ((do let eqs ← Match.getEquationsFor `test_1.match_1 ; return eqs.splitterAltNumParams) : MetaM _)


#check 1
--splitterAltNumParams

theorem test_2 (n : Nat) (h : n + 5 = 10) :
  (match n+1 with
  | 0 => 1
  | 1 => 67
  | 3 => 42
  | n+2 => n
    ) = 42 + (n+1) := by
      split
      all_goals sorry

#print test_2


theorem test_3 (n : Nat) :
  (match n with
  | 0 => 1
  | n+1 => if n = 67 then 42 else 666
    ) = if n = 67 then 42 else 666 := by
      split
      all_goals sorry

#print test_3

theorem test_4 (n : Nat) :
  37 = if n = 67 then 42 else 666 := by
    split
    all_goals sorry

#print test_4

open Classical in
theorem test_5 (n : Nat) :
  37 = if (∃ m, n = 67 +m) then 42 else 666 := by
    split
    all_goals sorry

#print test_5


theorem test_6 (n : Nat) :
  37 = if n = 67 then 42 else 666 := by
    split_ifs
    all_goals sorry

#print test_6

open Classical in
theorem test_7 (n : Nat) :
  37 = if (∃ m, n = 67 +m) then 42 else 666 := by
    split_ifs
    all_goals sorry

#print test_7



import LeanGrow.Caches.CoData
import LeanGrow.CoClustering


open Lean Data

partial def Trie.get_key [BEq α] (v : α) (cache : ByteArray) : Trie α → Option String
| .leaf x => if x == .some v then .some (String.fromUTF8! cache) else .none
| .node1 x a t =>
    if x == .some v
    then .some (String.fromUTF8! cache)
    else Trie.get_key v (cache.push a) t
| .node x as ts =>
    if x == .some v
    then .some (String.fromUTF8! cache)
    else
      Id.run do
      for c in List.range (as.size) do
        let res := Trie.get_key v (cache.push (as.get! c)) (ts.get! c)
        if res.isSome then return res
      return .none



def Array.argmaxIdx? [Inhabited α] (A : Array α) (f : α → β) (lt : β → β → Ordering) : Option Nat :=
  Id.run do
    if A.isEmpty
    then return .none
    else
      let mut M := f (A.get! 0)
      let mut I := 0
      let mut i := 0
      for x in A do
        let fx := (f x)
        if lt M fx == .lt
        then
          M := fx
          I := i
        i := i+1
      return .some I

def Array.maxIdx? [Inhabited α] (A : Array α)  (lt : α → α → Ordering) : Option Nat :=
  Id.run do
    if A.isEmpty
    then return .none
    else
      let mut M := (A.get! 0)
      let mut I := 0
      let mut i := 0
      for x in A do
        if lt M x == .lt
        then
          M := x
          I := i
        i := i+1
      return .some I

def Array.maxIdx?_with_constraints [Inhabited α] (A : Array α) (C : Array Bool) (lt : α → α → Ordering) : Option Nat :=
  Id.run do
    if A.isEmpty
    then return .none
    else
      let mut M := default
      let mut fst := true
      let mut I := Option.none
      let mut i := 0
      for x in A do
        if (C.get! i)
        then
          if fst
          then
            M := x
            I := .some i
            fst := false
          else
            if (lt M x == .lt)
            then
              M := x
              I := .some i
        i := i+1
      return  I

--#exit

def Array.argmin?_with_constraints [Inhabited α] [Inhabited β] (A : Array α) (C : Array Bool) (f : α → β) (lt : β → β → Ordering) : Option Nat :=
  Id.run do
    if A.isEmpty
    then return .none
    else
      let mut M := default
      let mut fst := true
      let mut I := Option.none
      let mut i := 0
      for x in A do
        if (C.get! i)
        then
          if fst
          then
            M := f x
            I := .some i
            fst := false
          else
            let fx := f x
            if (lt M fx == .gt)
            then
              M := fx
              I := .some i
        i := i+1
      return  I

--#exit


def query_wSplits [Inhabited α] (i : Nat) (L : List (Array α)) : α :=
  match L.get? (i / 10) with -- the 10 is the split_param
  | .none => default
  | .some a => a.get! (i % 10)


def Float.compare : Float → Float → Ordering :=
  fun a b => if a < b then .lt else (if a == b then .eq else .gt)

--#exit

elab "test_Charikar" : command => do
  let apps_float := joined_apps.map Nat.toFloat
  let co_float := joined_co_pre.map (Array.map Nat.toFloat)
  let mut densities := Array.mkArray joined_apps.size (0 : Float)
  let mut constraints := Array.mkArray joined_apps.size true
  let mut deletes := Array.mkArray joined_apps.size 0
  for del in (List.range joined_apps.size) do
    let den (v : Nat) := Id.run do
      let mut s := (0 : Float)
      for i in (List.range joined_apps.size) do
        if !(i == v) && (constraints.get! i) then s := s + (query_wSplits (use_brain v i) co_float)
      return (s / (apps_float.get! v))
    match Array.argmin?_with_constraints (Array.range joined_apps.size) constraints den Float.compare with
    | .none => throwError "aahh"
    | .some idx =>
        let mut D := (0 : Float)
        for x in (List.range joined_apps.size) do
          if (constraints.get! x)
          then
            for y in (List.range (joined_apps.size - x - 1)) do
              if (constraints.get! (y + x + 1))
              then D := D + (query_wSplits (use_brain x (y + x + 1)) co_float)
        let mut d := (0 : Float)
        for x in (List.range joined_apps.size) do
          if (constraints.get! x)
          then d := d + (apps_float.get! x)
        densities := densities.set! del (D / (max d 1))
        constraints := constraints.set! idx false
        deletes := deletes.set! del idx
  let .some argm := densities.maxIdx? Float.compare | throwError "ahhh 2"
  let full_density := Id.run do
                        let mut D := (0 : Float)
                        for x in (List.range joined_apps.size) do
                            for y in (List.range (joined_apps.size - x - 1)) do
                              D := D + (query_wSplits (use_brain x (y + x + 1)) co_float)
                        let mut d := (0 : Float)
                        for x in (List.range joined_apps.size) do
                          d := d + (apps_float.get! x)
                        return (D / d)
  let argm' := if densities.get! argm < full_density then joined_apps.size else argm
  let sol := Id.run do
    let mut res := []
    for i in List.range (argm') do
      res := (deletes.get! i) :: res
    return res
  IO.println (sol.map (Trie.get_key · ⟨#[]⟩ indexing)).reduceOption

--test_Charikar
-- has bugs, use version below

/-
After 20 min:

[AList, List.IsRotated, Function.Involutive, List.Sublist, Relator.LeftUnique, List.IsInfix,
Relator.RightUnique, WellFounded, String, Relator.BiUnique, Relation.ReflTransGen, List.chains,
LevenshteinEstimator', Function.Surjective, Function.RightInverse, Function.LeftInverse,
Function.Bijective, Cycle.Nontrivial, AList.Disjoint]

-/


def Charikar (apps_float_init : Array Float) (co_float_init : List (Array Float)) (constraints_mut : Array Bool): Elab.Command.CommandElabM (List Nat) := do
  let apps_float := apps_float_init --joined_apps.map Nat.toFloat
  let co_float := co_float_init -- joined_co_pre.map (Array.map Nat.toFloat)
  let mut densities := Array.mkArray joined_apps.size (0 : Float)
  let mut constraints := constraints_mut -- Array.mkArray joined_apps.size true
  let mut deletes := Array.mkArray joined_apps.size 0
  dbg_trace s!"Entering main loop with constraints : {constraints}"
  for del in (List.range joined_apps.size) do
    let den (v : Nat) (constraints : Array Bool) := Id.run do
      let mut s := (0 : Float)
      for i in (List.range joined_apps.size) do
        if !(i == v) && (constraints.get! i) then s := s + (query_wSplits (use_brain v i) co_float)
      return (s / (apps_float.get! v))
    if (constraints_mut.get! del)
    then
      match Array.argmin?_with_constraints (Array.range joined_apps.size) constraints (den · constraints) Float.compare with
      | .none => throwError "aahh"
      | .some idx =>
          dbg_trace s!"On round {del}, found minimizing index {idx}.\nDiscard it via constraints."
          constraints := constraints.set! idx false
          let mut D := (0 : Float)
          for x in (List.range joined_apps.size) do
            if (constraints.get! x)
            then
              for y in (List.range (joined_apps.size - x - 1)) do
                if (constraints.get! (y + x + 1))
                then D := D + (query_wSplits (use_brain x (y + x + 1)) co_float)
          let mut d := (0 : Float)
          for x in (List.range joined_apps.size) do
            if (constraints.get! x)
            then d := d + (apps_float.get! x)
          dbg_trace s!"Setting density at {del} to {D / (max d 1)}"
          densities := densities.set! del (D / (max d 1))
          dbg_trace s!"Setting delete at {del} to {idx}"
          deletes := deletes.set! del idx
  let .some argm := densities.maxIdx?_with_constraints constraints_mut Float.compare | throwError "ahhh 2"
  dbg_trace s!"Found minimizing arg wrt. constraints to be {argm}, od density {densities.get! argm}"
  let full_density := Id.run do
                        let mut D := (0 : Float)
                        for x in (List.range joined_apps.size) do
                          if (constraints_mut.get! x)
                          then
                            for y in (List.range (joined_apps.size - x - 1)) do
                              if (constraints_mut.get! y)
                              then
                                D := D + (query_wSplits (use_brain x (y + x + 1)) co_float)
                        let mut d := (0 : Float)
                        for x in (List.range joined_apps.size) do
                          d := d + (apps_float.get! x)
                        return (D / d)
  let argm' := if densities.get! argm < full_density then joined_apps.size else argm
  dbg_trace s!"After comparing to total density ({full_density}) : {argm'}"
  let sol := Id.run do
    let mut res := []
    for i in (List.range (argm' + 1)) do
      if (constraints_mut.get! i)
      then
        res := (deletes.get! i) :: res
    return res
  dbg_trace s!"Returning {sol}"
  return sol



elab "repeated_Charikar" : command => do
  let apps_float := joined_apps.map Nat.toFloat
  let co_float := joined_co_pre.map (Array.map Nat.toFloat)
  let mut constraints := Array.mkArray joined_apps.size true
  let mut toSource := []
  for c in (List.range joined_apps.size) do
    if constraints.contains true
    then
      let sol ← Charikar apps_float co_float constraints
      let t := (SortedTrieFormList' ((sol.map (Trie.get_key · ⟨#[]⟩ indexing)).reduceOption))
      toSource := s!"\ndef clusTrie_{c} : Trie Unit := {print_trie t}" :: toSource -- add pdata clusters, of course
      for n in sol do
        constraints := constraints.set! n false
  let source := s!"import LeanGrow.NameListCompare\nimport LeanGrow.Caches.CoData\nopen Lean Data{String.join toSource}"
  IO.FS.writeFile ⟨"/./home/yves/Desktop/CodeWorkspace/Lean4_General/LeanGrow/LeanGrow/Caches/CarikarClusters.lean"⟩ (source)

--repeated_Charikar
-- 10h +

def repeated_split_Charikar (constraints_init : Array Bool) (offset : Nat) := do
  let apps_float := joined_apps.map Nat.toFloat
  let co_float := joined_co_pre.map (Array.map Nat.toFloat)
  let mut constraints := constraints_init
  let mut toSource := []
  for c in (List.range 3) do
    if constraints.contains true
    then
      dbg_trace s!"Entering Charikar with constraints {constraints}"
      let sol ← Charikar apps_float co_float constraints
      let t := (SortedTrieFormList' ((sol.map (Trie.get_key · ⟨#[]⟩ indexing)).reduceOption))
      toSource := s!"\ndef clusTrie_{c + (3*offset)} : Trie Unit := {print_trie t}" :: toSource -- add pdata clusters, of course
      for n in sol do
        constraints := constraints.set! n false

  let split_param := 10
  let num_splits_apps := constraints.size / split_param
  let mut a_o_as := Array.mkArray (num_splits_apps + 1)  #[]
  for ca in [0:(num_splits_apps)] do
    let mut A := Array.mkArray (split_param) 0
    for spc in [0:(split_param)] do
      A := A.set! spc (constraints.get! (split_param*ca + spc))
    a_o_as := a_o_as.set! ca A
  let mut A := Array.mkArray (constraints.size % split_param) 0
  for spc in [0:(constraints.size % split_param)] do
    A := A.set! spc (constraints.get! (split_param*num_splits_apps + spc))
  a_o_as := a_o_as.set! num_splits_apps A

  let mut toSource_constraints:= ([] : List String)
  let mut co := 0
  for a in a_o_as do
    toSource_constraints := s!"\ndef constraints_split_{co}_{offset} : Array Bool := {a}" :: toSource_constraints
    co := co+1
  toSource_constraints := toSource_constraints.reverse
  let source_apps := (String.join toSource_constraints) ++ s!"\ndef constriants_remaining_{offset} : Array Bool := {String.intercalate " ++ " ((List.range (num_splits_apps + 1)).map (s!"constraints_split_{·}_{offset}"))}"


  let source := s!"import LeanGrow.NameListCompare\nimport LeanGrow.Caches.CoData\nopen Lean Data{String.join toSource}{source_apps}"
  IO.FS.writeFile ⟨s!"/./home/yves/Desktop/CodeWorkspace/Lean4_General/LeanGrow/LeanGrow/Caches/CarikarClusters_batch_o_{offset}.lean"⟩ (source)

-- 0th batch
--#eval repeated_split_Charikar (Array.mkArray joined_apps.size true) 0
-- ≈ 10 min

/-
Entering Charikar with constraints #[true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true]
Entering main loop with constraints : #[true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true]
On round 0, found minimizing index 1.
Discard it via constraints.
Setting density at 0 to 1.979514
Setting delete at 0 to 1
On round 1, found minimizing index 26.
Discard it via constraints.
Setting density at 1 to 1.979858
Setting delete at 1 to 26
On round 2, found minimizing index 45.
Discard it via constraints.
Setting density at 2 to 1.980201
Setting delete at 2 to 45
On round 3, found minimizing index 48.
Discard it via constraints.
Setting density at 3 to 1.980545
Setting delete at 3 to 48
On round 4, found minimizing index 49.
Discard it via constraints.
Setting density at 4 to 1.980890
Setting delete at 4 to 49
On round 5, found minimizing index 50.
Discard it via constraints.
Setting density at 5 to 1.981234
Setting delete at 5 to 50
On round 6, found minimizing index 72.
Discard it via constraints.
Setting density at 6 to 1.983646
Setting delete at 6 to 72
On round 7, found minimizing index 108.
Discard it via constraints.
Setting density at 7 to 1.983992
Setting delete at 7 to 108
On round 8, found minimizing index 219.
Discard it via constraints.
Setting density at 8 to 1.984337
Setting delete at 8 to 219
On round 9, found minimizing index 220.
Discard it via constraints.
Setting density at 9 to 1.985719
Setting delete at 9 to 220
On round 10, found minimizing index 234.
Discard it via constraints.
Setting density at 10 to 1.987796
Setting delete at 10 to 234
On round 11, found minimizing index 249.
Discard it via constraints.
Setting density at 11 to 1.988143
Setting delete at 11 to 249
On round 12, found minimizing index 223.
Discard it via constraints.
Setting density at 12 to 1.989009
Setting delete at 12 to 223
On round 13, found minimizing index 84.
Discard it via constraints.
Setting density at 13 to 1.989529
Setting delete at 13 to 84
On round 14, found minimizing index 221.
Discard it via constraints.
Setting density at 14 to 1.990049
Setting delete at 14 to 221
On round 15, found minimizing index 99.
Discard it via constraints.
Setting density at 15 to 1.994570
Setting delete at 15 to 99
On round 16, found minimizing index 47.
Discard it via constraints.
Setting density at 16 to 1.995268
Setting delete at 16 to 47
On round 17, found minimizing index 86.
Discard it via constraints.
Setting density at 17 to 1.997191
Setting delete at 17 to 86
On round 18, found minimizing index 0.
Discard it via constraints.
Setting density at 18 to 2.006378
Setting delete at 18 to 0
On round 19, found minimizing index 69.
Discard it via constraints.
Setting density at 19 to 2.006557
Setting delete at 19 to 69
On round 20, found minimizing index 82.
Discard it via constraints.
Setting density at 20 to 2.006735
Setting delete at 20 to 82
On round 21, found minimizing index 101.
Discard it via constraints.
Setting density at 21 to 2.007271
Setting delete at 21 to 101
On round 22, found minimizing index 151.
Discard it via constraints.
Setting density at 22 to 2.007449
Setting delete at 22 to 151
On round 23, found minimizing index 224.
Discard it via constraints.
Setting density at 23 to 2.007628
Setting delete at 23 to 224
On round 24, found minimizing index 80.
Discard it via constraints.
Setting density at 24 to 2.009780
Setting delete at 24 to 80
On round 25, found minimizing index 81.
Discard it via constraints.
Setting density at 25 to 2.010139
Setting delete at 25 to 81
On round 26, found minimizing index 46.
Discard it via constraints.
Setting density at 26 to 2.012123
Setting delete at 26 to 46
On round 27, found minimizing index 23.
Discard it via constraints.
Setting density at 27 to 2.018329
Setting delete at 27 to 23
On round 28, found minimizing index 27.
Discard it via constraints.
Setting density at 28 to 2.018695
Setting delete at 28 to 27
On round 29, found minimizing index 100.
Discard it via constraints.
Setting density at 29 to 2.019248
Setting delete at 29 to 100
On round 30, found minimizing index 87.
Discard it via constraints.
Setting density at 30 to 2.019618
Setting delete at 30 to 87
On round 31, found minimizing index 93.
Discard it via constraints.
Setting density at 31 to 2.022974
Setting delete at 31 to 93
On round 32, found minimizing index 68.
Discard it via constraints.
Setting density at 32 to 2.045293
Setting delete at 32 to 68
On round 33, found minimizing index 90.
Discard it via constraints.
Setting density at 33 to 2.046878
Setting delete at 33 to 90
On round 34, found minimizing index 91.
Discard it via constraints.
Setting density at 34 to 2.047271
Setting delete at 34 to 91
On round 35, found minimizing index 95.
Discard it via constraints.
Setting density at 35 to 2.048075
Setting delete at 35 to 95
On round 36, found minimizing index 96.
Discard it via constraints.
Setting density at 36 to 2.048469
Setting delete at 36 to 96
On round 37, found minimizing index 79.
Discard it via constraints.
Setting density at 37 to 2.049079
Setting delete at 37 to 79
On round 38, found minimizing index 102.
Discard it via constraints.
Setting density at 38 to 2.049689
Setting delete at 38 to 102
On round 39, found minimizing index 24.
Discard it via constraints.
Setting density at 39 to 2.049896
Setting delete at 39 to 24
On round 40, found minimizing index 39.
Discard it via constraints.
Setting density at 40 to 2.050104
Setting delete at 40 to 39
On round 41, found minimizing index 231.
Discard it via constraints.
Setting density at 41 to 2.057888
Setting delete at 41 to 231
On round 42, found minimizing index 97.
Discard it via constraints.
Setting density at 42 to 2.063719
Setting delete at 42 to 97
On round 43, found minimizing index 2.
Discard it via constraints.
Setting density at 43 to 2.065945
Setting delete at 43 to 2
On round 44, found minimizing index 70.
Discard it via constraints.
Setting density at 44 to 2.068482
Setting delete at 44 to 70
On round 45, found minimizing index 13.
Discard it via constraints.
Setting density at 45 to 2.068717
Setting delete at 45 to 13
On round 46, found minimizing index 22.
Discard it via constraints.
Setting density at 46 to 2.069133
Setting delete at 46 to 22
On round 47, found minimizing index 76.
Discard it via constraints.
Setting density at 47 to 2.189553
Setting delete at 47 to 76
On round 48, found minimizing index 248.
Discard it via constraints.
Setting density at 48 to 2.189860
Setting delete at 48 to 248
On round 49, found minimizing index 67.
Discard it via constraints.
Setting density at 49 to 2.293553
Setting delete at 49 to 67
On round 50, found minimizing index 12.
Discard it via constraints.
Setting density at 50 to 2.296274
Setting delete at 50 to 12
On round 51, found minimizing index 208.
Discard it via constraints.
Setting density at 51 to 2.298525
Setting delete at 51 to 208
On round 52, found minimizing index 246.
Discard it via constraints.
Setting density at 52 to 2.298916
Setting delete at 52 to 246
On round 53, found minimizing index 14.
Discard it via constraints.
Setting density at 53 to 2.320221
Setting delete at 53 to 14
On round 54, found minimizing index 94.
Discard it via constraints.
Setting density at 54 to 2.322750
Setting delete at 54 to 94
On round 55, found minimizing index 136.
Discard it via constraints.
Setting density at 55 to 2.324274
Setting delete at 55 to 136
On round 56, found minimizing index 58.
Discard it via constraints.
Setting density at 56 to 2.327245
Setting delete at 56 to 58
On round 57, found minimizing index 83.
Discard it via constraints.
Setting density at 57 to 2.330949
Setting delete at 57 to 83
On round 58, found minimizing index 244.
Discard it via constraints.
Setting density at 58 to 2.331569
Setting delete at 58 to 244
On round 59, found minimizing index 92.
Discard it via constraints.
Setting density at 59 to 2.349455
Setting delete at 59 to 92
On round 60, found minimizing index 41.
Discard it via constraints.
Setting density at 60 to 2.365782
Setting delete at 60 to 41
On round 61, found minimizing index 85.
Discard it via constraints.
Setting density at 61 to 2.367763
Setting delete at 61 to 85
On round 62, found minimizing index 59.
Discard it via constraints.
Setting density at 62 to 2.368820
Setting delete at 62 to 59
On round 63, found minimizing index 77.
Discard it via constraints.
Setting density at 63 to 2.370946
Setting delete at 63 to 77
On round 64, found minimizing index 129.
Discard it via constraints.
Setting density at 64 to 2.371400
Setting delete at 64 to 129
On round 65, found minimizing index 145.
Discard it via constraints.
Setting density at 65 to 2.373090
Setting delete at 65 to 145
On round 66, found minimizing index 103.
Discard it via constraints.
Setting density at 66 to 2.373919
Setting delete at 66 to 103
On round 67, found minimizing index 78.
Discard it via constraints.
Setting density at 67 to 2.377472
Setting delete at 67 to 78
On round 68, found minimizing index 28.
Discard it via constraints.
Setting density at 68 to 2.379461
Setting delete at 68 to 28
On round 69, found minimizing index 25.
Discard it via constraints.
Setting density at 69 to 2.384251
Setting delete at 69 to 25
On round 70, found minimizing index 31.
Discard it via constraints.
Setting density at 70 to 2.385188
Setting delete at 70 to 31
On round 71, found minimizing index 29.
Discard it via constraints.
Setting density at 71 to 2.385318
Setting delete at 71 to 29
On round 72, found minimizing index 30.
Discard it via constraints.
Setting density at 72 to 2.385787
Setting delete at 72 to 30
On round 73, found minimizing index 42.
Discard it via constraints.
Setting density at 73 to 2.385917
Setting delete at 73 to 42
On round 74, found minimizing index 192.
Discard it via constraints.
Setting density at 74 to 2.386387
Setting delete at 74 to 192
On round 75, found minimizing index 115.
Discard it via constraints.
Setting density at 75 to 2.386518
Setting delete at 75 to 115
On round 76, found minimizing index 116.
Discard it via constraints.
Setting density at 76 to 2.386649
Setting delete at 76 to 116
On round 77, found minimizing index 150.
Discard it via constraints.
Setting density at 77 to 2.386780
Setting delete at 77 to 150
On round 78, found minimizing index 198.
Discard it via constraints.
Setting density at 78 to 2.396803
Setting delete at 78 to 198
On round 79, found minimizing index 164.
Discard it via constraints.
Setting density at 79 to 2.397289
Setting delete at 79 to 164
On round 80, found minimizing index 165.
Discard it via constraints.
Setting density at 80 to 2.397775
Setting delete at 80 to 165
On round 81, found minimizing index 232.
Discard it via constraints.
Setting density at 81 to 2.399512
Setting delete at 81 to 232
On round 82, found minimizing index 156.
Discard it via constraints.
Setting density at 82 to 2.399652
Setting delete at 82 to 156
On round 83, found minimizing index 170.
Discard it via constraints.
Setting density at 83 to 2.399791
Setting delete at 83 to 170
On round 84, found minimizing index 172.
Discard it via constraints.
Setting density at 84 to 2.399930
Setting delete at 84 to 172
On round 85, found minimizing index 177.
Discard it via constraints.
Setting density at 85 to 2.400070
Setting delete at 85 to 177
On round 86, found minimizing index 183.
Discard it via constraints.
Setting density at 86 to 2.400209
Setting delete at 86 to 183
On round 87, found minimizing index 217.
Discard it via constraints.
Setting density at 87 to 2.400349
Setting delete at 87 to 217
On round 88, found minimizing index 222.
Discard it via constraints.
Setting density at 88 to 2.400489
Setting delete at 88 to 222
On round 89, found minimizing index 227.
Discard it via constraints.
Setting density at 89 to 2.401049
Setting delete at 89 to 227
On round 90, found minimizing index 229.
Discard it via constraints.
Setting density at 90 to 2.402029
Setting delete at 90 to 229
On round 91, found minimizing index 230.
Discard it via constraints.
Setting density at 91 to 2.404695
Setting delete at 91 to 230
On round 92, found minimizing index 195.
Discard it via constraints.
Setting density at 92 to 2.439865
Setting delete at 92 to 195
On round 93, found minimizing index 56.
Discard it via constraints.
Setting density at 93 to 2.440236
Setting delete at 93 to 56
On round 94, found minimizing index 269.
Discard it via constraints.
Setting density at 94 to 2.441449
Setting delete at 94 to 269
On round 95, found minimizing index 275.
Discard it via constraints.
Setting density at 95 to 2.443508
Setting delete at 95 to 275
On round 96, found minimizing index 111.
Discard it via constraints.
Setting density at 96 to 2.444069
Setting delete at 96 to 111
On round 97, found minimizing index 123.
Discard it via constraints.
Setting density at 97 to 2.444257
Setting delete at 97 to 123
On round 98, found minimizing index 140.
Discard it via constraints.
Setting density at 98 to 2.444632
Setting delete at 98 to 140
On round 99, found minimizing index 163.
Discard it via constraints.
Setting density at 99 to 2.444820
Setting delete at 99 to 163
On round 100, found minimizing index 98.
Discard it via constraints.
Setting density at 100 to 2.448055
Setting delete at 100 to 98
On round 101, found minimizing index 51.
Discard it via constraints.
Setting density at 101 to 2.448246
Setting delete at 101 to 51
On round 102, found minimizing index 271.
Discard it via constraints.
Setting density at 102 to 2.448438
Setting delete at 102 to 271
On round 103, found minimizing index 273.
Discard it via constraints.
Setting density at 103 to 2.448630
Setting delete at 103 to 273
On round 104, found minimizing index 159.
Discard it via constraints.
Setting density at 104 to 2.448971
Setting delete at 104 to 159
On round 105, found minimizing index 201.
Discard it via constraints.
Setting density at 105 to 2.455961
Setting delete at 105 to 201
On round 106, found minimizing index 122.
Discard it via constraints.
Setting density at 106 to 2.456164
Setting delete at 106 to 122
On round 107, found minimizing index 203.
Discard it via constraints.
Setting density at 107 to 2.456570
Setting delete at 107 to 203
On round 108, found minimizing index 128.
Discard it via constraints.
Setting density at 108 to 2.457347
Setting delete at 108 to 128
On round 109, found minimizing index 132.
Discard it via constraints.
Setting density at 109 to 2.457513
Setting delete at 109 to 132
On round 110, found minimizing index 181.
Discard it via constraints.
Setting density at 110 to 2.457680
Setting delete at 110 to 181
On round 111, found minimizing index 204.
Discard it via constraints.
Setting density at 111 to 2.457848
Setting delete at 111 to 204
On round 112, found minimizing index 233.
Discard it via constraints.
Setting density at 112 to 2.458015
Setting delete at 112 to 233
On round 113, found minimizing index 154.
Discard it via constraints.
Setting density at 113 to 2.458108
Setting delete at 113 to 154
On round 114, found minimizing index 112.
Discard it via constraints.
Setting density at 114 to 2.458070
Setting delete at 114 to 112
On round 115, found minimizing index 175.
Discard it via constraints.
Setting density at 115 to 2.458032
Setting delete at 115 to 175
On round 116, found minimizing index 176.
Discard it via constraints.
Setting density at 116 to 2.457995
Setting delete at 116 to 176
On round 117, found minimizing index 242.
Discard it via constraints.
Setting density at 117 to 2.457919
Setting delete at 117 to 242
On round 118, found minimizing index 261.
Discard it via constraints.
Setting density at 118 to 2.457880
Setting delete at 118 to 261
On round 119, found minimizing index 130.
Discard it via constraints.
Setting density at 119 to 2.457974
Setting delete at 119 to 130
On round 120, found minimizing index 211.
Discard it via constraints.
Setting density at 120 to 2.457534
Setting delete at 120 to 211
On round 121, found minimizing index 89.
Discard it via constraints.
Setting density at 121 to 2.457952
Setting delete at 121 to 89
On round 122, found minimizing index 52.
Discard it via constraints.
Setting density at 122 to 2.458124
Setting delete at 122 to 52
On round 123, found minimizing index 88.
Discard it via constraints.
Setting density at 123 to 2.458085
Setting delete at 123 to 88
On round 124, found minimizing index 109.
Discard it via constraints.
Setting density at 124 to 2.456941
Setting delete at 124 to 109
On round 125, found minimizing index 74.
Discard it via constraints.
Setting density at 125 to 2.457156
Setting delete at 125 to 74
On round 126, found minimizing index 187.
Discard it via constraints.
Setting density at 126 to 2.457327
Setting delete at 126 to 187
On round 127, found minimizing index 138.
Discard it via constraints.
Setting density at 127 to 2.566910
Setting delete at 127 to 138
On round 128, found minimizing index 142.
Discard it via constraints.
Setting density at 128 to 2.576147
Setting delete at 128 to 142
On round 129, found minimizing index 141.
Discard it via constraints.
Setting density at 129 to 2.577723
Setting delete at 129 to 141
On round 130, found minimizing index 114.
Discard it via constraints.
Setting density at 130 to 2.578690
Setting delete at 130 to 114
On round 131, found minimizing index 182.
Discard it via constraints.
Setting density at 131 to 2.580270
Setting delete at 131 to 182
On round 132, found minimizing index 228.
Discard it via constraints.
Setting density at 132 to 2.581239
Setting delete at 132 to 228
On round 133, found minimizing index 280.
Discard it via constraints.
Setting density at 133 to 2.582822
Setting delete at 133 to 280
On round 134, found minimizing index 11.
Discard it via constraints.
Setting density at 134 to 2.590012
Setting delete at 134 to 11
On round 135, found minimizing index 40.
Discard it via constraints.
Setting density at 135 to 2.598513
Setting delete at 135 to 40
On round 136, found minimizing index 113.
Discard it via constraints.
Setting density at 136 to 2.600248
Setting delete at 136 to 113
On round 137, found minimizing index 110.
Discard it via constraints.
Setting density at 137 to 2.602740
Setting delete at 137 to 110
On round 138, found minimizing index 127.
Discard it via constraints.
Setting density at 138 to 2.607255
Setting delete at 138 to 127
On round 139, found minimizing index 199.
Discard it via constraints.
Setting density at 139 to 2.628370
Setting delete at 139 to 199
On round 140, found minimizing index 143.
Discard it via constraints.
Setting density at 140 to 2.629416
Setting delete at 140 to 143
On round 141, found minimizing index 202.
Discard it via constraints.
Setting density at 141 to 2.646597
Setting delete at 141 to 202
On round 142, found minimizing index 8.
Discard it via constraints.
Setting density at 142 to 2.647675
Setting delete at 142 to 8
On round 143, found minimizing index 61.
Discard it via constraints.
Setting density at 143 to 2.649180
Setting delete at 143 to 61
On round 144, found minimizing index 5.
Discard it via constraints.
Setting density at 144 to 2.655013
Setting delete at 144 to 5
On round 145, found minimizing index 119.
Discard it via constraints.
Setting density at 145 to 2.658278
Setting delete at 145 to 119
On round 146, found minimizing index 3.
Discard it via constraints.
Setting density at 146 to 2.660027
Setting delete at 146 to 3
On round 147, found minimizing index 4.
Discard it via constraints.
Setting density at 147 to 2.664447
Setting delete at 147 to 4
On round 148, found minimizing index 35.
Discard it via constraints.
Setting density at 148 to 2.671562
Setting delete at 148 to 35
On round 149, found minimizing index 6.
Discard it via constraints.
Setting density at 149 to 2.672011
Setting delete at 149 to 6
On round 150, found minimizing index 7.
Discard it via constraints.
Setting density at 150 to 2.673128
Setting delete at 150 to 7
On round 151, found minimizing index 247.
Discard it via constraints.
Setting density at 151 to 2.675820
Setting delete at 151 to 247
On round 152, found minimizing index 139.
Discard it via constraints.
Setting density at 152 to 2.678068
Setting delete at 152 to 139
On round 153, found minimizing index 60.
Discard it via constraints.
Setting density at 153 to 2.679892
Setting delete at 153 to 60
On round 154, found minimizing index 137.
Discard it via constraints.
Setting density at 154 to 2.684423
Setting delete at 154 to 137
On round 155, found minimizing index 263.
Discard it via constraints.
Setting density at 155 to 2.693559
Setting delete at 155 to 263
On round 156, found minimizing index 104.
Discard it via constraints.
Setting density at 156 to 2.694030
Setting delete at 156 to 104
On round 157, found minimizing index 124.
Discard it via constraints.
Setting density at 157 to 2.695180
Setting delete at 157 to 124
On round 158, found minimizing index 245.
Discard it via constraints.
Setting density at 158 to 2.697011
Setting delete at 158 to 245
On round 159, found minimizing index 118.
Discard it via constraints.
Setting density at 159 to 2.698910
Setting delete at 159 to 118
On round 160, found minimizing index 120.
Discard it via constraints.
Setting density at 160 to 2.700341
Setting delete at 160 to 120
On round 161, found minimizing index 168.
Discard it via constraints.
Setting density at 161 to 2.701299
Setting delete at 161 to 168
On round 162, found minimizing index 179.
Discard it via constraints.
Setting density at 162 to 2.702259
Setting delete at 162 to 179
On round 163, found minimizing index 243.
Discard it via constraints.
Setting density at 163 to 2.704592
Setting delete at 163 to 243
On round 164, found minimizing index 241.
Discard it via constraints.
Setting density at 164 to 2.705075
Setting delete at 164 to 241
On round 165, found minimizing index 197.
Discard it via constraints.
Setting density at 165 to 2.706327
Setting delete at 165 to 197
On round 166, found minimizing index 107.
Discard it via constraints.
Setting density at 166 to 2.707099
Setting delete at 166 to 107
On round 167, found minimizing index 152.
Discard it via constraints.
Setting density at 167 to 2.721583
Setting delete at 167 to 152
On round 168, found minimizing index 158.
Discard it via constraints.
Setting density at 168 to 2.721902
Setting delete at 168 to 158
On round 169, found minimizing index 36.
Discard it via constraints.
Setting density at 169 to 2.731935
Setting delete at 169 to 36
On round 170, found minimizing index 15.
Discard it via constraints.
Setting density at 170 to 2.744497
Setting delete at 170 to 15
On round 171, found minimizing index 37.
Discard it via constraints.
Setting density at 171 to 2.745083
Setting delete at 171 to 37
On round 172, found minimizing index 38.
Discard it via constraints.
Setting density at 172 to 2.746457
Setting delete at 172 to 38
On round 173, found minimizing index 278.
Discard it via constraints.
Setting density at 173 to 2.748621
Setting delete at 173 to 278
On round 174, found minimizing index 174.
Discard it via constraints.
Setting density at 174 to 2.751582
Setting delete at 174 to 174
On round 175, found minimizing index 214.
Discard it via constraints.
Setting density at 175 to 2.752177
Setting delete at 175 to 214
On round 176, found minimizing index 216.
Discard it via constraints.
Setting density at 176 to 2.753566
Setting delete at 176 to 216
On round 177, found minimizing index 169.
Discard it via constraints.
Setting density at 177 to 2.754972
Setting delete at 177 to 169
On round 178, found minimizing index 272.
Discard it via constraints.
Setting density at 178 to 2.760691
Setting delete at 178 to 272
On round 179, found minimizing index 62.
Discard it via constraints.
Setting density at 179 to 2.778830
Setting delete at 179 to 62
On round 180, found minimizing index 185.
Discard it via constraints.
Setting density at 180 to 2.779602
Setting delete at 180 to 185
On round 181, found minimizing index 213.
Discard it via constraints.
Setting density at 181 to 2.775291
Setting delete at 181 to 213
On round 182, found minimizing index 184.
Discard it via constraints.
Setting density at 182 to 2.779279
Setting delete at 182 to 184
On round 183, found minimizing index 144.
Discard it via constraints.
Setting density at 183 to 2.762749
Setting delete at 183 to 144
On round 184, found minimizing index 121.
Discard it via constraints.
Setting density at 184 to 2.765295
Setting delete at 184 to 121
On round 185, found minimizing index 131.
Discard it via constraints.
Setting density at 185 to 2.767001
Setting delete at 185 to 131
On round 186, found minimizing index 146.
Discard it via constraints.
Setting density at 186 to 2.767857
Setting delete at 186 to 146
On round 187, found minimizing index 153.
Discard it via constraints.
Setting density at 187 to 2.769575
Setting delete at 187 to 153
On round 188, found minimizing index 155.
Discard it via constraints.
Setting density at 188 to 2.771300
Setting delete at 188 to 155
On round 189, found minimizing index 161.
Discard it via constraints.
Setting density at 189 to 2.772166
Setting delete at 189 to 161
On round 190, found minimizing index 173.
Discard it via constraints.
Setting density at 190 to 2.773903
Setting delete at 190 to 173
On round 191, found minimizing index 157.
Discard it via constraints.
Setting density at 191 to 2.775141
Setting delete at 191 to 157
On round 192, found minimizing index 64.
Discard it via constraints.
Setting density at 192 to 2.803894
Setting delete at 192 to 64
On round 193, found minimizing index 274.
Discard it via constraints.
Setting density at 193 to 3.085409
Setting delete at 193 to 274
On round 194, found minimizing index 162.
Discard it via constraints.
Setting density at 194 to 3.092857
Setting delete at 194 to 162
On round 195, found minimizing index 133.
Discard it via constraints.
Setting density at 195 to 3.116152
Setting delete at 195 to 133
On round 196, found minimizing index 117.
Discard it via constraints.
Setting density at 196 to 3.118182
Setting delete at 196 to 117
On round 197, found minimizing index 126.
Discard it via constraints.
Setting density at 197 to 3.126374
Setting delete at 197 to 126
On round 198, found minimizing index 186.
Discard it via constraints.
Setting density at 198 to 3.130275
Setting delete at 198 to 186
On round 199, found minimizing index 196.
Discard it via constraints.
Setting density at 199 to 3.136029
Setting delete at 199 to 196
On round 200, found minimizing index 32.
Discard it via constraints.
Setting density at 200 to 3.138122
Setting delete at 200 to 32
On round 201, found minimizing index 206.
Discard it via constraints.
Setting density at 201 to 3.142066
Setting delete at 201 to 206
On round 202, found minimizing index 218.
Discard it via constraints.
Setting density at 202 to 3.147874
Setting delete at 202 to 218
On round 203, found minimizing index 258.
Discard it via constraints.
Setting density at 203 to 3.150000
Setting delete at 203 to 258
On round 204, found minimizing index 259.
Discard it via constraints.
Setting density at 204 to 3.153989
Setting delete at 204 to 259
On round 205, found minimizing index 260.
Discard it via constraints.
Setting density at 205 to 3.160448
Setting delete at 205 to 260
On round 206, found minimizing index 256.
Discard it via constraints.
Setting density at 206 to 3.162617
Setting delete at 206 to 256
On round 207, found minimizing index 257.
Discard it via constraints.
Setting density at 207 to 3.164794
Setting delete at 207 to 257
On round 208, found minimizing index 205.
Discard it via constraints.
Setting density at 208 to 3.165103
Setting delete at 208 to 205
On round 209, found minimizing index 171.
Discard it via constraints.
Setting density at 209 to 3.164773
Setting delete at 209 to 171
On round 210, found minimizing index 105.
Discard it via constraints.
Setting density at 210 to 3.164122
Setting delete at 210 to 105
On round 211, found minimizing index 106.
Discard it via constraints.
Setting density at 211 to 3.163462
Setting delete at 211 to 106
On round 212, found minimizing index 200.
Discard it via constraints.
Setting density at 212 to 3.132321
Setting delete at 212 to 200
On round 213, found minimizing index 276.
Discard it via constraints.
Setting density at 213 to 3.238806
Setting delete at 213 to 276
On round 214, found minimizing index 71.
Discard it via constraints.
Setting density at 214 to 3.241895
Setting delete at 214 to 71
On round 215, found minimizing index 236.
Discard it via constraints.
Setting density at 215 to 3.247500
Setting delete at 215 to 236
On round 216, found minimizing index 180.
Discard it via constraints.
Setting density at 216 to 3.254408
Setting delete at 216 to 180
On round 217, found minimizing index 54.
Discard it via constraints.
Setting density at 217 to 3.280519
Setting delete at 217 to 54
On round 218, found minimizing index 262.
Discard it via constraints.
Setting density at 218 to 3.340483
Setting delete at 218 to 262
On round 219, found minimizing index 267.
Discard it via constraints.
Setting density at 219 to 3.437673
Setting delete at 219 to 267
On round 220, found minimizing index 178.
Discard it via constraints.
Setting density at 220 to 3.448468
Setting delete at 220 to 178
On round 221, found minimizing index 239.
Discard it via constraints.
Setting density at 221 to 3.464986
Setting delete at 221 to 239
On round 222, found minimizing index 240.
Discard it via constraints.
Setting density at 222 to 3.474719
Setting delete at 222 to 240
On round 223, found minimizing index 167.
Discard it via constraints.
Setting density at 223 to 3.487252
Setting delete at 223 to 167
On round 224, found minimizing index 57.
Discard it via constraints.
Setting density at 224 to 3.508721
Setting delete at 224 to 57
On round 225, found minimizing index 270.
Discard it via constraints.
Setting density at 225 to 3.558209
Setting delete at 225 to 270
On round 226, found minimizing index 277.
Discard it via constraints.
Setting density at 226 to 3.638037
Setting delete at 226 to 277
On round 227, found minimizing index 44.
Discard it via constraints.
Setting density at 227 to 3.646154
Setting delete at 227 to 44
On round 228, found minimizing index 125.
Discard it via constraints.
Setting density at 228 to 3.644860
Setting delete at 228 to 125
On round 229, found minimizing index 43.
Discard it via constraints.
Setting density at 229 to 3.641509
Setting delete at 229 to 43
On round 230, found minimizing index 55.
Discard it via constraints.
Setting density at 230 to 3.608247
Setting delete at 230 to 55
On round 231, found minimizing index 134.
Discard it via constraints.
Setting density at 231 to 3.670455
Setting delete at 231 to 134
On round 232, found minimizing index 268.
Discard it via constraints.
Setting density at 232 to 3.860759
Setting delete at 232 to 268
On round 233, found minimizing index 215.
Discard it via constraints.
Setting density at 233 to 3.891892
Setting delete at 233 to 215
On round 234, found minimizing index 147.
Discard it via constraints.
Setting density at 234 to 3.890411
Setting delete at 234 to 147
On round 235, found minimizing index 148.
Discard it via constraints.
Setting density at 235 to 3.888889
Setting delete at 235 to 148
On round 236, found minimizing index 235.
Discard it via constraints.
Setting density at 236 to 3.882353
Setting delete at 236 to 235
On round 237, found minimizing index 250.
Discard it via constraints.
Setting density at 237 to 3.875000
Setting delete at 237 to 250
On round 238, found minimizing index 252.
Discard it via constraints.
Setting density at 238 to 3.887755
Setting delete at 238 to 252
On round 239, found minimizing index 253.
Discard it via constraints.
Setting density at 239 to 3.880208
Setting delete at 239 to 253
On round 240, found minimizing index 255.
Discard it via constraints.
Setting density at 240 to 3.893617
Setting delete at 240 to 255
On round 241, found minimizing index 210.
Discard it via constraints.
Setting density at 241 to 3.875706
Setting delete at 241 to 210
On round 242, found minimizing index 209.
Discard it via constraints.
Setting density at 242 to 3.899371
Setting delete at 242 to 209
On round 243, found minimizing index 266.
Discard it via constraints.
Setting density at 243 to 3.918367
Setting delete at 243 to 266
On round 244, found minimizing index 33.
Discard it via constraints.
Setting density at 244 to 4.030075
Setting delete at 244 to 33
On round 245, found minimizing index 66.
Discard it via constraints.
Setting density at 245 to 4.285714
Setting delete at 245 to 66
On round 246, found minimizing index 226.
Discard it via constraints.
Setting density at 246 to 4.742857
Setting delete at 246 to 226
On round 247, found minimizing index 251.
Discard it via constraints.
Setting density at 247 to 4.788462
Setting delete at 247 to 251
On round 248, found minimizing index 254.
Discard it via constraints.
Setting density at 248 to 4.834951
Setting delete at 248 to 254
On round 249, found minimizing index 264.
Discard it via constraints.
Setting density at 249 to 5.134021
Setting delete at 249 to 264
On round 250, found minimizing index 63.
Discard it via constraints.
Setting density at 250 to 5.177083
Setting delete at 250 to 63
On round 251, found minimizing index 265.
Discard it via constraints.
Setting density at 251 to 5.276596
Setting delete at 251 to 265
On round 252, found minimizing index 65.
Discard it via constraints.
Setting density at 252 to 5.333333
Setting delete at 252 to 65
On round 253, found minimizing index 166.
Discard it via constraints.
Setting density at 253 to 5.433735
Setting delete at 253 to 166
On round 254, found minimizing index 238.
Discard it via constraints.
Setting density at 254 to 5.400000
Setting delete at 254 to 238
On round 255, found minimizing index 212.
Discard it via constraints.
Setting density at 255 to 5.352113
Setting delete at 255 to 212
On round 256, found minimizing index 21.
Discard it via constraints.
Setting density at 256 to 5.264706
Setting delete at 256 to 21
On round 257, found minimizing index 34.
Discard it via constraints.
Setting density at 257 to 5.227273
Setting delete at 257 to 34
On round 258, found minimizing index 191.
Discard it via constraints.
Setting density at 258 to 5.218750
Setting delete at 258 to 191
On round 259, found minimizing index 225.
Discard it via constraints.
Setting density at 259 to 5.241935
Setting delete at 259 to 225
On round 260, found minimizing index 279.
Discard it via constraints.
Setting density at 260 to 5.300000
Setting delete at 260 to 279
On round 261, found minimizing index 16.
Discard it via constraints.
Setting density at 261 to 5.275862
Setting delete at 261 to 16
On round 262, found minimizing index 160.
Discard it via constraints.
Setting density at 262 to 5.285714
Setting delete at 262 to 160
On round 263, found minimizing index 188.
Discard it via constraints.
Setting density at 263 to 5.333333
Setting delete at 263 to 188
On round 264, found minimizing index 189.
Discard it via constraints.
Setting density at 264 to 5.423077
Setting delete at 264 to 189
On round 265, found minimizing index 190.
Discard it via constraints.
Setting density at 265 to 5.560000
Setting delete at 265 to 190
On round 266, found minimizing index 193.
Discard it via constraints.
Setting density at 266 to 5.750000
Setting delete at 266 to 193
On round 267, found minimizing index 194.
Discard it via constraints.
Setting density at 267 to 6.000000
Setting delete at 267 to 194
On round 268, found minimizing index 281.
Discard it via constraints.
Setting density at 268 to 5.642857
Setting delete at 268 to 281
On round 269, found minimizing index 53.
Discard it via constraints.
Setting density at 269 to 5.236842
Setting delete at 269 to 53
On round 270, found minimizing index 135.
Discard it via constraints.
Setting density at 270 to 4.852941
Setting delete at 270 to 135
On round 271, found minimizing index 237.
Discard it via constraints.
Setting density at 271 to 4.500000
Setting delete at 271 to 237
On round 272, found minimizing index 9.
Discard it via constraints.
Setting density at 272 to 4.000000
Setting delete at 272 to 9
On round 273, found minimizing index 10.
Discard it via constraints.
Setting density at 273 to 3.500000
Setting delete at 273 to 10
On round 274, found minimizing index 17.
Discard it via constraints.
Setting density at 274 to 3.000000
Setting delete at 274 to 17
On round 275, found minimizing index 18.
Discard it via constraints.
Setting density at 275 to 2.500000
Setting delete at 275 to 18
On round 276, found minimizing index 19.
Discard it via constraints.
Setting density at 276 to 2.000000
Setting delete at 276 to 19
On round 277, found minimizing index 20.
Discard it via constraints.
Setting density at 277 to 1.500000
Setting delete at 277 to 20
On round 278, found minimizing index 73.
Discard it via constraints.
Setting density at 278 to 1.000000
Setting delete at 278 to 73
On round 279, found minimizing index 75.
Discard it via constraints.
Setting density at 279 to 0.500000
Setting delete at 279 to 75
On round 280, found minimizing index 149.
Discard it via constraints.
Setting density at 280 to 0.000000
Setting delete at 280 to 149
On round 281, found minimizing index 207.
Discard it via constraints.
Setting density at 281 to 0.000000
Setting delete at 281 to 207
Found minimizing arg wrt. constraints to be 267, od density 6.000000
After comparing to total density (1.979170) : 267
Returning [194, 193, 190, 189, 188, 160, 16, 279, 225, 191, 34, 21, 212, 238, 166, 65, 265, 63, 264, 254, 251, 226, 66, 33, 266, 209, 210, 255, 253, 252, 250, 235, 148, 147, 215, 268, 134, 55, 43, 125, 44, 277, 270, 57, 167, 240, 239, 178, 267, 262, 54, 180, 236, 71, 276, 200, 106, 105, 171, 205, 257, 256, 260, 259, 258, 218, 206, 32, 196, 186, 126, 117, 133, 162, 274, 64, 157, 173, 161, 155, 153, 146, 131, 121, 144, 184, 213, 185, 62, 272, 169, 216, 214, 174, 278, 38, 37, 15, 36, 158, 152, 107, 197, 241, 243, 179, 168, 120, 118, 245, 124, 104, 263, 137, 60, 139, 247, 7, 6, 35, 4, 3, 119, 5, 61, 8, 202, 143, 199, 127, 110, 113, 40, 11, 280, 228, 182, 114, 141, 142, 138, 187, 74, 109, 88, 52, 89, 211, 130, 261, 242, 176, 175, 112, 154, 233, 204, 181, 132, 128, 203, 122, 201, 159, 273, 271, 51, 98, 163, 140, 123, 111, 275, 269, 56, 195, 230, 229, 227, 222, 217, 183, 177, 172, 170, 156, 232, 165, 164, 198, 150, 116, 115, 192, 42, 30, 29, 31, 25, 28, 78, 103, 145, 129, 77, 59, 85, 41, 92, 244, 83, 58, 136, 94, 14, 246, 208, 12, 67, 248, 76, 22, 13, 70, 2, 97, 231, 39, 24, 102, 79, 96, 95, 91, 90, 68, 93, 87, 100, 27, 23, 46, 81, 80, 224, 151, 101, 82, 69, 0, 86, 47, 99, 221, 84, 223, 249, 234, 220, 219, 108, 72, 50, 49, 48, 45, 26, 1]
Entering Charikar with constraints #[false, false, false, false, false, false, false, false, false, true, true, false, false, false, false, false, false, true, true, true, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true]
Entering main loop with constraints : #[false, false, false, false, false, false, false, false, false, true, true, false, false, false, false, false, false, true, true, true, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true]
On round 9, found minimizing index 281.
Discard it via constraints.
Setting density at 9 to 5.642857
Setting delete at 9 to 281
On round 10, found minimizing index 53.
Discard it via constraints.
Setting density at 10 to 5.236842
Setting delete at 10 to 53
On round 17, found minimizing index 135.
Discard it via constraints.
Setting density at 17 to 4.852941
Setting delete at 17 to 135
On round 18, found minimizing index 237.
Discard it via constraints.
Setting density at 18 to 4.500000
Setting delete at 18 to 237
On round 19, found minimizing index 9.
Discard it via constraints.
Setting density at 19 to 4.000000
Setting delete at 19 to 9
On round 20, found minimizing index 10.
Discard it via constraints.
Setting density at 20 to 3.500000
Setting delete at 20 to 10
On round 53, found minimizing index 17.
Discard it via constraints.
Setting density at 53 to 3.000000
Setting delete at 53 to 17
On round 73, found minimizing index 18.
Discard it via constraints.
Setting density at 73 to 2.500000
Setting delete at 73 to 18
On round 75, found minimizing index 19.
Discard it via constraints.
Setting density at 75 to 2.000000
Setting delete at 75 to 19
On round 135, found minimizing index 20.
Discard it via constraints.
Setting density at 135 to 1.500000
Setting delete at 135 to 20
On round 149, found minimizing index 73.
Discard it via constraints.
Setting density at 149 to 1.000000
Setting delete at 149 to 73
On round 207, found minimizing index 75.
Discard it via constraints.
Setting density at 207 to 0.500000
Setting delete at 207 to 75
On round 237, found minimizing index 149.
Discard it via constraints.
Setting density at 237 to 0.000000
Setting delete at 237 to 149
On round 281, found minimizing index 207.
Discard it via constraints.
Setting density at 281 to 0.000000
Setting delete at 281 to 207
Found minimizing arg wrt. constraints to be 9, od density 5.642857
After comparing to total density (0.006943) : 9
Returning [281]
Entering Charikar with constraints #[false, false, false, false, false, false, false, false, false, true, true, false, false, false, false, false, false, true, true, true, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]
Entering main loop with constraints : #[false, false, false, false, false, false, false, false, false, true, true, false, false, false, false, false, false, true, true, true, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]
On round 9, found minimizing index 53.
Discard it via constraints.
Setting density at 9 to 5.236842
Setting delete at 9 to 53
On round 10, found minimizing index 135.
Discard it via constraints.
Setting density at 10 to 4.852941
Setting delete at 10 to 135
On round 17, found minimizing index 237.
Discard it via constraints.
Setting density at 17 to 4.500000
Setting delete at 17 to 237
On round 18, found minimizing index 9.
Discard it via constraints.
Setting density at 18 to 4.000000
Setting delete at 18 to 9
On round 19, found minimizing index 10.
Discard it via constraints.
Setting density at 19 to 3.500000
Setting delete at 19 to 10
On round 20, found minimizing index 17.
Discard it via constraints.
Setting density at 20 to 3.000000
Setting delete at 20 to 17
On round 53, found minimizing index 18.
Discard it via constraints.
Setting density at 53 to 2.500000
Setting delete at 53 to 18
On round 73, found minimizing index 19.
Discard it via constraints.
Setting density at 73 to 2.000000
Setting delete at 73 to 19
On round 75, found minimizing index 20.
Discard it via constraints.
Setting density at 75 to 1.500000
Setting delete at 75 to 20
On round 135, found minimizing index 73.
Discard it via constraints.
Setting density at 135 to 1.000000
Setting delete at 135 to 73
On round 149, found minimizing index 75.
Discard it via constraints.
Setting density at 149 to 0.500000
Setting delete at 149 to 75
On round 207, found minimizing index 149.
Discard it via constraints.
Setting density at 207 to 0.000000
Setting delete at 207 to 149
On round 237, found minimizing index 207.
Discard it via constraints.
Setting density at 237 to 0.000000
Setting delete at 237 to 207
Found minimizing arg wrt. constraints to be 9, od density 5.236842
After comparing to total density (0.006943) : 9
Returning [53]

-/

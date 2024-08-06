

import LeanGrow.Caches.CoData
import LeanGrow.CoClustering
import LeanGrow.AnalyseCoData


open Lean




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

def Array.argmin?_with_constraints [Inhabited α] (A : Array α) (C : Array Bool) (f : α → β) (lt : β → β → Ordering) : Option Nat :=
  Id.run do
    if A.isEmpty
    then return .none
    else
      let mut M := f (A.get! 0)
      let mut I := 0
      let mut i := 0
      for x in A do
        let fx := (f x)
        if (C.get! i) && (lt M fx == .gt)
        then
          M := fx
          I := i
        i := i+1
      return .some I



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

/-
After 20 min:

[AList, List.IsRotated, Function.Involutive, List.Sublist, Relator.LeftUnique, List.IsInfix,
Relator.RightUnique, WellFounded, String, Relator.BiUnique, Relation.ReflTransGen, List.chains,
LevenshteinEstimator', Function.Surjective, Function.RightInverse, Function.LeftInverse,
Function.Bijective, Cycle.Nontrivial, AList.Disjoint]

-/

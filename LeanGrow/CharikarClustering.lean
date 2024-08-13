

import LeanGrow.Caches.CoData
import LeanGrow.CoClustering
import LeanGrow.Caches.goalCoData
import LeanGrow.Caches.CoData_nom


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



def Charikar (apps_float_init : Array Float) (co_float_init : List (Array Float)) (constraints_mut : Array Bool): Elab.Command.CommandElabM (List Nat) := do
  let apps_float := apps_float_init --joined_apps.map Nat.toFloat
  let co_float := co_float_init -- joined_co_pre.map (Array.map Nat.toFloat)
  let mut densities := Array.mkArray apps_float_init.size (0 : Float)
  let mut constraints := constraints_mut -- Array.mkArray apps_float_init.size true
  let mut deletes := Array.mkArray apps_float_init.size 0
  --dbg_trace s!"Entering main loop with constraints : {constraints}"
  for del in (List.range apps_float_init.size) do
    let den (v : Nat) (constraints : Array Bool) := Id.run do
      let mut s := (0 : Float)
      for i in (List.range apps_float_init.size) do
        if !(i == v) && (constraints.get! i) then s := s + (query_wSplits (use_brain v i) co_float)
      return (s / (apps_float.get! v))
    if (constraints_mut.get! del)
    then
      match Array.argmin?_with_constraints (Array.range apps_float_init.size) constraints (den · constraints) Float.compare with
      | .none => throwError "aahh"
      | .some idx =>
          --dbg_trace s!"On round {del}, found minimizing index {idx}.\nDiscard it via constraints."
          constraints := constraints.set! idx false
          let mut D := (0 : Float)
          for x in (List.range apps_float_init.size) do
            if (constraints.get! x)
            then
              for y in (List.range (apps_float_init.size - x - 1)) do
                if (constraints.get! (y + x + 1))
                then D := D + (query_wSplits (use_brain x (y + x + 1)) co_float)
          let mut d := (0 : Float)
          for x in (List.range apps_float_init.size) do
            if (constraints.get! x)
            then d := d + (apps_float.get! x)
          --dbg_trace s!"Setting density at {del} to {D / (max d 1)}"
          densities := densities.set! del (D / (max d 1))
          --dbg_trace s!"Setting delete at {del} to {idx}"
          deletes := deletes.set! del idx
  let .some argm := densities.maxIdx?_with_constraints constraints_mut Float.compare | throwError "ahhh 2"
  --dbg_trace s!"Found minimizing arg wrt. constraints to be {argm}, od density {densities.get! argm}"
  let full_density := Id.run do
                        let mut D := (0 : Float)
                        for x in (List.range apps_float_init.size) do
                          if (constraints_mut.get! x)
                          then
                            for y in (List.range (apps_float_init.size - x - 1)) do
                              if (constraints_mut.get! y)
                              then
                                D := D + (query_wSplits (use_brain x (y + x + 1)) co_float)
                        let mut d := (0 : Float)
                        for x in (List.range apps_float_init.size) do
                          d := d + (apps_float.get! x)
                        return (D / d)
  let argm' := if densities.get! argm < full_density then apps_float_init.size else argm
  --dbg_trace s!"After comparing to total density ({full_density}) : {argm'}"
  let sol := Id.run do
    let mut res := []
    for i in (List.range (argm' + 1)) do
      if (constraints_mut.get! i)
      then
        res := (deletes.get! i) :: res
    return res
  --dbg_trace s!"Returning {sol}"
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


def repeated_split_Charikar (constraints_init : Array Bool) (offset : Nat) := do
  let apps_float := joined_apps.map Nat.toFloat
  let co_float := joined_co_pre.map (Array.map Nat.toFloat)
  let mut constraints := constraints_init
  let mut toSource := []
  for c in (List.range 3) do
    if constraints.contains true
    then
      --dbg_trace s!"Entering Charikar with constraints {constraints}"
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


def repeated_split_Charikar_on_goals (constraints_init : Array Bool) (offset : Nat) := do
  let apps_float := g_joined_apps.map Nat.toFloat
  let co_float := g_joined_co_pre.map (Array.map Nat.toFloat)
  let mut constraints := constraints_init
  let mut toSource := []
  for c in (List.range 3) do
    if constraints.contains true
    then
      --dbg_trace s!"Entering Charikar with constraints {constraints}"
      let sol ← Charikar apps_float co_float constraints
      let t := (SortedTrieFormList' ((sol.map (Trie.get_key · ⟨#[]⟩ g_indexing)).reduceOption))
      toSource := s!"\ndef g_clusTrie_{c + (3*offset)} : Trie Unit := {print_trie t}" :: toSource -- add pdata clusters, of course
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
    toSource_constraints := s!"\ndef g_constraints_split_{co}_{offset} : Array Bool := {a}" :: toSource_constraints
    co := co+1
  toSource_constraints := toSource_constraints.reverse
  let source_apps := (String.join toSource_constraints) ++ s!"\ndef g_constriants_remaining_{offset} : Array Bool := {String.intercalate " ++ " ((List.range (num_splits_apps + 1)).map (s!"g_constraints_split_{·}_{offset}"))}"


  let source := s!"import LeanGrow.NameListCompare\nimport LeanGrow.Caches.goalCoData\nopen Lean Data{String.join toSource}{source_apps}"
  IO.FS.writeFile ⟨s!"/./home/yves/Desktop/CodeWorkspace/Lean4_General/LeanGrow/LeanGrow/Caches/CarikarClustersGoal_batch_{offset}.lean"⟩ (source)

-- 0th batch
--#eval repeated_split_Charikar_on_goals (Array.mkArray g_joined_apps.size true) 0
-- ≈ 45 min ?


-- # Charikar for nomenclature

-- ↓ from nomenclature

def Name.getStringList : Name → List String
| .anonymous => []
| .str p s => s :: (Name.getStringList p)
| .num p _ => Name.getStringList p

def thm_parse' (cache : List Char) : List Char → List String
| [] => [String.mk cache]
| c :: next =>
    if c.isUpper
    then if (String.mk cache ≠ "")
         then (String.mk cache) :: (thm_parse' [c.toLower] next)
         else (thm_parse' [c.toLower] next)
    else if c = '_' || c = ' '
         then (String.mk cache) :: (thm_parse' [] next)
         else thm_parse' (c :: cache) next

def String.reverse (s : String) := String.mk (s.data.reverse)

def thm_parse (s : String ) : List String := (thm_parse' [] s.data).map String.reverse

#eval thm_parse "add_oddEven_le"

#eval Name.getStringList `List.countP_le_length
#eval (Name.getStringList `List.countP_le_length).map thm_parse

-- ↓ new here

elab "make_CoCluster_nom" : command => do
  let env ← getEnv
  let modules := env.header.moduleNames.map ((`Mathlib.Data.List).isPrefixOf ·)
  let mut allnames := Trie.leaf .none
  for (n, i) in env.constants.map₁ do
    let na ← Loogle.isBlackListed n
    if modules[env.const2ModIdx[n].get! (α := Nat)]! && (! na)
    then match i with
         | .thmInfo v | .defnInfo v | .axiomInfo v | .ctorInfo v | .quotInfo v | .recInfo v => do
            let ext_names := SortedTrieFormList' ((Name.getStringList n).map thm_parse).join
            allnames := Trie.merge_count (Trie.merge_count_initialise ext_names) allnames
         | _ => pure ()
  let (indexing, count) := Trie.enumerate 0 allnames

  let mut apps := Array.mkArray count 0
  let mut commons := Array.mkArray ((count*(count - 1) / 2)) 0
  for (n, i) in env.constants.map₁ do
    let na ← Loogle.isBlackListed n
    if modules[env.const2ModIdx[n].get! (α := Nat)]! && (! na)
    then match i with
         | .thmInfo v | .defnInfo v | .axiomInfo v | .ctorInfo v | .quotInfo v | .recInfo v => do
            let keys := ((Name.getStringList n).map thm_parse).join
            let indices := ((keys.map (Trie.find? indexing)).reduceOption)
            let indices2 := ((keys.map (Trie.find? indexing)).reduceOption).pairs
            for (x,y) in indices2 do
              commons := commons.modify ((use_brain x y)) Nat.succ
            for x in indices do
              apps := apps.modify x Nat.succ
         | _ => pure ()


  let split_param := 10
  let num_splits_apps := count / split_param
  let mut a_o_as := Array.mkArray (num_splits_apps + 1)  #[]
  for ca in [0:(num_splits_apps)] do
    let mut A := Array.mkArray (split_param) 0
    for spc in [0:(split_param)] do
      A := A.set! spc (apps.get! (split_param*ca + spc))
    a_o_as := a_o_as.set! ca A
  let mut A := Array.mkArray (count % split_param) 0
  for spc in [0:(count % split_param)] do
    A := A.set! spc (apps.get! (split_param*num_splits_apps + spc))
  a_o_as := a_o_as.set! num_splits_apps A

  let mut toSource_apps := ([] : List String)
  let mut co := 0
  for a in a_o_as do
    toSource_apps := s!"\ndef nom_apps_{co} : Array Nat := {a}" :: toSource_apps
    co := co+1
  toSource_apps := toSource_apps.reverse
  let source_apps := (String.join toSource_apps) ++ s!"\ndef nom_joined_apps := {String.intercalate " ++ " ((List.range (num_splits_apps + 1)).map (s!"nom_apps_{·}"))}"

  let split_param := 10
  let num_splits_co := ((count*(count - 1) / 2)) / split_param
  let mut a_o_as' := Array.mkArray (num_splits_co + 1) #[]
  for ca in [0:(num_splits_co)] do
    let mut A' := Array.mkArray (split_param) 0
    for spc in [0:(split_param)] do
      A' := A'.set! spc (commons.get! (split_param*ca + spc))
    a_o_as' := a_o_as'.set! ca A'
  let mut A' := Array.mkArray (((count*(count - 1) / 2)) % split_param) 0
  for spc in [0:(((count*(count - 1) / 2)) % split_param)] do
    A' := A'.set! spc (commons.get! (split_param*num_splits_co + spc))
  a_o_as' := a_o_as'.set! num_splits_co A'

  let mut toSource_co := []
  let mut co' := 0
  for a in a_o_as' do
    toSource_co := s!"\ndef nom_co_{co'} : Array Nat := {a}" :: toSource_co
    co' := co'+1
  toSource_co := toSource_co.reverse
  let source_co := (String.join toSource_co) ++ s!"\ndef nom_joined_co_pre : List (Array Nat) := {((List.range (num_splits_co + 1)).map (s!"nom_co_{·}"))}"

  let source_allnames := print_trie allnames
  let source_indexing := print_trie indexing
  let source := s!"import LeanGrow.NameListCompare\nopen Lean Data\ndef nom_allnames : Trie Nat := {source_allnames}\ndef nom_indexing : Trie Nat := {source_indexing}{source_apps}{source_co}"
  IO.FS.writeFile ⟨"/./home/yves/Desktop/CodeWorkspace/Lean4_General/LeanGrow/LeanGrow/Caches/CoData_nom.lean"⟩ (source)


--make_CoCluster_nom


def repeated_split_Charikar_on_nom (constraints_init : Array Bool) (offset : Nat) := do
  let apps_float := nom_joined_apps.map Nat.toFloat
  let co_float := nom_joined_co_pre.map (Array.map Nat.toFloat)
  let mut constraints := constraints_init
  let mut toSource := []
  for c in (List.range 3) do
    if constraints.contains true
    then
      --dbg_trace s!"Entering Charikar with constraints {constraints}"
      let sol ← Charikar apps_float co_float constraints
      let t := (SortedTrieFormList' ((sol.map (Trie.get_key · ⟨#[]⟩ nom_indexing)).reduceOption))
      toSource := s!"\ndef nom_clusTrie_{c + (3*offset)} : Trie Unit := {print_trie t}" :: toSource -- add pdata clusters, of course
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
    toSource_constraints := s!"\ndef nom_constraints_split_{co}_{offset} : Array Bool := {a}" :: toSource_constraints
    co := co+1
  toSource_constraints := toSource_constraints.reverse
  let source_apps := (String.join toSource_constraints) ++ s!"\ndef nom_constriants_remaining_{offset} : Array Bool := {String.intercalate " ++ " ((List.range (num_splits_apps + 1)).map (s!"nom_constraints_split_{·}_{offset}"))}"

  let source := s!"import LeanGrow.NameListCompare\nimport LeanGrow.Caches.CoData_nom\nopen Lean Data{String.join toSource}{source_apps}"
  IO.FS.writeFile ⟨s!"/./home/yves/Desktop/CodeWorkspace/Lean4_General/LeanGrow/LeanGrow/Caches/CarikarClustersNom_batch_o_{offset}.lean"⟩ (source)

-- 0th batch
--#eval repeated_split_Charikar_on_nom (Array.mkArray nom_joined_apps.size true) 0
-- ≈ 30 min

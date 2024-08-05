
import LeanGrow.ProcessDecl
import LeanGrow.Blacklisting
import LeanGrow.Quadtree
import LeanGrow.NameListCompare
--import LeanGrow.Caches.mark2cache_v2
import LeanGrow.Caches.mark2cache_v2_big
import LeanGrow.Caches.mark1goalCache_big
import Mathlib

open Lean Data



partial def update_co_appearances (t : QT Nat Nat Wrap) (kx : Nat) (ky : Nat) (f : Nat → Nat) : QT Nat Nat Wrap :=
  QT.update t kx ky (fun z => match z with | .val v => .val (f v) | .postponed T => .postponed (update_co_appearances T kx ky f))

def update_list_main (t : QT Nat Nat Wrap) : List Nat →  QT Nat Nat Wrap
| [] => t
| x :: l => l.foldl (fun y z => update_co_appearances y x z (Nat.succ)) (update_list_main t l)

def update_list (t : QT Nat Nat Wrap) (l : List String) : QT Nat Nat Wrap :=
  let L := (l.map (fun x => (String.hash x).val.val)).mergeSort (· ≤ ·) -- with this and ↑, we get that queies on string should be with hash-smallest as x
  update_list_main t L


def List.pairs : List α → List (α × α)
| [] => []
| x :: l => (l.map (x, ·)) ++ l.pairs

#eval [1,2,3,4,5].pairs





--#exit

elab "cacheCoData" n:name : command =>
  match (Lean.Syntax.isNameLit? n.raw) with
  | none => throwError s!"Error : please enter the correct name of a module to search theorems in."
  | some N => do
        let env ← getEnv
        let modules := env.header.moduleNames.map (N.isPrefixOf ·)
        let res ← env.constants.map₁.foldM (fun hmm decName decInfo => do
                    let na ← Loogle.isBlackListed decName
                    if modules[env.const2ModIdx[decName].get! (α := Nat)]! && (! na)
                    then match decInfo with
                          | .thmInfo v | .defnInfo v | .axiomInfo v | .ctorInfo v | .quotInfo v | .recInfo v => do
                              IO.println s!"Looking at {v.name}"
                              let spice := ((Expr.getConstNames (Expr.getForallBody v.type)).map Name.toString)
                              let L := ((spice.map (fun x => (String.hash x).val.val)).mergeSort (· ≤ ·)).pairs
                              return L.foldl (fun qt p => QT.update qt p.1 p.2 Nat.succ) hmm
                          | _ => return hmm
                      else return hmm) QT.nil
        let toPrint := QT_build 0 UInt64.size 0 UInt64.size (fun x y => match QT.find? res x y with | .some v => v | _ => 0) 3
        let source := s!"import LeanGrow.Quadtree\n" ++ (String.intercalate "\n" (toPrint.map (fun (n,qt) => s!"def {n} : QT Nat Nat Wrap := {QT.toString instToStringNat.toString instToStringNat.toString ValPost.toStringTrick qt}")))
        IO.FS.writeFile ⟨"/./home/yves/Desktop/CodeWorkspace/Lean4_General/LeanGrow/LeanGrow/Caches/CoData.lean"⟩ (source)


-- set_option maxRecDepth 1000
-- set_option maxHeartbeats 0
--cacheCoData `Mathlib.Data.List.Basic
-- massive time then crah


elab "make_CoCluster" : command => do
  let mut allnames := Trie.leaf .none
  for pd in cluster_list do
    allnames := Trie.merge_count (Trie.merge_count_initialise pd.sink_cst_names) allnames
  let (indexing, count) := Trie.enumerate 0 allnames
  let mut commons := Array.mkArray ((count*(count - 1) / 2)) 0
  for pd in cluster_list do
    let keys := (Trie.print_keys ⟨#[]⟩ pd.sink_cst_names)
    let indices := ((keys.map (Trie.find? indexing)).reduceOption).pairs
    for (x,y) in indices do
      commons := commons.modify (((min x y)*(count - 1) + (max x y))) Nat.succ
  let source_allnames := print_trie allnames
  let source_indexing := print_trie indexing
  let source_commons := s!"{commons}"
  let source := s!"import LeanGrow.NameListCompare\nimport LeanGrow.Caches.mark2cache_v2\nopen Lean Data\ndef allnames : Trie Nat := {source_allnames}\ndef indexing : Trie Nat := {source_indexing}\ndef commons : Array Nat := {source_commons}"
  IO.FS.writeFile ⟨"/./home/yves/Desktop/CodeWorkspace/Lean4_General/LeanGrow/LeanGrow/Caches/CoData.lean"⟩ (source)

--make_CoCluster

-- todo split array since its too big :(


def use_brain (x y : Nat) : Nat :=
  let m := min x y
  let M := max x y
  Id.run do
    let mut s := 0
    for j in List.range M do
      s := s + j
    return s + m



elab "make_CoCluster2" : command => do
  let mut allnames := Trie.leaf .none
  for pd in cluster_list do
    allnames := Trie.merge_count (Trie.merge_count_initialise pd.sink_cst_names) allnames
  let (indexing, count) := Trie.enumerate 0 allnames

  let mut apps := Array.mkArray count 0
  for pd in cluster_list do
    let keys := (Trie.print_keys ⟨#[]⟩ pd.sink_cst_names)
    let indices := ((keys.map (Trie.find? indexing)).reduceOption)
    for x in indices do
      apps := apps.modify x Nat.succ

  let mut commons := Array.mkArray ((count*(count - 1) / 2)) 0
  for pd in cluster_list do
    let keys := (Trie.print_keys ⟨#[]⟩ pd.sink_cst_names)
    let indices := ((keys.map (Trie.find? indexing)).reduceOption).pairs
    for (x,y) in indices do
      commons := commons.modify ((use_brain x y)) Nat.succ

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
    toSource_apps := s!"\ndef apps_{co} : Array Nat:= {a}" :: toSource_apps
    co := co+1
  toSource_apps := toSource_apps.reverse
  let source_apps := (String.join toSource_apps) ++ s!"\ndef joined_apps := {String.intercalate " ++ " ((List.range (num_splits_apps + 1)).map (s!"apps_{·}"))}"

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
    toSource_co := s!"\ndef co_{co'} : Array Nat := {a}" :: toSource_co
    co' := co'+1
  toSource_co := toSource_co.reverse
  --let source_co := (String.join toSource_co) ++ s!"\ndef joined_co := {String.intercalate " ++ " ((List.range (num_splits_co + 1)).map (s!"co_{·}"))}"
  --let source_co := (String.join toSource_co) ++ s!"\ndef joined_co := Array.join {((Array.range (num_splits_co + 1)).map (s!"co_{·}"))}"
  -- ↑ first causes stack overflow, second "build failure" on Mathlib.Data.List for split_param 10
  let source_co := (String.join toSource_co) ++ s!"\ndef joined_co_pre : List (Array Nat) := {((List.range (num_splits_co + 1)).map (s!"co_{·}"))}"


  let source_allnames := print_trie allnames
  let source_indexing := print_trie indexing
  let source := s!"import LeanGrow.NameListCompare\nimport LeanGrow.Caches.mark2cache_v2_big\nopen Lean Data\ndef allnames : Trie Nat := {source_allnames}\ndef indexing : Trie Nat := {source_indexing}{source_apps}{source_co}"
  IO.FS.writeFile ⟨"/./home/yves/Desktop/CodeWorkspace/Lean4_General/LeanGrow/LeanGrow/Caches/CoData.lean"⟩ (source)

--make_CoCluster2

elab "make_goalCoCluster2" : command => do
  let mut allnames := Trie.leaf .none
  for pd in goal_cluster_list do
    allnames := Trie.merge_count (Trie.merge_count_initialise pd.name_list) allnames
  let (indexing, count) := Trie.enumerate 0 allnames

  let mut apps := Array.mkArray count 0
  for pd in goal_cluster_list do
    let keys := (Trie.print_keys ⟨#[]⟩ pd.name_list)
    let indices := ((keys.map (Trie.find? indexing)).reduceOption)
    for x in indices do
      apps := apps.modify x Nat.succ

  let mut commons := Array.mkArray ((count*(count - 1) / 2)) 0
  for pd in goal_cluster_list do
    let keys := (Trie.print_keys ⟨#[]⟩ pd.name_list)
    let indices := ((keys.map (Trie.find? indexing)).reduceOption).pairs
    for (x,y) in indices do
      commons := commons.modify ((use_brain x y)) Nat.succ

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
    toSource_apps := s!"\ndef g_apps_{co} : Array Nat:= {a}" :: toSource_apps
    co := co+1
  toSource_apps := toSource_apps.reverse
  let source_apps := (String.join toSource_apps) ++ s!"\ndef g_joined_apps := {String.intercalate " ++ " ((List.range (num_splits_apps + 1)).map (s!"g_apps_{·}"))}"

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
    toSource_co := s!"\ndef g_co_{co'} : Array Nat := {a}" :: toSource_co
    co' := co'+1
  toSource_co := toSource_co.reverse
  --let source_co := (String.join toSource_co) ++ s!"\ndef joined_co := {String.intercalate " ++ " ((List.range (num_splits_co + 1)).map (s!"co_{·}"))}"
  --let source_co := (String.join toSource_co) ++ s!"\ndef joined_co := Array.join {((Array.range (num_splits_co + 1)).map (s!"co_{·}"))}"
  -- ↑ first causes stack overflow, second "build failure" on Mathlib.Data.List for split_param 10
  let source_co := (String.join toSource_co) ++ s!"\ndef g_joined_co_pre : List (Array Nat) := {((List.range (num_splits_co + 1)).map (s!"g_co_{·}"))}"


  let source_allnames := print_trie allnames
  let source_indexing := print_trie indexing
  let source := s!"import LeanGrow.NameListCompare\nimport LeanGrow.Caches.mark1goalCache_big\nopen Lean Data\ndef g_allnames : Trie Nat := {source_allnames}\ndef g_indexing : Trie Nat := {source_indexing}{source_apps}{source_co}"
  IO.FS.writeFile ⟨"/./home/yves/Desktop/CodeWorkspace/Lean4_General/LeanGrow/LeanGrow/Caches/goalCoData.lean"⟩ (source)

--make_goalCoCluster2



elab "make_CoCluster2_qt" : command => do
  let mut allnames := Trie.leaf .none
  for pd in cluster_list do
    allnames := Trie.merge_count (Trie.merge_count_initialise pd.sink_cst_names) allnames
  let (indexing, count) := Trie.enumerate 0 allnames

  -- let mut apps := Array.mkArray count 0
  -- for pd in cluster_list do
  --   let keys := (Trie.print_keys ⟨#[]⟩ pd.sink_cst_names)
  --   let indices := ((keys.map (Trie.find? indexing)).reduceOption)
  --   for x in indices do
  --     apps := apps.modify x Nat.succ

  let mut commons := Array.mkArray ((count*(count - 1) / 2)) 0
  for pd in cluster_list do
    let keys := (Trie.print_keys ⟨#[]⟩ pd.sink_cst_names)
    let indices := ((keys.map (Trie.find? indexing)).reduceOption).pairs
    for (x,y) in indices do
      commons := commons.modify ((use_brain x y)) Nat.succ

  let res_qt := QT_build 0 (count - 1) 0 (count - 1) (fun x y => if x == y then 0 else commons.get! (use_brain x y)) 3
  let qt_source := s!"\n" ++ (String.intercalate "\n" (res_qt.map (fun (n,qt) => s!"def {n} : QT Nat Nat Wrap := {QT.toString instToStringNat.toString instToStringNat.toString ValPost.toStringTrick qt}")))

  -- let split_param := 10
  -- let num_splits_apps := count / split_param
  -- let mut a_o_as := Array.mkArray (num_splits_apps + 1)  #[]
  -- for ca in [0:(num_splits_apps)] do
  --   let mut A := Array.mkArray (split_param) 0
  --   for spc in [0:(split_param)] do
  --     A := A.set! spc (apps.get! (split_param*ca + spc))
  --   a_o_as := a_o_as.set! ca A
  -- let mut A := Array.mkArray (count % split_param) 0
  -- for spc in [0:(count % split_param)] do
  --   A := A.set! spc (apps.get! (split_param*num_splits_apps + spc))
  -- a_o_as := a_o_as.set! num_splits_apps A

  -- let mut toSource_apps := ([] : List String)
  -- let mut co := 0
  -- for a in a_o_as do
  --   toSource_apps := s!"\ndef apps_{co} : Array Nat:= {a}" :: toSource_apps
  --   co := co+1
  -- toSource_apps := toSource_apps.reverse
  -- let source_apps := (String.join toSource_apps) ++ s!"\ndef joined_apps := {String.intercalate " ++ " ((List.range (num_splits_apps + 1)).map (s!"apps_{·}"))}"

  -- let source_allnames := print_trie allnames
  -- let source_indexing := print_trie indexing
  let source := s!"import LeanGrow.Quadtree\nimport LeanGrow.NameListCompare\nimport LeanGrow.Caches.mark2cache_v2_big\nopen Lean Data\n{qt_source}"
  IO.FS.writeFile ⟨"/./home/yves/Desktop/CodeWorkspace/Lean4_General/LeanGrow/LeanGrow/Caches/CoData_qt.lean"⟩ (source)

--make_CoCluster2_qt

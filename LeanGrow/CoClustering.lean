
import LeanGrow.ProcessDecl
import LeanGrow.Blacklisting
import LeanGrow.Quadtree
import LeanGrow.NameListCompare
import LeanGrow.Caches.mark2cache_v2
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

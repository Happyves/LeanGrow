

import LeanGrow.F.Utils.CExprTrie.Unify
import LeanGrow.F.Utils.CExprTrie.Intersect
import LeanGrow.F.Utils.CExprTrie.Unify
import LeanGrow.F.Utils.CExprTrie.Build


open Lean

namespace CExprTrie


partial def applyShift (B : CExprTrie) (shiftIndB : Nat → Nat) : CExprTrie :=
  match B with
  | .dead => B
  | .br lnodes gnodes bvars sorts consts lits apf apa api laf laa lai alf ala ali lef lea lez lei projs =>
      .br
        (lnodes.map (fun (x,y) => (x.map shiftIndB, y)))
        (gnodes.map (fun (x,y) => (x.map shiftIndB, y)))
        (bvars.map (fun (x,y) => (x.map shiftIndB, y)))
        (sorts.map (fun (x,y) => (x.map shiftIndB, y)))
        (consts.map (fun (x,y) => (x.map shiftIndB, y)))
        (lits.map (fun (x,y) => (x.map shiftIndB, y)))
        (applyShift apf shiftIndB) (applyShift apa shiftIndB) (api.map shiftIndB)
        (applyShift laf shiftIndB) (applyShift laa shiftIndB) (lai.map shiftIndB)
        (applyShift alf shiftIndB) (applyShift ala shiftIndB) (ali.map shiftIndB)
        (applyShift lef shiftIndB) (applyShift lea shiftIndB) (applyShift lez shiftIndB) (lei.map shiftIndB)
        (projs.map (fun (x,y,z,w) => (x.map shiftIndB, y,z, applyShift w shiftIndB)))


private def help_merge [BEq α] (A B : List (List Nat × α)) (shiftIndB : Nat → Nat) : List (List Nat × α) :=
  let rec go (done : List (List Nat × α)) : List (List Nat × α) → List (List Nat × α)
    | [] => done
    | nx :: more => go (done.findModifyAdd (fun x => x.2 == nx.2) (fun x => (x.1 ++ nx.1.map shiftIndB, x.2)) (nx.1.map shiftIndB, nx.2)) more
  go A B


private def help_merge_projs (A B : List (List Nat × Name × Nat × CExprTrie)) (shiftIndB : Nat → Nat) (merge : CExprTrie → CExprTrie → CExprTrie)
  : List (List Nat × Name × Nat × CExprTrie) :=
  let rec go (done : List (List Nat × Name × Nat × CExprTrie)) : List (List Nat × Name × Nat × CExprTrie) → List (List Nat × Name × Nat × CExprTrie)
    | [] => done
    | nx :: more => go (done.findModifyAdd (fun x => x.2.1 == nx.2.1 && x.2.2.1 == nx.2.2.1) (fun x => (x.1 ++ nx.1.map shiftIndB, x.2.1, x.2.2.1, merge x.2.2.2 nx.2.2.2)) nx) more
  go A B



partial def merge (A B : CExprTrie) (shiftIndB : Nat → Nat) : CExprTrie :=
  match A, B with
  | .dead, .dead => .dead
  | .br .., .dead => A
  | .dead, .br .. => applyShift B shiftIndB
  | .br lnodes gnodes bvars sorts consts lits apf apa api laf laa lai alf ala ali lef lea lez lei projs, .br lnodes' gnodes' bvars' sorts' consts' lits' apf' apa' api' laf' laa' lai' alf' ala' ali' lef' lea' lez' lei' projs' =>
      .br
        (help_merge lnodes lnodes' shiftIndB)
        (help_merge gnodes gnodes' shiftIndB)
        (help_merge bvars bvars' shiftIndB)
        (help_merge sorts sorts' shiftIndB)
        (help_merge consts consts' shiftIndB)
        (help_merge lits lits' shiftIndB)
        (merge apf apf' shiftIndB) (merge apa apa' shiftIndB) (api ++ (api'.map shiftIndB))
        (merge laf laf' shiftIndB) (merge laa laa' shiftIndB) (lai ++ (lai'.map shiftIndB))
        (merge alf alf' shiftIndB) (merge ala ala' shiftIndB) (ali ++ (ali'.map shiftIndB))
        (merge lef lef' shiftIndB) (merge lea lea' shiftIndB) (merge lez lez' shiftIndB) (lei ++ (lei'.map shiftIndB))
        (help_merge_projs projs projs' shiftIndB (merge · · shiftIndB))


def findMaxIdx (T : CExprTrie) : Nat :=
  let rec max (c : Nat) : List Nat → Nat
    | [] => c
    | nx :: more => if nx > c then max nx more else max c more
  let ind := CExprTrie.getIndices T
  max 0 ind

def merge! (A B : CExprTrie) : CExprTrie :=
  let off := CExprTrie.findMaxIdx A
  CExprTrie.merge A B (fun x => x+off)

-- Probably better to specify the whole SetTrie implementation, as ↑ is inefficient

-- name wrt. SetTrie API
def count (T : CExprTrie) : List (CExpr × Nat) :=
  let ces := CExprTrie.build T
  ces.map (fun (x,y) => (x,y.length))


def find_maxes (cand : List (CExpr × Nat)) : Option (CExprTrie × Nat) :=
  let rec go (max : Nat) (idx : Nat) (T : CExprTrie) : List (CExpr × Nat) → Option (CExprTrie × Nat)
    | [] => .some (T,max)
    | (ce,occ) :: more =>
        match compare occ max with
        | .gt => go occ 2 (CExprTrie.insert ce 1 .dead) more
        | .eq => go max (idx+1) (CExprTrie.insert ce idx T) more
        | .lt => go max idx T more
  go 0 1 .dead cand


def find_max (cand : List (CExpr × Nat)) : Option (CExpr × Nat) :=
  let rec go (good? : Bool) (max : Nat) (ce : CExpr) : List (CExpr × Nat) → Option (CExpr × Nat)
    | [] => if good? then .some (ce, max) else .none
    | nx :: more => if nx.2 > max then go true nx.2 nx.1 more else go true max ce more
  go false 0 .failed cand

/-- Assumes indices from interval from 1 to N, so that N is the size-/
def sizeCanon (T : CExprTrie) : Nat := T.findMaxIdx

def sizeSafe (T : CExprTrie) : Nat :=
  let ind := CExprTrie.getIndices T
  let rec count (c : Nat) (seen : List Nat) : List Nat → Nat
    | [] => c
    | x :: xs =>
        if seen.orderedContains (· ≤ ·) x
        then count c seen xs
        else count (c+1) (seen.orderedInsertOrLeave (· ≤ ·) x) xs
  count 0 [] ind

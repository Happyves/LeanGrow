

import LeanGrow.F.Utils.CExprTrie.Types
import LeanGrow.F.Utils.List

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

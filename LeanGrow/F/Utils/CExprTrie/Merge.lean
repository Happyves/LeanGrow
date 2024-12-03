

import LeanGrow.F.Utils.CExprTrie.Types

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


def merge (A B : CExprTrie) (shiftIndB : Nat → Nat) : CExprTrie :=
  match A, B with
  | .dead, .dead => .dead
  | .br .., .dead => A
  | .dead, .br .. => applyShift B shiftIndB
  | .br lnodes gnodes bvars sorts consts lits apf apa api laf laa lai alf ala ali lef lea lez lei projs, .br lnodes' gnodes' bvars' sorts' consts' lits' apf' apa' api' laf' laa' lai' alf' ala' ali' lef' lea' lez' lei' projs' =>
      .br
        (lnodes ++ (lnodes'.map (fun (x,y) => (x.map shiftIndB, y))))
        (gnodes ++ (gnodes'.map (fun (x,y) => (x.map shiftIndB, y))))
        (bvars ++ (bvars'.map (fun (x,y) => (x.map shiftIndB, y))))
        (sorts ++ (sorts'.map (fun (x,y) => (x.map shiftIndB, y))))
        (consts ++ (consts'.map (fun (x,y) => (x.map shiftIndB, y))))
        (lits ++ (lits'.map (fun (x,y) => (x.map shiftIndB, y))))
        (merge apf apf' shiftIndB) (merge apa apa' shiftIndB) (api ++ (api'.map shiftIndB))
        (merge laf laf' shiftIndB) (merge laa laa' shiftIndB) (lai ++ (lai'.map shiftIndB))
        (merge alf alf' shiftIndB) (merge ala ala' shiftIndB) (ali ++ (ali'.map shiftIndB))
        (merge lef apf' shiftIndB) (merge lea lea' shiftIndB) (merge lez lez' shiftIndB) (lei ++ (lei'.map shiftIndB))
        sorry --(Listprojs (fun (x,y,z,w) => (x.map shiftIndB, y,z, applyShift w shiftIndB)))

#check 1

-- Not it at all...
-- at lnodes etc, we should join the indices of those with common data !

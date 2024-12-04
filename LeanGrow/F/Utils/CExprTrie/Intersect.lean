
import LeanGrow.F.Utils.CExprTrie.Types
import LeanGrow.F.Utils.List

open Lean

namespace CExprTrie


def getIndices : CExprTrie → List Nat
  | .dead => []
  | .br lnodes gnodes bvars sorts consts lits _ _ api _ _ lai _ _ ali _ _ _ lei projs =>
      (lnodes.map Prod.fst).join ++ (gnodes.map Prod.fst).join ++ (bvars.map Prod.fst).join ++
      (sorts.map Prod.fst).join ++ (consts.map Prod.fst).join ++ (lits.map Prod.fst).join ++
      (projs.map Prod.fst).join ++ api ++ lai ++ ali ++ lei

private def merge1 (L R : List (List Nat × List Nat)) : List (List Nat × List Nat) :=
  let rec comp (done : List (List Nat × List Nat)) (l r : List Nat) : List (List Nat × List Nat) → List (List Nat × List Nat)
    | [] => done
    | nx :: more =>
        match List.orderedIntersect (· ≤ ·) nx.1 l, List.orderedIntersect (· ≤ ·) nx.2 r with
        | [], _ => comp done l r more
        | _, [] => comp done l r more
        | x, y =>  comp ((x,y) :: done) l r more
  let rec go (done : List (List Nat × List Nat)) : List (List Nat × List Nat) → List (List Nat × List Nat)
    | [] => done
    | nx :: more => go ((comp [] nx.1 nx.2 R) ++ done) more
  go [] L


private def merge2 [BEq α] (L R : List (List Nat × α)) : List (List Nat × List Nat) :=
  let rec go (done : List (List Nat × List Nat)) : List (List Nat × α) → List (List Nat × List Nat)
    | [] => done
    | nx :: more =>
        match L.find? (fun x => x.2 == nx.2) with
        | .none => [] -- early return
        | .some (i,_) => go ((i,nx.1) :: done) more
  go [] R


private def merge3 (L R : List (List Nat × Name × Nat × CExprTrie))
  (go : CExprTrie → CExprTrie → List (List Nat × List Nat)) : List (List Nat × List Nat) :=
  let rec go (done : List (List Nat × List Nat)) : List (List Nat ×  Name × Nat × CExprTrie) → List (List Nat × List Nat)
    | [] => done
    | nx :: more =>
        match L.find? (fun x => x.2 == nx.2) with
        | .none => [] -- early return
        | .some (i,_) => go ((i,nx.1) :: done) more
  go [] R


--#exit

/--
Context : Q is the ltx trie with gnodes only, t corresponds
to thm inputs with lnodes only
-/
partial def contains (Q t : CExprTrie) : Bool :=
  let rec go (Q t : CExprTrie) : List (List Nat × List Nat) :=
    match Q, t with
    | .dead, .dead => []
    | .br .., .dead => []
    | .dead, .br .. => []
    | .br _ gnodes bvars sorts consts lits apf apa api laf laa lai alf ala ali lef lea lez lei projs,
      .br lnodes' _ bvars' sorts' consts' lits' apf' apa' api' laf' laa' lai' alf' ala' ali' lef' lea' lez' lei' projs' =>
        if (api.isEmpty && !api'.isEmpty) || (lai.isEmpty && !lai'.isEmpty) || (ali.isEmpty && !ali'.isEmpty) || (lei.isEmpty && !lei'.isEmpty)
        then [] --early return
        else
          let IQ := Q.getIndices
          let IL := lnodes'.map (fun x => (IQ,x.1))
          let IB := merge2 bvars bvars'
          let IS := merge2 sorts sorts'
          let IC := merge2 consts consts'
          let ILi := merge2 lits lits'
          if (!bvars.isEmpty && !bvars'.isEmpty && IB.isEmpty) || (!sorts.isEmpty && !sorts'.isEmpty && IS.isEmpty) || (!lits.isEmpty && !lits'.isEmpty && IC.isEmpty) || (!bvars.isEmpty && !bvars'.isEmpty && ILi.isEmpty)
          then [] -- early return
          else
            if !api'.isEmpty
            then
              merge1 (go apf apf') (go apa apa')
            else



  sorry


#check Bool.xor

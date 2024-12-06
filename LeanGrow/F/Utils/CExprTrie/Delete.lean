
import LeanGrow.F.Utils.CExprTrie.Query
import Mathlib.Data.List.Sort
import LeanGrow.F.Utils.CExprTrie.Unify


open Lean

namespace CExprTrie


private def deleteInd_help (L : List (List Nat × α)) (idx : Nat) :  Option (List (List Nat × α)) :=
  let rec go (done : List (List Nat × α)) : List (List Nat × α) →  Option (List (List Nat × α))
    | [] => .none
    | nx :: more =>
        if List.orderedContains (· ≤ ·) idx nx.1
        then ((List.orderedEraseOrLeave (· ≤ ·) idx nx.1, nx.2) :: done ) ++ more
        else go (nx :: done) more
  go [] L

private def deleteInd_help_proj (L : List (List Nat × Name × Nat × CExprTrie)) (idx : Nat)
  (deleteInd : Nat → CExprTrie → CExprTrie)
  :  Option (List (List Nat × Name × Nat × CExprTrie)) :=
  let rec go (done : List (List Nat × Name × Nat × CExprTrie)) : List (List Nat × Name × Nat × CExprTrie) →  Option (List (List Nat × Name × Nat × CExprTrie))
    | [] => .none
    | nx :: more =>
        if List.orderedContains (· ≤ ·) idx nx.1
        then ((List.orderedEraseOrLeave (· ≤ ·) idx nx.1, nx.2.1, nx.2.2.1, deleteInd idx nx.2.2.2) :: done ) ++ more
        else go (nx :: done) more
  go [] L


partial def deleteInd (idx : Nat) (T : CExprTrie) : CExprTrie :=
  let rec go : CExprTrie → CExprTrie
    | .dead => .dead
    | .br lnodes gnodes bvars sorts consts lits apf apa api laf laa lai alf ala ali lef lea lez lei projs =>
        match deleteInd_help lnodes idx with
        | .some new =>
            .br new gnodes bvars sorts consts lits apf apa api laf laa lai alf ala ali lef lea lez lei projs
        | _ =>
          match deleteInd_help gnodes idx with
          | .some new =>
              .br lnodes new bvars sorts consts lits apf apa api laf laa lai alf ala ali lef lea lez lei projs
          | _ =>
            match deleteInd_help bvars idx with
            | .some new =>
                .br lnodes gnodes new sorts consts lits apf apa api laf laa lai alf ala ali lef lea lez lei projs
            | _ =>
              match deleteInd_help sorts idx with
              | .some new =>
                  .br lnodes gnodes bvars new consts lits apf apa api laf laa lai alf ala ali lef lea lez lei projs
              | _ =>
                match deleteInd_help consts idx with
                | .some new =>
                    .br lnodes gnodes bvars sorts new lits apf apa api laf laa lai alf ala ali lef lea lez lei projs
                | _ =>
                  match deleteInd_help lits idx with
                  | .some new =>
                      .br lnodes gnodes bvars sorts consts new apf apa api laf laa lai alf ala ali lef lea lez lei projs
                  | _ =>
                    if List.orderedContains (· ≤ ·) idx api
                    then
                      .br lnodes gnodes bvars sorts consts lits (deleteInd idx apf) (deleteInd idx apa) (List.orderedEraseOrLeave (· ≤ ·) idx api) laf laa lai alf ala ali lef lea lez lei projs
                    else
                      if List.orderedContains (· ≤ ·) idx lai
                      then
                        .br lnodes gnodes bvars sorts consts lits apf apa api (deleteInd idx laf) (deleteInd idx laa) (List.orderedEraseOrLeave (· ≤ ·) idx lai) alf ala ali lef lea lez lei projs
                      else
                        if List.orderedContains (· ≤ ·) idx ali
                        then
                          .br lnodes gnodes bvars sorts consts lits apf apa api laf laa lai (deleteInd idx alf) (deleteInd idx ala) (List.orderedEraseOrLeave (· ≤ ·) idx ali) lef lea lez lei projs
                        else
                          if List.orderedContains (· ≤ ·) idx lei
                          then
                            .br lnodes gnodes bvars sorts consts lits apf apa api laf laa lai  alf ala ali (deleteInd idx lef) (deleteInd idx lea) (deleteInd idx lez) (List.orderedEraseOrLeave (· ≤ ·) idx lei) projs
                          else
                            match deleteInd_help_proj projs idx deleteInd with
                            | .some new => .br lnodes gnodes bvars sorts consts lits apf apa api laf laa lai alf ala ali lef lea lez lei new
                            | _ => .br lnodes gnodes bvars sorts consts lits apf apa api laf laa lai alf ala ali lef lea lez lei projs
  go T


def deleteCExpr (T : CExprTrie) (ce : CExpr) : CExprTrie :=
  match T.find? ce with
  | [] => T
  | inds => inds.foldl (fun x y => x.deleteInd y) T


def difference (A B : CExprTrie) : CExprTrie :=
  let bB := B.build.map Prod.fst
  bB.foldl CExprTrie.deleteCExpr A


#exit

/-

The approach ↓ is nonesense.

It would retuurn an empty tree for T[a b, x y] \ T[a y, x b]

-/

private def reIndex (sorted_deletes : List Nat) (ind : Nat) : Nat :=
  let rec countDec (count : Nat) : List Nat → Nat
    | [] => count
    | nx :: more => if nx < ind then countDec (count + 1) more else count
  ind - (countDec 0 sorted_deletes)


#eval List.mergeSort (· ≤ ·) [2,1,3]


private def help_dif [BEq α] (A B : List (List Nat × α)) : List (List Nat × α) × List Nat :=
  let rec erase (k : α) (done : List (List Nat × α)) : List (List Nat × α) → List (List Nat × α) × Bool
    | [] => (done, false)
    | nx :: more => if nx.2 == k then (done ++ more, true) else erase k (nx :: done) more
  let rec go (done : List (List Nat × α)) (deleted : List Nat) : List (List Nat × α) → List (List Nat × α) × List Nat
    | [] => (done, deleted)
    | nx :: more =>
        let (cleaned, or?) := erase nx.2 [] done
        if or?
        then go cleaned (nx.1 ++ deleted) more
        else go done deleted more
  go A [] B

#eval List.dedup  [1,2,2,3]

#check List.erase

-- List (List ℕ × Name × ℕ × CExprTrie)


private def help_dif_projs (A B : List (List Nat × Name × ℕ × CExprTrie))
  (difgo : CExprTrie → CExprTrie → CExprTrie × List Nat)
  : List (List Nat × Name × ℕ × CExprTrie) × List Nat :=
  let rec erase (kn : Name) (ki : Nat) (kt : CExprTrie) (done : List (List Nat × Name × ℕ × CExprTrie)) : List (List Nat × Name × ℕ × CExprTrie) → List (List Nat × Name × ℕ × CExprTrie) × List Nat
    | [] => (done, [])
    | nx :: more =>
        if nx.2.1 == kn && nx.2.2.1 == ki
        then
          let (new, dels) := difgo nx.2.2.2 kt
          ((nx.1, nx.2.1, nx.2.2.1, new) :: (done ++ more), dels)
        else erase kn ki kt (nx :: done) more
  let rec go (done : List (List Nat × Name × ℕ × CExprTrie)) (deleted : List Nat) : List (List Nat × Name × ℕ × CExprTrie) → List (List Nat × Name × ℕ × CExprTrie) × List Nat
    | [] => (done, deleted)
    | nx :: more =>
        let (cleaned, or?) := erase nx.2.1 nx.2.2.1 nx.2.2.2 [] done
        match or? with
        | _ :: _ => go cleaned (nx.1 ++ deleted) more
        | _ => go done deleted more
  go A [] B



partial def difference (A B : CExprTrie) : CExprTrie :=
  let rec go (A B : CExprTrie) : CExprTrie × List Nat :=
    match A, B with
    | .dead, _ => (.dead, [])
    | .br .., .dead => (A, [])
    | .br lnodes gnodes bvars sorts consts lits apf apa api laf laa lai alf ala ali lef lea lez lei projs,
      .br lnodes' gnodes' bvars' sorts' consts' lits' apf' apa' _ laf' laa' _ alf' ala' _ lef' lea' lez' _ projs' =>
          let (ln,lnd) := help_dif lnodes lnodes'
          let (gn,gnd) := help_dif gnodes gnodes'
          let (bv,bvd) := help_dif bvars bvars'
          let (so,sod) := help_dif sorts sorts'
          let (co,cod) := help_dif consts consts'
          let (li,lid) := help_dif lits lits'
          let (napf,apfd) := go apf apf'
          let (napa,apad) := go apa apa'
          let (nlaf,lafd) := go laf laf'
          let (nlaa,laad) := go laa laa'
          let (nalf,alfd) := go alf alf'
          let (nala,alad) := go ala ala'
          let (nlef,lefd) := go lef lef'
          let (nlea,lead) := go lea lea'
          let (nlez,lezd) := go lez lez'
          let (npr, prd) := help_dif_projs projs projs' go
          let dels := (lnd ++ gnd ++ bvd ++ sod ++ cod ++ lid ++ apfd ++ apad ++ lafd ++ laad ++ alfd ++ alad ++ lefd ++ lead ++ lezd ++ prd).dedup.mergeSort (· ≤ ·)
          let BR := CExprTrie.br
            (ln.map (fun (x,y) => (x.map (reIndex dels),y)))
            (gn.map (fun (x,y) => (x.map (reIndex dels),y)))
            (bv.map (fun (x,y) => (x.map (reIndex dels),y)))
            (so.map (fun (x,y) => (x.map (reIndex dels),y)))
            (co.map (fun (x,y) => (x.map (reIndex dels),y)))
            (li.map (fun (x,y) => (x.map (reIndex dels),y)))
            napf napa (((apfd ++ apad).foldl List.erase api).map (reIndex dels))
            nlaf nlaa (((lafd ++ laad).foldl List.erase lai).map (reIndex dels))
            nalf nala (((alfd ++ alad).foldl List.erase ali).map (reIndex dels))
            nlef nlea nlez (((lefd ++ lead ++ lezd).foldl List.erase lei).map (reIndex dels))
            (npr.map (fun (x,y) => (x.map (reIndex dels),y)))
          (BR, dels)
  (go A B).1

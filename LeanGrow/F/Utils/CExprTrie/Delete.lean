
import LeanGrow.F.Utils.CExprTrie.Query


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


def deleteCExpr (ce : CExpr) (T : CExprTrie) : CExprTrie :=
  match T.find? ce with
  | [] => T
  | inds => inds.foldl (fun x y => x.deleteInd y) T

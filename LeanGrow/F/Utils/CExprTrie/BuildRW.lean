

import LeanGrow.F.Utils.CExprTrie.Types
import LeanGrow.F.Utils.List

open Lean

namespace CExprTrie


partial def build_target (T : CExprTrie) (idx : Nat) : CExpr :=
  match T with
  | .dead => .failed
  | .br lnodes gnodes bvars sorts consts lits apf apa api laf laa lai alf ala ali lef lea lez lei projs =>
        match lnodes.find? (fun x => List.orderedContains (· ≤ ·) idx x.1) with
        | .some (_,i,t) => .lnode i (.ofBvar 42) t
        | _ =>
          match gnodes.find? (fun x => List.orderedContains (· ≤ ·) idx x.1) with
          | .some (_,i) => .gnode i (.ofBvar 42)
          | _ =>
            match bvars.find? (fun x => List.orderedContains (· ≤ ·) idx x.1) with
            | .some (_,i) => .bvar i
            | _ =>
              match sorts.find? (fun x => List.orderedContains (· ≤ ·) idx x.1) with
              | .some (_,i) => .sort i
              | _ =>
                match consts.find? (fun x => List.orderedContains (· ≤ ·) idx x.1) with
                | .some (_,n,l) => .const n l
                | _ =>
                  match lits.find? (fun x => List.orderedContains (· ≤ ·) idx x.1) with
                  | .some (_,i) => .lit i
                  | _ =>
                    if List.orderedContains (· ≤ ·) idx api
                    then .app (build_target apf idx) (build_target apa idx)
                    else
                      if List.orderedContains (· ≤ ·) idx lai
                      then .lam `dummy (build_target laf idx) (build_target laa idx) .default
                      else
                        if List.orderedContains (· ≤ ·) idx ali
                        then .forallE `dummy (build_target alf idx) (build_target ala idx) .default
                        else
                          if List.orderedContains (· ≤ ·) idx lei
                          then .letE `dummy (build_target lef idx) (build_target lea idx) (build_target lez idx) true
                          else
                            match projs.find? (fun x => List.orderedContains (· ≤ ·) idx x.1) with
                            | .some (_,n,i,t) => .proj n i (build_target t idx)
                            | _ => .failed





partial def factor_with (T : CExprTrie) (idx : Nat) (dirs : List oDirs) (insert : Nat → CExpr) : CExpr :=
    let rec go (depth : Nat) (T : CExprTrie) (dirs : List oDirs) : CExpr :=
      match T with
      | .dead => .failed
      | .br _ _ _ _ _ _ apf apa _ laf laa _ alf ala _ lef lea lez _ projs =>
        match dirs with
        | [] => insert depth
        | nx :: more =>
            match nx with
            | .apf => .app (go depth apf more) (apa.build_target idx)
            | .apa => .app (apf.build_target idx) (go depth apa more)
            | .laf => .lam `dummy (go depth laf more) (laa.build_target idx) .default
            | .laa => .lam `dummy (laf.build_target idx) (go (depth+1) laa more) .default
            | .alf => .forallE `dummy (go depth alf more) (ala.build_target idx) .default
            | .ala => .forallE `dummy (alf.build_target idx) (go (depth+1) ala more) .default
            | .lef => .letE `dummy (go depth lef more) (lea.build_target idx) (lez.build_target idx) true
            | .lea => .letE `dummy (lef.build_target idx) (go depth lea more) (lez.build_target idx) true
            | .lez => .letE `dummy (lef.build_target idx) (lea.build_target idx) (go (depth+1) lez more) true
            | .pro n i =>
                match List.find? (fun x => x.2.1 == n && x.2.2.1 == i) projs with
                | .some (_,_,_,t) => .proj n i (go depth t more)
                | _ => .failed
    go 0 T dirs



def factor (T : CExprTrie) (idx : Nat) (dirs : List oDirs) : CExpr :=
  (CExprTrie.factor_with T idx dirs (fun d => .bvar d))

def buildRWtype (T : CExprTrie) (idx : Nat) (dirs : List oDirs) (replacement : CExpr) : CExpr :=
  CExprTrie.factor_with T idx dirs (fun _ => replacement)

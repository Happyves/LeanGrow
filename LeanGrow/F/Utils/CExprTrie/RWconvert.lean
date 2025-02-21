import LeanGrow.F.Utils.CExprTrie.Query
import Lean
import LeanGrow.F.Data.CExpr.API
import Mathlib.Data.List.Sort
import LeanGrow.F.Data.CExpr.ReduceInferMuggle.Reduce

open Lean

#check 1

/-
We want:
- conservative conversion : if its supposed to replace unification, we shouldn't throw to many false
  positives, since it will be costly to propagate and analyse clashes for unification we expect to be
  false most of the time.
- liberal congruence : assuming the equalities we see among goals aren't nonsensical most of the time
  (which is the job of conversion), liberal congruence should counter our lack of congruence closure
-/



/-
Conversion
- delta(-beta-iota ?)
- proof irrelevance
- count the appearance of pairs to convert : we seek large average appearances

Actually, conversion will constitute a new entry to backtree, that is a mix of
ofUni and of ofBack with ofRW Backtype ...
-/

#check oDirs

partial def convertRequirements (fctx : FixCtx)
  (patternTrie : CExprTrie) -- should contain both sides of all equations in ltx ; used as heuristic to greenlight conversion
  (cand goal : CExpr) :
  Option ( -- return none,
      List ((Nat × Option Nat) × CExpr) -- lnodes match-ups
      × List (List oDirs × CExpr × CExpr)) -- locations and patterns of cand and goal (in that order) to equate as subgoals
      :=
  let rec go (sf_match : List ((Nat × Option Nat) × CExpr)) (sf_eq : List (List oDirs × CExpr × CExpr)) :
    List (List CExpr × List oDirs × CExpr × CExpr) → Option (List ((Nat × Option Nat) × CExpr) × List (List oDirs × CExpr × CExpr))
      | [] => (sf_match,sf_eq)
      | (bvarCtx,ds,cec,ceg) :: more =>
          match cec, ceg with
          | _, .lnode p _ t =>
            go (((p,t), cec) :: sf_match) sf_eq more
          | .app cf ca, .app gf ga =>
            go sf_match sf_eq ((bvarCtx,.apf :: ds,cf,gf) :: (bvarCtx,.apa :: ds,ca, ga) :: more)
          | _, _ => -- similar for λ ∀ let, but adapt bvar conetxt !!!
            -- here, we only have the code that proceeds if they're different
            let cT := CExpr.inferType fctx cec -- add bvar context !
            let gT := CExpr.inferType fctx ceg
            let P? := CExpr.whnf fctx (CExpr.inferType fctx cT)
            if P? == .sort 0 && cT == gT
            then -- skip proofs since kernel will not complain
              go sf_match sf_eq more
            else
              let cpat? := patternTrie.find? cec
              if cpat?.isEmpty
              then
                -- if we currently have no eq thms involving the pattern, we don't
                -- convert ; note that this means we should retry conversions that failed,
                -- if new eqs were added to ltx
                .none
              else
                let gpat? := patternTrie.find? ceg -- may contain lnodes... we don't care
                if gpat?.isEmpty
                then
                  .none
                else
                  go sf_match ((ds, cec,ceg) :: sf_eq) more
  let res := go [] [] [([],[],cand,goal)]
  match res with
  | .none => .none
  | .some (mat,eqs) =>
    let rec appears (done : List (Nat × CExpr × CExpr)) : List (List oDirs × CExpr × CExpr) → List (Nat × CExpr × CExpr)
      | [] => done
      | x :: xs => appears (done.findModifyAdd (fun y => y.2 == x.2) (fun z => (z.1 +1, z.2)) (1,x.2)) xs
    let aps := appears [] eqs
    sorry
    /-
    Multiple criteria to dismiss conversion here:
    - High average number of appearances
    - High minimum number of appearances
    Actually, these criteria should only count for the dependency
    sources. For example, if only one rewrite would be required for
    the converstion, but it has a lot of dependencies, then the
    dependecies will be among the cexpr to euqate, but with a small
    number of appearances (typically 1).
    -/




--#exit

/-
Congruence
- determine tree of different locations
- proceed as for rewrites : disjoin app, λ and ∀ cases, except that we don't need
  to search for inner dependencies ? After all, both terms should be type correct,
  so if they differ at some part, the locations depending on that part should also
  differ ?
  So carry out app rewrites as with std ones, but with prescribed dependencies instead
  of the forced ones. Problem of handling simutaneous differences in binder type and body.
  Note: if there is a difference in a binder type, there should also be one in the body, though
  this isn't necessarily the case, as we could have a body constant in the binder.
  Actually, it is possible to rewrite simltaneously, as is described in test29_2 and test33_2
- at differing locations, check if terms are proof of same and close with proof_irrel if so,
  or not because the kernel has proof irrelevance by default !?!

-/


theorem testPI (n m : Nat) (p1 p2 : m < n) : Fin.mk m p1 = Fin.mk m p2 := rfl


#check pi_congr


import LeanGrow.F.Utils.CExprTrie.Types
import LeanGrow.F.Utils.List


open Lean

namespace CExprTrie


def find? (ce : CExpr) (T : CExprTrie) : List Nat :=
  let rec go (ce : CExpr) : CExprTrie → List Nat
    | .dead => []
    | .br lnodes gnodes bvars sorts consts lits apf apa api laf laa lai alf ala ali lef lea lez lei projs =>
      match ce with
      | .app f a =>
          match api with
          | [] => []
          | _ => List.orderedIntersect (· ≤ ·) (find? f apf) (find? a apa)
      | .lam _ f a _  =>
          match lai with
          | [] => []
          | _ => List.orderedIntersect (· ≤ ·) (find? f laf) (find? a laa)
      | .forallE _ f a _  =>
          match ali with
          | [] => []
          | _ => List.orderedIntersect (· ≤ ·) (find? f alf) (find? a ala)
      | .letE _ f a z _ =>
          match lei with
          | [] => []
          | _ => List.orderedIntersect (· ≤ ·) (List.orderedIntersect (· ≤ ·) (find? f lef) (find? a lea)) (find? z lez)
      | .proj n i e =>
          let found := List.find? (fun x => x.2.1 == n && x.2.2.1 == i) projs
          match found with
          | .none => []
          | .some x => find? e x.2.2.2
      | .lnode p _ t =>
          let found := List.find? (fun x => x.2.1 == p && x.2.2 == t) lnodes
          match found with
          | .none => []
          | .some x => x.1
      | .gnode p _ =>
          let found := List.find? (fun x => x.2 == p ) gnodes
          match found with
          | .none => []
          | .some x => x.1
      | .bvar p =>
          let found := List.find? (fun x => x.2 == p ) bvars
          match found with
          | .none => []
          | .some x => x.1
      | .sort p  =>
          let found := List.find? (fun x => x.2 == p ) sorts
          match found with
          | .none => []
          | .some x => x.1
      | .const n l =>
          let found := List.find? (fun x => x.2.1 == n && x.2.2 == l ) consts
          match found with
          | .none => []
          | .some x => x.1
      | .lit p  =>
          let found := List.find? (fun x => x.2 == p ) lits
          match found with
          | .none => []
          | .some x => x.1
      | .failed => []
  go ce T


def getIndices_copy : CExprTrie → List Nat
  | .dead => []
  | .br lnodes gnodes bvars sorts consts lits _ _ api _ _ lai _ _ ali _ _ _ lei projs =>
      (lnodes.map Prod.fst).join ++ (gnodes.map Prod.fst).join ++ (bvars.map Prod.fst).join ++
      (sorts.map Prod.fst).join ++ (consts.map Prod.fst).join ++ (lits.map Prod.fst).join ++
      (projs.map Prod.fst).join ++ api ++ lai ++ ali ++ lei


/--
Actually, we should build the tries, and run goal-match-unification for each !
... If we build we might have loose bvars ?!
Also, mkae version that doesn't unify with cexprtrie that has loose bvars (which
requires to keep track of depth)
-/
def findMatch? (ce : CExpr) (T : CExprTrie) : List Nat × (List (Nat × CExprTrie)) :=
  let rec go (ce : CExpr) : CExprTrie → List Nat × (List (Nat × CExprTrie))
    | .dead => ([],[])
    | B@(.br lnodes gnodes bvars sorts consts lits apf apa api laf laa lai alf ala ali lef lea lez lei projs) =>
      match ce with
      | .app f a =>
          match api with
          | [] => ([],[])
          | _ =>
            let resf := (findMatch? f apf)
            let resa := (findMatch? a apa)
            match List.orderedIntersect (· ≤ ·) resf.1 resa.1 with
            | [] => ([],[])
            | I => (I,resf.2 ++ resa.2)
      | .lam _ f a _  =>
          match lai with
          | [] => ([],[])
          | _ =>
            let resf := (findMatch? f laf)
            let resa := (findMatch? a laa)
            match List.orderedIntersect (· ≤ ·) resf.1 resa.1 with
            | [] => ([],[])
            | I => (I,resf.2 ++ resa.2)
      | .forallE _ f a _  =>
            let resf := (findMatch? f alf)
            let resa := (findMatch? a ala)
            match List.orderedIntersect (· ≤ ·) resf.1 resa.1 with
            | [] => ([],[])
            | I => (I,resf.2 ++ resa.2)
      | .letE _ f a z _ =>
            let resf := (findMatch? f lef)
            let resa := (findMatch? a lea)
            let resz := (findMatch? z lez)
            match List.orderedIntersect (· ≤ ·) (List.orderedIntersect (· ≤ ·) resf.1 resa.1) resz.1 with
            | [] => ([],[])
            | I => (I,resf.2 ++ resa.2 ++ resz.2)
      | .proj n i e =>
          let found := List.find? (fun x => x.2.1 == n && x.2.2.1 == i) projs
          match found with
          | .none => ([],[])
          | .some x => findMatch? e x.2.2.2
      | .lnode p _ .none =>
          let ind := getIndices_copy B
          (ind,[(p,B)])
      | .gnode p _ =>
          let found := List.find? (fun x => x.2 == p ) gnodes
          match found with
          | .none => ([],[])
          | .some x => (x.1,[])
      | .bvar p =>
          let found := List.find? (fun x => x.2 == p ) bvars
          match found with
          | .none => ([],[])
          | .some x => (x.1,[])
      | .sort p  =>
          let found := List.find? (fun x => x.2 == p ) sorts
          match found with
          | .none => ([],[])
          | .some x => (x.1,[])
      | .const n l =>
          let found := List.find? (fun x => x.2.1 == n && x.2.2 == l ) consts
          match found with
          | .none => ([],[])
          | .some x => (x.1,[])
      | .lit p  =>
          let found := List.find? (fun x => x.2 == p ) lits
          match found with
          | .none => ([],[])
          | .some x => (x.1,[])
      | _ => ([],[])
  go ce T

#exit


partial def find_occurences (ce : CExpr) (T : CExprTrie) : List (List Nat × List oDirs) :=
    let rec go (done : List (List Nat × List oDirs)) : List (List oDirs × CExprTrie) → List (List Nat × List oDirs)
        | [] => done
        | nx :: more =>
            match nx.2.find? ce with -- replace find? with an embedding version ?
            | [] =>
                match nx.2 with
                | .dead => go done more
                | .br _ _ _ _ _ _ apf apa api laf laa lai alf ala ali lef lea lez lei projs =>
                    let todo := (if api.isEmpty then [] else [(.apf :: nx.1, apf),(.apa :: nx.1, apa)])
                                ++ (if lai.isEmpty then [] else [(.laf :: nx.1, laf),(.laa :: nx.1, laa)])
                                ++ (if ali.isEmpty then [] else [(.alf :: nx.1, alf),(.ala :: nx.1, ala)])
                                ++ (if lei.isEmpty then [] else [(.lef :: nx.1, lef),(.lea :: nx.1, lea),(.lez :: nx.1, lez)])
                                ++ projs.map (fun x => ((.pro x.2.1 x.2.2.1) :: nx.1, x.2.2.2))
                    go done (todo ++ more)
            | ind => go ((ind, nx.1) :: done) more
    go [] [([],T)]


partial def find_occurences_censored (ce : CExpr) (T : CExprTrie) : List (List Nat × List oDirs) :=
    let rec go (done : List (List Nat × List oDirs)) : List (List oDirs × CExprTrie) → List (List Nat × List oDirs)
        | [] => done
        | nx :: more =>
            match nx.2.find? ce with
            | [] =>
                match nx.2 with
                | .dead => go done more
                | .br _ _ _ _ _ _ apf apa api _ laa lai _ ala ali _ _ lez lei projs =>
                    let todo := (if api.isEmpty then [] else [(.apf :: nx.1, apf),(.apa :: nx.1, apa)])
                                ++ (if lai.isEmpty then [] else [(.laa :: nx.1, laa)])
                                ++ (if ali.isEmpty then [] else [(.ala :: nx.1, ala)])
                                ++ (if lei.isEmpty then [] else [(.lez :: nx.1, lez)])
                                ++ projs.map (fun x => ((.pro x.2.1 x.2.2.1) :: nx.1, x.2.2.2))
                    go done (todo ++ more)
            | ind => go ((ind, nx.1) :: done) more
    go [] [([],T)]

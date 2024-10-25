
import LeanGrow.F.Data.CExpr.API

#check 1


partial def CExpr.instanciate (subs within : CExpr) : CExpr :=
  let rec go : List (Nat × CExpr) → List CExpr
    | [] => []
    | (d, .lam n t b i) :: more =>
          let r := go ((d,t) :: (d+1,b) :: more)
          let (F,r2) := List.headD_tail r .failed
          let (A,r3) := List.headD_tail r2 .failed
          (.lam n F A i) :: r3
    | (d, .forallE n t b i) :: more =>
          let r := go ((d,t) :: (d+1,b) :: more)
          let (F,r2) := List.headD_tail r .failed
          let (A,r3) := List.headD_tail r2 .failed
          (.forallE n F A i) :: r3
    | (d, .letE n t v b i) :: more =>
          let r := go ((d,t) :: (d,v) :: (d+1,b) :: more)
          let (F,r2) := List.headD_tail r .failed
          let (A,r3) := List.headD_tail r2 .failed
          let (Z,r4) := List.headD_tail r3 .failed
          (.letE n F A Z i) :: r4
    | (d, .proj n i e) :: more =>
          let r := go ((d,e) :: more)
          let (E,r2) := List.headD_tail r .failed
          (.proj n i E) :: r2
    | (d, .app l r) :: more =>
          let r := go ((d,l) :: (d,r) :: more)
          let (F,r2) := List.headD_tail r .failed
          let (A,r3) := List.headD_tail r2 .failed
          (.app F A) :: r3
    | (d, .bvar i) :: more =>
          if d == i then subs :: go more else (.bvar i) :: go more
    | (_, ce) :: more => ce :: go more
  List.headD (go [(0,within)]) .failed


def CExpr.letFunAppArgs? (e : CExpr) : Option (List CExpr × Lean.Name × CExpr × CExpr × CExpr) :=
  let (h, as) := CExpr.getApp e
  if 4 ≤ as.length
  then
    match h with
    | .const `letFun _ =>
        let t := as.get! 0
        let v := as.get! 2
        let f := as.get! 3
        let rest := as.drop 4
        match f with
        | .lam n _ b _ => .some (rest, n, t, v, b)
        | _ => .some (rest, .anonymous, t, v, .app f (.bvar 0))
    | _ => .none
  else
    .none


def CExpr.beta (h : CExpr) : List CExpr → CExpr
      | [] => h
      | a :: as =>
            match h with
            | .lam _ _ b _ =>
                  let go := CExpr.instanciate a b
                  CExpr.beta go as
            | _ => CExpr.mkApp h (a :: as)

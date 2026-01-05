
/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/


import LeanGrow.Src.Data.PathIndex.API
import LeanGrow.Src.Utils.Lean.Expr.Basic

open Lean Meta

variable {IdxCollType : Type _}

namespace PaIn


inductive bCType (IdxCollType : Type _) where
| nil
| load (_ : ListProd Expr IdxCollType) (nx : bCType IdxCollType)
| app (turn : UInt8) (depth : Nat) (l r : PaIn IdxCollType) (tmp branch : ListProd Expr IdxCollType) (nx : bCType IdxCollType)
| lam (turn : UInt8) (depth : Nat) (l r : PaIn IdxCollType) (tmp branch  : ListProd Expr IdxCollType) (nx : bCType IdxCollType)
| all (turn : UInt8) (depth : Nat) (l r : PaIn IdxCollType) (tmp branch  : ListProd Expr IdxCollType) (nx : bCType IdxCollType)
| letE (turn : UInt8) (depth : Nat) (l r z : PaIn IdxCollType) (tmp1 tmp2 branch  : ListProd Expr IdxCollType) (nx : bCType IdxCollType)
| proj (fst? : Bool) (n : Name) (i : Nat) (is : IdxCollType) (depth : Nat) (_ : PaIn IdxCollType) (branch : ListProd Expr IdxCollType) (nx : bCType IdxCollType)
| proofs (fst? : Bool) (depth : Nat) (_ : PaIn IdxCollType) (branch : ListProd Expr IdxCollType) (nx : bCType IdxCollType)
deriving Inhabited


@[specialize]
def buildCoreDown (T : PaIn IdxCollType) (workas : List FVarId) (depth : Nat)
  (focus : IdxCollType → IdxCollType) (empty? : IdxCollType → Bool)
  (sofar : bCType IdxCollType) : bCType IdxCollType :=
  match T with
  | .dead => sofar
  | .br fvars mvars bvars sorts consts lits apf apa api laf laa lai alf ala ali lef lea lez lei projs _ proofs =>
      let fvars_res : ListProd Expr IdxCollType :=
        (fvars.fold .nil (fun na ind sf =>
          let na := (String.fromUTF8! na).toName
          let ind := focus ind
          if empty? ind
          then sf
          else
            .cons (.fvar ⟨na⟩) ind sf
            )
          )
      let mvars_res : ListProd Expr IdxCollType :=
        (mvars.fold fvars_res (fun na ind sf =>
          let na := (String.fromUTF8! na).toName
          let ind := focus ind
          if empty? ind
          then sf
          else
            .cons (.mvar ⟨na⟩) ind sf
            )
          )
      let bv_res : ListProd Expr IdxCollType :=
          bvars.foldl mvars_res (fun ind i sf =>
            let ind := focus ind
            if empty? ind
            then sf
            else
              if i ≥ depth
              then
                let w := workas[i - depth]!
                ListProd.cons (.fvar w) ind sf
              else
                ListProd.cons (.bvar i) ind sf
            )
      let sort_res : ListProd Expr IdxCollType :=
          sorts.foldl bv_res (fun ind i sf =>
            let ind := focus ind
            if empty? ind
            then sf
            else
              .cons (.sort i) ind sf
            )
      let lit_res : ListProd Expr IdxCollType :=
          lits.foldl sort_res (fun ind i sf =>
            let ind := focus ind
            if empty? ind
            then sf
            else
              .cons (.lit i) ind sf
            )
      let const_res : ListProd Expr IdxCollType :=
        (consts.fold lit_res (fun na L sf =>
          let na := (String.fromUTF8! na).toName
          L.foldl sf (fun ind ls sf =>
            let ind := focus ind
            if empty? ind
            then sf
            else
              .cons (.const na ls) ind sf
            )
          ))
      let sofar : bCType IdxCollType :=
          match const_res with
          | .nil => sofar
          | _ => .load const_res sofar
      let sofar : bCType IdxCollType := if empty? (focus api) then sofar else .app 0 depth apf apa .nil .nil sofar
      let sofar : bCType IdxCollType := if empty? (focus lai) then sofar else .lam 0 depth laf laa .nil .nil sofar
      let sofar : bCType IdxCollType := if empty? (focus ali) then sofar else .all 0 depth alf ala .nil .nil sofar
      let sofar : bCType IdxCollType := if empty? (focus lei) then sofar else .letE 0 depth lef lea lez .nil .nil .nil sofar
      let sofar : bCType IdxCollType := projs.fold sofar (fun na L sf =>
          let na := (String.fromUTF8! na).toName
          L.foldl sf (fun is (i,T) sf =>
            let is := focus is
            if empty? is
            then sf
            else
              .proj true na i is depth T .nil sf
            )
          )
      match proofs with
      | .dead => sofar
      | _ => .proofs true depth proofs .nil sofar




@[specialize]
partial def buildCoreUp (workas : List FVarId)
  (focus : IdxCollType → IdxCollType) (intersect : IdxCollType → IdxCollType → IdxCollType) (empty? : IdxCollType → Bool)
  (sofar : ListProd Expr IdxCollType) (todo : bCType IdxCollType) : ListProd Expr IdxCollType :=
  let buildCoreDownSpec (T : PaIn IdxCollType) (workas : List FVarId) (depth : Nat)
    (sofar : bCType IdxCollType) : bCType IdxCollType := buildCoreDown T workas depth focus empty? sofar
  match todo with
  | .nil => sofar
  | .load data nx => buildCoreUp workas focus intersect empty? (data.append sofar) nx
  | .app turn depth l r tmp branch nx =>
      if turn == 0
      then
        let NX := buildCoreDownSpec l workas depth <| .app 1 depth l r tmp sofar nx
        buildCoreUp workas focus intersect empty? .nil NX
      else if turn == 1
      then
        let NX := buildCoreDownSpec r workas depth <| .app 2 depth l r sofar branch nx
        buildCoreUp workas focus intersect empty? .nil NX
      else
        let sofar := (tmp.foldl branch (fun x y R =>
          (sofar.foldl R (fun X Y R =>
              let inter := intersect y Y
              if empty? inter
              then R
              else .cons (.app x X) inter R
            ))))
        buildCoreUp workas  focus intersect empty? sofar nx
  | .lam turn depth l r tmp branch nx =>
      if turn == 0
      then
        let NX := buildCoreDownSpec l workas depth <| .lam 1 depth l r tmp sofar nx
        buildCoreUp workas  focus intersect empty? .nil NX
      else if turn == 1
      then
        let NX := buildCoreDownSpec r workas (depth+1) <| .lam 2 depth l r sofar branch nx
        buildCoreUp workas  focus intersect empty? .nil NX
      else
        let sofar := (tmp.foldl branch (fun x y R =>
          (sofar.foldl R (fun X Y R =>
              let inter := intersect y Y
              if empty? inter
              then R
              else .cons (.lam `buildCore x X .default) inter R
            ))))
        buildCoreUp workas  focus intersect empty? sofar nx
  | .all turn depth l r tmp branch nx =>
      if turn == 0
      then
        let NX := buildCoreDownSpec l workas depth <| .all 1 depth l r tmp sofar nx
        buildCoreUp workas  focus intersect empty? .nil NX
      else if turn == 1
      then
        let NX := buildCoreDownSpec r workas (depth+1) <| .all 2 depth l r sofar branch nx
        buildCoreUp workas  focus intersect empty? .nil NX
      else
        let sofar := (tmp.foldl branch (fun x y R =>
          (sofar.foldl R (fun X Y R =>
              let inter := intersect y Y
              if empty? inter
              then R
              else .cons (.forallE `buildCore x X .default) inter R
            ))))
        buildCoreUp workas  focus intersect empty? sofar nx
  | .letE turn depth l r z tmp1 tmp2 branch nx =>
      if turn == 0
      then
        let NX := buildCoreDownSpec l workas depth <| .letE 1 depth l r z tmp1 tmp2 sofar nx
        buildCoreUp workas  focus intersect empty? .nil NX
      else if turn == 1
      then
        let NX := buildCoreDownSpec r workas depth <| .letE 2 depth l r z sofar tmp2 branch nx
        buildCoreUp workas  focus intersect empty? .nil NX
      else if turn == 2
      then
        let NX := buildCoreDownSpec z workas (depth + 1) <| .letE 3 depth l r z tmp1 sofar branch nx
        buildCoreUp workas  focus intersect empty? .nil NX
      else
        let sofar := (tmp1.foldl branch (fun x y R =>
          (tmp2.foldl R (fun X Y R =>
            (sofar.foldl R (fun X' Y' R =>
              let inter := intersect y <| intersect Y Y'
              if empty? inter
              then R
              else .cons (.letE `buildCore x X X' false) inter R
          ))))))
        buildCoreUp workas  focus intersect empty? sofar nx
  | .proj fst name idx is depth T branch nx =>
      if fst
      then
        let NX := buildCoreDownSpec T workas depth <| .proj false name idx is depth T sofar nx
        buildCoreUp workas  focus intersect empty? .nil NX
      else
        let res := sofar.foldl branch (fun e is R => .cons (.proj name idx e) is R)
        buildCoreUp workas  focus intersect empty? res nx
  | .proofs fst depth T branch nx =>
      if fst
      then
        let NX := buildCoreDownSpec T workas depth <| .proofs false depth T sofar nx
        buildCoreUp workas  focus intersect empty? .nil NX
      else
        let res := sofar.append branch
        buildCoreUp workas  focus intersect empty? res nx


@[specialize, inline]
partial def buildCore (T : PaIn IdxCollType) (workas : List FVarId) (depth : Nat)
  (focus : IdxCollType → IdxCollType) (intersect : IdxCollType → IdxCollType → IdxCollType) (empty? : IdxCollType → Bool)
  : ListProd Expr IdxCollType :=
  buildCoreUp workas focus intersect empty? .nil (buildCoreDown T workas depth focus empty? .nil)


@[specialize, inline]
def buildAll (T : PaIn IdxCollType) (workas : List FVarId) (depth : Nat)
  (intersect : IdxCollType → IdxCollType → IdxCollType) (empty? : IdxCollType → Bool)
  : ListProd Expr IdxCollType :=
  buildCore T workas depth id intersect empty?

@[specialize, inline]
def buildAllTop (T : PaIn IdxCollType)
  (intersect : IdxCollType → IdxCollType → IdxCollType) (empty? : IdxCollType → Bool)
  : ListProd Expr IdxCollType :=
  buildCore T [] 0 id intersect empty?



-- # Specialize

def buildS (T : PaIn UInt32Array) (workas : List FVarId) (depth : Nat)
  (among : UInt32Array) : ListProd Expr UInt32Array :=
    buildCore T workas depth (fun x => UInt32Array.inter among x) UInt32Array.inter UInt32Array.isEmpty

def buildAllS (T : PaIn UInt32Array) (workas : List FVarId) (depth : Nat) :=
  buildAll T workas depth UInt32Array.inter UInt32Array.isEmpty

def buildAllTopS (T : PaIn UInt32Array) :=
  buildAllTop T UInt32Array.inter UInt32Array.isEmpty



-- # Printing

@[inline]
def ppPainHelp [Repr IdxCollType] (l1 : LocalContext) (l2 : LocalInstances) (built : ListProd Expr IdxCollType) : MetaM String := do
  let pretty ← built.toListOfProd.mapM (fun (e,is) => return s!"({← PpExpr e l1 l2} ::: {repr is})")
  return String.intercalate " ;;; " pretty

@[inline]
def pp [Repr IdxCollType] (l1 : LocalContext) (l2 : LocalInstances) (T : PaIn IdxCollType) (workas : List FVarId) (depth : Nat)
  (intersect : IdxCollType → IdxCollType → IdxCollType) (empty? : IdxCollType → Bool)
  : MetaM String := do
  let built := buildCore T workas depth id intersect empty?
  ppPainHelp l1 l2 built



def ppS (l1 : LocalContext) (l2 : LocalInstances) (T : PaIn UInt32Array) (workas : List FVarId) (depth : Nat)
  : MetaM String :=
    pp l1 l2 T workas depth (UInt32Array.inter) UInt32Array.isEmpty





-- # Without loose bvars




@[specialize]
def buildNoLoBvCoreDown (T : PaIn IdxCollType) (depth : Nat)
  (focus : IdxCollType → IdxCollType) (empty? : IdxCollType → Bool)
  (sofar : bCType IdxCollType) : bCType IdxCollType :=
  match T with
  | .dead => sofar
  | .br fvars mvars bvars sorts consts lits apf apa api laf laa lai alf ala ali lef lea lez lei projs _ proofs =>
      let fvars_res : ListProd Expr IdxCollType :=
        (fvars.fold .nil (fun na ind sf =>
          let na := (String.fromUTF8! na).toName
          let ind := focus ind
          if empty? ind
          then sf
          else
            .cons (.fvar ⟨na⟩) ind sf
            )
          )
      let mvars_res : ListProd Expr IdxCollType :=
        (mvars.fold fvars_res (fun na ind sf =>
          let na := (String.fromUTF8! na).toName
          let ind := focus ind
          if empty? ind
          then sf
          else
            .cons (.mvar ⟨na⟩) ind sf
            )
          )
      let bv_res : ListProd Expr IdxCollType :=
          bvars.foldl mvars_res (fun ind i sf =>
            let ind := focus ind
            if empty? ind
              then sf
              else
                if i ≥ depth
                then
                  sf
                else
                  ListProd.cons (.bvar i) ind sf
            )
      let sort_res : ListProd Expr IdxCollType :=
          sorts.foldl bv_res (fun ind i sf =>
            let ind := focus ind
            if empty? ind
            then sf
            else
              .cons (.sort i) ind sf
            )
      let lit_res : ListProd Expr IdxCollType :=
          lits.foldl sort_res (fun ind i sf =>
            let ind := focus ind
            if empty? ind
            then sf
            else
              .cons (.lit i) ind sf
            )
      let const_res : ListProd Expr IdxCollType :=
        (consts.fold lit_res (fun na L sf =>
          let na := (String.fromUTF8! na).toName
          L.foldl sf (fun ind ls sf =>
            let ind := focus ind
            if empty? ind
            then sf
            else
              .cons (.const na ls) ind sf
            )
          ))
      let sofar : bCType IdxCollType :=
          match const_res with
          | .nil => sofar
          | _ => .load const_res sofar
      let sofar : bCType IdxCollType := if empty? (focus api) then sofar else .app 0 depth apf apa .nil .nil sofar
      let sofar : bCType IdxCollType := if empty? (focus lai) then sofar else .lam 0 depth laf laa .nil .nil sofar
      let sofar : bCType IdxCollType := if empty? (focus ali) then sofar else .all 0 depth alf ala .nil .nil sofar
      let sofar : bCType IdxCollType := if empty? (focus lei) then sofar else .letE 0 depth lef lea lez .nil .nil .nil sofar
      let sofar : bCType IdxCollType := projs.fold sofar (fun na L sf =>
          let na := (String.fromUTF8! na).toName
          L.foldl sf (fun is (i,T) sf =>
            let is := focus is
            if empty? is
            then sf
            else
              .proj true na i is depth T .nil sf
            )
          )
      match proofs with
      | .dead => sofar
      | _ => .proofs true depth proofs .nil sofar


@[specialize]
partial def buildNoLoBvCoreUp
  (focus : IdxCollType → IdxCollType) (intersect : IdxCollType → IdxCollType → IdxCollType) (empty? : IdxCollType → Bool)
  (sofar : ListProd Expr IdxCollType) (todo : bCType IdxCollType) : ListProd Expr IdxCollType :=
  let buildNoLoBvCoreDownSpec (T : PaIn IdxCollType) (depth : Nat)
    (sofar : bCType IdxCollType) : bCType IdxCollType := buildNoLoBvCoreDown T depth focus empty? sofar
  match todo with
  | .nil => sofar
  | .load data nx => buildNoLoBvCoreUp focus intersect empty? (data.append sofar) nx
  | .app turn depth l r tmp branch nx =>
      if turn == 0
      then
        let NX := buildNoLoBvCoreDownSpec l depth <| .app 1 depth l r tmp sofar nx
        buildNoLoBvCoreUp focus intersect empty? .nil NX
      else if turn == 1
      then
        let NX := buildNoLoBvCoreDownSpec r depth <| .app 2 depth l r sofar branch nx
        buildNoLoBvCoreUp focus intersect empty? .nil NX
      else
        let sofar := (tmp.foldl branch (fun x y R =>
          (sofar.foldl R (fun X Y R =>
              let inter := intersect y Y
              if empty? inter
              then R
              else .cons (.app x X) inter R
            ))))
        buildNoLoBvCoreUp  focus intersect empty? sofar nx
  | .lam turn depth l r tmp branch nx =>
      if turn == 0
      then
        let NX := buildNoLoBvCoreDownSpec l depth <| .lam 1 depth l r tmp sofar nx
        buildNoLoBvCoreUp  focus intersect empty? .nil NX
      else if turn == 1
      then
        let NX := buildNoLoBvCoreDownSpec r (depth+1) <| .lam 2 depth l r sofar branch nx
        buildNoLoBvCoreUp  focus intersect empty? .nil NX
      else
        let sofar := (tmp.foldl branch (fun x y R =>
          (sofar.foldl R (fun X Y R =>
              let inter := intersect y Y
              if empty? inter
              then R
              else .cons (.lam `buildCore x X .default) inter R
            ))))
        buildNoLoBvCoreUp  focus intersect empty? sofar nx
  | .all turn depth l r tmp branch nx =>
      if turn == 0
      then
        let NX := buildNoLoBvCoreDownSpec l depth <| .all 1 depth l r tmp sofar nx
        buildNoLoBvCoreUp  focus intersect empty? .nil NX
      else if turn == 1
      then
        let NX := buildNoLoBvCoreDownSpec r (depth+1) <| .all 2 depth l r sofar branch nx
        buildNoLoBvCoreUp  focus intersect empty? .nil NX
      else
        let sofar := (tmp.foldl branch (fun x y R =>
          (sofar.foldl R (fun X Y R =>
              let inter := intersect y Y
              if empty? inter
              then R
              else .cons (.forallE `buildCore x X .default) inter R
            ))))
        buildNoLoBvCoreUp  focus intersect empty? sofar nx
  | .letE turn depth l r z tmp1 tmp2 branch nx =>
      if turn == 0
      then
        let NX := buildNoLoBvCoreDownSpec l depth <| .letE 1 depth l r z tmp1 tmp2 sofar nx
        buildNoLoBvCoreUp  focus intersect empty? .nil NX
      else if turn == 1
      then
        let NX := buildNoLoBvCoreDownSpec r depth <| .letE 2 depth l r z sofar tmp2 branch nx
        buildNoLoBvCoreUp  focus intersect empty? .nil NX
      else if turn == 2
      then
        let NX := buildNoLoBvCoreDownSpec z (depth + 1) <| .letE 3 depth l r z tmp1 sofar branch nx
        buildNoLoBvCoreUp  focus intersect empty? .nil NX
      else
        let sofar := (tmp1.foldl branch (fun x y R =>
          (tmp2.foldl R (fun X Y R =>
            (sofar.foldl R (fun X' Y' R =>
              let inter := intersect y <| intersect Y Y'
              if empty? inter
              then R
              else .cons (.letE `buildCore x X X' false) inter R
          ))))))
        buildNoLoBvCoreUp  focus intersect empty? sofar nx
  | .proj fst name idx is depth T branch nx =>
      if fst
      then
        let NX := buildNoLoBvCoreDownSpec T depth <| .proj false name idx is depth T sofar nx
        buildNoLoBvCoreUp  focus intersect empty? .nil NX
      else
        let res := sofar.foldl branch (fun e is R => .cons (.proj name idx e) is R)
        buildNoLoBvCoreUp  focus intersect empty? res nx
  | .proofs fst depth T branch nx =>
      if fst
      then
        let NX := buildNoLoBvCoreDownSpec T depth <| .proofs false depth T sofar nx
        buildNoLoBvCoreUp  focus intersect empty? .nil NX
      else
        let res := sofar.append branch
        buildNoLoBvCoreUp  focus intersect empty? res nx


@[specialize, inline]
partial def buildNoLoBvCore (T : PaIn IdxCollType) (depth : Nat)
  (focus : IdxCollType → IdxCollType) (intersect : IdxCollType → IdxCollType → IdxCollType) (empty? : IdxCollType → Bool)
  : ListProd Expr IdxCollType :=
  buildNoLoBvCoreUp focus intersect empty? .nil (buildNoLoBvCoreDown T depth focus empty? .nil)



@[specialize]
def buildMultiCoreDown (T : PaIn IdxCollType) (workas : ListProd IdxCollType (List FVarId)) (depth : Nat)
  (intersect : IdxCollType → IdxCollType → IdxCollType) (focus : IdxCollType → IdxCollType) (empty? : IdxCollType → Bool)
  (sofar : bCType IdxCollType) : bCType IdxCollType :=
  match T with
  | .dead => sofar
  | .br fvars mvars bvars sorts consts lits apf apa api laf laa lai alf ala ali lef lea lez lei projs _ proofs =>
      let fvars_res : ListProd Expr IdxCollType :=
        (fvars.fold .nil (fun na ind sf =>
          let na := (String.fromUTF8! na).toName
          let ind := focus ind
          if empty? ind
          then sf
          else
            .cons (.fvar ⟨na⟩) ind sf
            )
          )
      let mvars_res : ListProd Expr IdxCollType :=
        (mvars.fold fvars_res (fun na ind sf =>
          let na := (String.fromUTF8! na).toName
          let ind := focus ind
          if empty? ind
          then sf
          else
            .cons (.mvar ⟨na⟩) ind sf
            )
          )
      let bv_res : ListProd Expr IdxCollType :=
          bvars.foldl mvars_res (fun ind i sf =>
            let ind := focus ind
            if empty? ind
            then sf
            else
              if i ≥ depth
              then
                workas.foldl sf (fun winds workas sf =>
                  let I := intersect ind winds
                  if empty? I
                  then sf
                  else
                    let w := workas[i - depth]!
                    ListProd.cons (.fvar w) I sf)
              else
                ListProd.cons (.bvar i) ind sf
            )
      let sort_res : ListProd Expr IdxCollType :=
          sorts.foldl bv_res (fun ind i sf =>
            let ind := focus ind
            if empty? ind
            then sf
            else
              .cons (.sort i) ind sf
            )
      let lit_res : ListProd Expr IdxCollType :=
          lits.foldl sort_res (fun ind i sf =>
            let ind := focus ind
            if empty? ind
            then sf
            else
              .cons (.lit i) ind sf
            )
      let const_res : ListProd Expr IdxCollType :=
        (consts.fold lit_res (fun na L sf =>
          let na := (String.fromUTF8! na).toName
          L.foldl sf (fun ind ls sf =>
            let ind := focus ind
            if empty? ind
            then sf
            else
              .cons (.const na ls) ind sf
            )
          ))
      let sofar : bCType IdxCollType :=
          match const_res with
          | .nil => sofar
          | _ => .load const_res sofar
      let sofar : bCType IdxCollType := if empty? (focus api) then sofar else .app 0 depth apf apa .nil .nil sofar
      let sofar : bCType IdxCollType := if empty? (focus lai) then sofar else .lam 0 depth laf laa .nil .nil sofar
      let sofar : bCType IdxCollType := if empty? (focus ali) then sofar else .all 0 depth alf ala .nil .nil sofar
      let sofar : bCType IdxCollType := if empty? (focus lei) then sofar else .letE 0 depth lef lea lez .nil .nil .nil sofar
      let sofar : bCType IdxCollType := projs.fold sofar (fun na L sf =>
          let na := (String.fromUTF8! na).toName
          L.foldl sf (fun is (i,T) sf =>
            let is := focus is
            if empty? is
            then sf
            else
              .proj true na i is depth T .nil sf
            )
          )
      match proofs with
      | .dead => sofar
      | _ => .proofs true depth proofs .nil sofar


@[specialize]
partial def buildMultiCoreUp (workas : ListProd IdxCollType (List FVarId))
  (focus : IdxCollType → IdxCollType) (intersect : IdxCollType → IdxCollType → IdxCollType) (empty? : IdxCollType → Bool)
  (sofar : ListProd Expr IdxCollType) (todo : bCType IdxCollType) : ListProd Expr IdxCollType :=
  let buildMultiCoreDownSpec (T : PaIn IdxCollType) (workas : ListProd IdxCollType (List FVarId)) (depth : Nat)
    (sofar : bCType IdxCollType) : bCType IdxCollType := buildMultiCoreDown T workas depth intersect focus empty? sofar
  match todo with
  | .nil => sofar
  | .load data nx => buildMultiCoreUp workas focus intersect empty? (data.append sofar) nx
  | .app turn depth l r tmp branch nx =>
      if turn == 0
      then
        let NX := buildMultiCoreDownSpec l workas depth <| .app 1 depth l r tmp sofar nx
        buildMultiCoreUp workas focus intersect empty? .nil NX
      else if turn == 1
      then
        let NX := buildMultiCoreDownSpec r workas depth <| .app 2 depth l r sofar branch nx
        buildMultiCoreUp workas focus intersect empty? .nil NX
      else
        let sofar := (tmp.foldl branch (fun x y R =>
          (sofar.foldl R (fun X Y R =>
              let inter := intersect y Y
              if empty? inter
              then R
              else .cons (.app x X) inter R
            ))))
        buildMultiCoreUp workas  focus intersect empty? sofar nx
  | .lam turn depth l r tmp branch nx =>
      if turn == 0
      then
        let NX := buildMultiCoreDownSpec l workas depth <| .lam 1 depth l r tmp sofar nx
        buildMultiCoreUp workas  focus intersect empty? .nil NX
      else if turn == 1
      then
        let NX := buildMultiCoreDownSpec r workas (depth+1) <| .lam 2 depth l r sofar branch nx
        buildMultiCoreUp workas  focus intersect empty? .nil NX
      else
        let sofar := (tmp.foldl branch (fun x y R =>
          (sofar.foldl R (fun X Y R =>
              let inter := intersect y Y
              if empty? inter
              then R
              else .cons (.lam `buildCore x X .default) inter R
            ))))
        buildMultiCoreUp workas  focus intersect empty? sofar nx
  | .all turn depth l r tmp branch nx =>
      if turn == 0
      then
        let NX := buildMultiCoreDownSpec l workas depth <| .all 1 depth l r tmp sofar nx
        buildMultiCoreUp workas  focus intersect empty? .nil NX
      else if turn == 1
      then
        let NX := buildMultiCoreDownSpec r workas (depth+1) <| .all 2 depth l r sofar branch nx
        buildMultiCoreUp workas  focus intersect empty? .nil NX
      else
        let sofar := (tmp.foldl branch (fun x y R =>
          (sofar.foldl R (fun X Y R =>
              let inter := intersect y Y
              if empty? inter
              then R
              else .cons (.forallE `buildCore x X .default) inter R
            ))))
        buildMultiCoreUp workas  focus intersect empty? sofar nx
  | .letE turn depth l r z tmp1 tmp2 branch nx =>
      if turn == 0
      then
        let NX := buildMultiCoreDownSpec l workas depth <| .letE 1 depth l r z tmp1 tmp2 sofar nx
        buildMultiCoreUp workas  focus intersect empty? .nil NX
      else if turn == 1
      then
        let NX := buildMultiCoreDownSpec r workas depth <| .letE 2 depth l r z sofar tmp2 branch nx
        buildMultiCoreUp workas  focus intersect empty? .nil NX
      else if turn == 2
      then
        let NX := buildMultiCoreDownSpec z workas (depth + 1) <| .letE 3 depth l r z tmp1 sofar branch nx
        buildMultiCoreUp workas  focus intersect empty? .nil NX
      else
        let sofar := (tmp1.foldl branch (fun x y R =>
          (tmp2.foldl R (fun X Y R =>
            (sofar.foldl R (fun X' Y' R =>
              let inter := intersect y <| intersect Y Y'
              if empty? inter
              then R
              else .cons (.letE `buildCore x X X' false) inter R
          ))))))
        buildMultiCoreUp workas  focus intersect empty? sofar nx
  | .proj fst name idx is depth T branch nx =>
      if fst
      then
        let NX := buildMultiCoreDownSpec T workas depth <| .proj false name idx is depth T sofar nx
        buildMultiCoreUp workas  focus intersect empty? .nil NX
      else
        let res := sofar.foldl branch (fun e is R => .cons (.proj name idx e) is R)
        buildMultiCoreUp workas  focus intersect empty? res nx
  | .proofs fst depth T branch nx =>
      if fst
      then
        let NX := buildMultiCoreDownSpec T workas depth <| .proofs false depth T sofar nx
        buildMultiCoreUp workas  focus intersect empty? .nil NX
      else
        let res := sofar.append branch
        buildMultiCoreUp workas  focus intersect empty? res nx


@[specialize, inline]
partial def buildMultiCore (T : PaIn IdxCollType) (workas : ListProd IdxCollType (List FVarId)) (depth : Nat)
  (focus : IdxCollType → IdxCollType) (intersect : IdxCollType → IdxCollType → IdxCollType) (empty? : IdxCollType → Bool)
  : ListProd Expr IdxCollType :=
  buildMultiCoreUp workas focus intersect empty? .nil (buildMultiCoreDown T workas depth intersect focus empty? .nil)


-- # Indices Only

inductive bIType (IdxCollType : Type _) where
| nil
| load (_ : List IdxCollType) (nx : bIType IdxCollType)
| app (turn : UInt8) (depth : Nat) (l r : PaIn IdxCollType) (tmp branch : List IdxCollType) (nx : bIType IdxCollType)
| lam (turn : UInt8) (depth : Nat) (l r : PaIn IdxCollType) (tmp branch  : List IdxCollType) (nx : bIType IdxCollType)
| all (turn : UInt8) (depth : Nat) (l r : PaIn IdxCollType) (tmp branch  : List IdxCollType) (nx : bIType IdxCollType)
| letE (turn : UInt8) (depth : Nat) (l r z : PaIn IdxCollType) (tmp1 tmp2 branch  : List IdxCollType) (nx : bIType IdxCollType)
| proj (fst? : Bool) (n : Name) (i : Nat) (is : IdxCollType) (depth : Nat) (_ : PaIn IdxCollType) (branch : List IdxCollType) (nx : bIType IdxCollType)
| proofs (fst? : Bool) (depth : Nat) (_ : PaIn IdxCollType) (branch : List IdxCollType) (nx : bIType IdxCollType)
deriving Inhabited


@[specialize]
def buildIndicesDown (T : PaIn IdxCollType) (depth : Nat)
  (focus : IdxCollType → IdxCollType) (empty? : IdxCollType → Bool)
  (sofar : bIType IdxCollType) : bIType IdxCollType :=
  match T with
  | .dead => sofar
  | .br fvars mvars bvars sorts consts lits apf apa api laf laa lai alf ala ali lef lea lez lei projs _ proofs =>
      let fvars_res : List IdxCollType :=
        (fvars.fold .nil (fun _ ind sf =>
          let ind := focus ind
          if empty? ind
          then sf
          else
            .cons ind sf
            )
          )
      let mvars_res : List IdxCollType :=
        (mvars.fold fvars_res (fun _ ind sf =>
          let ind := focus ind
          if empty? ind
          then sf
          else
            .cons ind sf
            )
          )
      let bv_res : List IdxCollType :=
          bvars.foldl mvars_res (fun ind i sf =>
            let ind := focus ind
            if empty? ind
            then sf
            else
              if i ≥ depth
              then
                .cons ind sf
              else
                .cons ind sf
            )
      let sort_res : List IdxCollType :=
          sorts.foldl bv_res (fun ind _ sf =>
            let ind := focus ind
            if empty? ind
            then sf
            else
              .cons ind sf
            )
      let lit_res : List IdxCollType :=
          lits.foldl sort_res (fun ind _ sf =>
            let ind := focus ind
            if empty? ind
            then sf
            else
              .cons ind sf
            )
      let const_res : List IdxCollType :=
        (consts.fold lit_res (fun _ L sf =>
          L.foldl sf (fun ind _ sf =>
            let ind := focus ind
            if empty? ind
            then sf
            else
              .cons ind sf
            )
          ))
      let sofar : bIType IdxCollType :=
          match const_res with
          | .nil => sofar
          | _ => .load const_res sofar
      let sofar : bIType IdxCollType := if empty? (focus api) then sofar else .app 0 depth apf apa .nil .nil sofar
      let sofar : bIType IdxCollType := if empty? (focus lai) then sofar else .lam 0 depth laf laa .nil .nil sofar
      let sofar : bIType IdxCollType := if empty? (focus ali) then sofar else .all 0 depth alf ala .nil .nil sofar
      let sofar : bIType IdxCollType := if empty? (focus lei) then sofar else .letE 0 depth lef lea lez .nil .nil .nil sofar
      let sofar : bIType IdxCollType := projs.fold sofar (fun na L sf =>
          let na := (String.fromUTF8! na).toName
          L.foldl sf (fun is (i,T) sf =>
            let is := focus is
            if empty? is
            then sf
            else
              .proj true na i is depth T .nil sf
            )
          )
      match proofs with
      | .dead => sofar
      | _ => .proofs true depth proofs .nil sofar


@[specialize]
partial def buildIndicesUp
  (focus : IdxCollType → IdxCollType) (intersect : IdxCollType → IdxCollType → IdxCollType) (empty? : IdxCollType → Bool)
  (sofar : List IdxCollType) (todo : bIType IdxCollType) : List IdxCollType :=
  let buildIndicesDownSpec (T : PaIn IdxCollType) (depth : Nat)
    (sofar : bIType IdxCollType) : bIType IdxCollType := buildIndicesDown T depth focus empty? sofar
  match todo with
  | .nil => sofar
  | .load data nx => buildIndicesUp focus intersect empty? (data.append sofar) nx
  | .app turn depth l r tmp branch nx =>
      if turn == 0
      then
        let NX := buildIndicesDownSpec l depth <| .app 1 depth l r tmp sofar nx
        buildIndicesUp focus intersect empty? .nil NX
      else if turn == 1
      then
        let NX := buildIndicesDownSpec r depth <| .app 2 depth l r sofar branch nx
        buildIndicesUp focus intersect empty? .nil NX
      else
        let sofar := (tmp.foldl (fun R y =>
          (sofar.foldl (fun R Y =>
              let inter := intersect y Y
              if empty? inter
              then R
              else .cons inter R
            ) R )) branch)
        buildIndicesUp  focus intersect empty? sofar nx
  | .lam turn depth l r tmp branch nx =>
      if turn == 0
      then
        let NX := buildIndicesDownSpec l depth <| .lam 1 depth l r tmp sofar nx
        buildIndicesUp  focus intersect empty? .nil NX
      else if turn == 1
      then
        let NX := buildIndicesDownSpec r (depth+1) <| .lam 2 depth l r sofar branch nx
        buildIndicesUp  focus intersect empty? .nil NX
      else
        let sofar := (tmp.foldl  (fun R y =>
          (sofar.foldl (fun R Y =>
              let inter := intersect y Y
              if empty? inter
              then R
              else .cons inter R
            ) R)) branch)
        buildIndicesUp  focus intersect empty? sofar nx
  | .all turn depth l r tmp branch nx =>
      if turn == 0
      then
        let NX := buildIndicesDownSpec l depth <| .all 1 depth l r tmp sofar nx
        buildIndicesUp  focus intersect empty? .nil NX
      else if turn == 1
      then
        let NX := buildIndicesDownSpec r (depth+1) <| .all 2 depth l r sofar branch nx
        buildIndicesUp  focus intersect empty? .nil NX
      else
        let sofar := (tmp.foldl (fun R y =>
          (sofar.foldl (fun R Y =>
              let inter := intersect y Y
              if empty? inter
              then R
              else .cons inter R
            ) R)) branch)
        buildIndicesUp  focus intersect empty? sofar nx
  | .letE turn depth l r z tmp1 tmp2 branch nx =>
      if turn == 0
      then
        let NX := buildIndicesDownSpec l depth <| .letE 1 depth l r z tmp1 tmp2 sofar nx
        buildIndicesUp  focus intersect empty? .nil NX
      else if turn == 1
      then
        let NX := buildIndicesDownSpec r depth <| .letE 2 depth l r z sofar tmp2 branch nx
        buildIndicesUp  focus intersect empty? .nil NX
      else if turn == 2
      then
        let NX := buildIndicesDownSpec z (depth + 1) <| .letE 3 depth l r z tmp1 sofar branch nx
        buildIndicesUp  focus intersect empty? .nil NX
      else
        let sofar := (tmp1.foldl (fun R y =>
          (tmp2.foldl (fun R Y =>
            (sofar.foldl (fun R Y' =>
              let inter := intersect y <| intersect Y Y'
              if empty? inter
              then R
              else .cons inter R
          ) R)) R)) branch)
        buildIndicesUp  focus intersect empty? sofar nx
  | .proj fst name idx is depth T branch nx =>
      if fst
      then
        let NX := buildIndicesDownSpec T depth <| .proj false name idx is depth T sofar nx
        buildIndicesUp  focus intersect empty? .nil NX
      else
        let res := sofar.foldl (fun R is => .cons is R) branch
        buildIndicesUp  focus intersect empty? res nx
  | .proofs fst depth T branch nx =>
      if fst
      then
        let NX := buildIndicesDownSpec T depth <| .proofs false depth T sofar nx
        buildIndicesUp  focus intersect empty? .nil NX
      else
        let res := sofar.append branch
        buildIndicesUp focus intersect empty? res nx


@[specialize, inline]
partial def buildIndices (T : PaIn IdxCollType) (depth : Nat)
  (focus : IdxCollType → IdxCollType) (intersect : IdxCollType → IdxCollType → IdxCollType) (empty? : IdxCollType → Bool)
  : List IdxCollType :=
  buildIndicesUp focus intersect empty? .nil (buildIndicesDown T depth focus empty? .nil)

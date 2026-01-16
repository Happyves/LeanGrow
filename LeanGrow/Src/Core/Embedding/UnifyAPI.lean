
/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/


import LeanGrow.Src.Data.PathIndexG.Query


open Lean Meta

variable {IdxCollType : Type _}

namespace PaInG


-- #exit
@[specialize, inline]
def uniUpdateWrtLevel
  (empty? : IdxCollType → Bool) (intersect : IdxCollType → IdxCollType → IdxCollType)
  (asInds : IdxCollType) (mv : LMVarId) (lv : Level)
  (sofar : ListProd3 IdxCollType (ListProd3 Nat Nat Expr) (ListProd3 Nat Nat Level))
  : MetaM <| ListProd3 IdxCollType (ListProd3 Nat Nat Expr) (ListProd3 Nat Nat Level) :=
    sofar.foldlM .nil (fun is tn ln R => do
      let I := intersect asInds is
      if empty? I
      then return .cons is tn ln R
      else
          match mv.name with
          | .num (.num _ backIdx) pos =>
              match ln.find? (fun x y _ => x == backIdx && y == pos) with
              | .none =>
                  return .cons I tn (.cons backIdx pos lv ln) R
              | .some _ _ al =>
                  if ← (do let res ← isLevelDefEq al lv ; clearMvarAssignments ; return res)
                  then
                    return .cons is tn ln R
                  else
                    return R
          | _ => panic s!"[uniUpdateWrtLevels] assignements from defeq contained level mvar not in format: {repr mv}"
      )


@[specialize, inline]
def uniUpdateWrtLevels [Repr IdxCollType]
  (empty? : IdxCollType → Bool) (intersect difference : IdxCollType → IdxCollType → IdxCollType)
  (asInds : IdxCollType) (As : PersistentHashMap LMVarId Level)
  (sofar : ListProd3 IdxCollType (ListProd3 Nat Nat Expr) (ListProd3 Nat Nat Level))
  : MetaM <| ListProd3 IdxCollType (ListProd3 Nat Nat Expr) (ListProd3 Nat Nat Level) :=
    -- trace set Tracing.Flags.none in
    sofar.foldlM .nil (fun is tn ln S => do
      mtracing
      let I := intersect asInds is
      if empty? I
      then
        mtrace on .zero with s!"[uniUpdateWrtLevels] empty inter, leve as is"
        return ListProd3.cons is tn ln S
      else
        mtrace on .zero with s!"[uniUpdateWrtLevels] intersection {repr I}"
        if As.isEmpty
        then return ListProd3.cons is tn ln S
        else
          let D := difference is asInds
          mtrace on .zero with s!"[uniUpdateWrtLevels] found diff D {repr D}"
          -- let pre (R : ListProd3 IdxCollType (ListProd3 Nat Nat Expr) (ListProd3 Nat Nat Level)) :=
          --   if empty? D then R else .cons D tn ln R
          let mut ntn := tn
          let mut nln := ln
          let mut broke? := false
          for (mv, lv) in As do
            mtrace on .zero with s!"[uniUpdateWrtLevels] looking at assignement {repr mv} with val {lv}"
            match mv.name with
            | .num (.num _ backIdx) pos =>
                match ln.find? (fun x y _ => x == backIdx && y == pos) with
                | .none =>
                    nln := (.cons backIdx pos lv nln)
                | .some _ _ al => do
                    if ← (do let res ← isLevelDefEq al lv ; clearMvarAssignments ; return res)
                    then
                      continue
                    else
                      broke? := true
                      break
            | _ => panic s!"[uniUpdateWrtLevels] assignements from defeq contained level mvar not in format: {repr mv}"
          if broke?
          then return S --pre S
          else return (.cons I ntn nln S) --pre (.cons I ntn nln S)
      )

@[specialize, inline]
def uniUpdateWrtMvar
  (empty? : IdxCollType → Bool) (intersect : IdxCollType → IdxCollType → IdxCollType)
  (l1 : LocalContext) (l2 : LocalInstances)
  (asInds : IdxCollType) (mv : MVarId) (lv : Expr)
  (sofar : ListProd3 IdxCollType (ListProd3 Nat Nat Expr) (ListProd3 Nat Nat Level))
  : MetaM (ListProd3 IdxCollType (ListProd3 Nat Nat Expr) (ListProd3 Nat Nat Level)) :=
  withReader (fun ctx => {ctx with lctx := l1, localInstances := l2}) do
    sofar.foldlM .nil (fun is tn ln R =>
      let I := intersect asInds is
      if empty? I
      then return .cons is tn ln R
      else
        match mv.name with
        | .num (.num _ backIdx) pos =>
            match tn.find? (fun x y _ => x == backIdx && y == pos) with
            | .none =>
                return .cons I (.cons backIdx pos lv tn) ln R
            | .some _ _ al => do
                if (← defEqWiMv al lv l1 l2).isSome
                then
                  return .cons is tn ln R
                else
                  return R
        | _ => panic s!"[uniUpdateWrtMvar] assignements from defeq contained level mvar not in format: {repr mv}"
      )

@[specialize, inline]
def uniUpdateWrtMvars [Repr IdxCollType]
  (empty? : IdxCollType → Bool) (intersect difference : IdxCollType → IdxCollType → IdxCollType)
  (l1 : LocalContext) (l2 : LocalInstances)
  (asInds : IdxCollType) (As : PersistentHashMap MVarId Expr)
  (sofar : ListProd3 IdxCollType (ListProd3 Nat Nat Expr) (ListProd3 Nat Nat Level))
  : MetaM (ListProd3 IdxCollType (ListProd3 Nat Nat Expr) (ListProd3 Nat Nat Level)) :=
    -- trace set Tracing.Flags.none in do
  withReader (fun ctx => {ctx with lctx := l1, localInstances := l2}) do
    mtracing
    mtrace on .zero with s!"[uniUpdateWrtMvars] call on asInds {repr asInds}"
    sofar.foldlM .nil (fun is tn ln S => do
      let I := intersect asInds is
      if empty? I
      then
        mtrace on .zero with s!"[uniUpdateWrtMvars] is had empty intersection , leaving ; is {repr is}"
        return .cons is tn ln S
      else
        mtrace on .zero with s!"[uniUpdateWrtMvars] found intersection I {repr I}"
        if As.isEmpty
        then return ListProd3.cons is tn ln S
        else
          let D := difference is asInds
          mtrace on .zero with s!"[uniUpdateWrtMvars] found diff D {repr D}"
          -- let pre (R : ListProd3 IdxCollType (ListProd3 Nat Nat Expr) (ListProd3 Nat Nat Level)) :=
          --   if empty? D then R else .cons D tn ln R
          let mut ntn := tn
          let mut nln := ln
          let mut broke? := false
          for (mv, lv) in As do
            mtrace on .zero with s!"[uniUpdateWrtMvars] looking at assignement {repr mv} with val {← ppExpr lv}"
            match mv.name with
            | .num (.num _ backIdx) pos =>
                match tn.find? (fun x y _ => x == backIdx && y == pos) with
                | .none =>
                    ntn := (.cons backIdx pos lv ntn)
                | .some _ _ al => do
                    if (← defEqWiMv al lv l1 l2).isSome
                    then
                      continue
                    else
                      broke? := true
                      break
            | _ => panic s!"[uniUpdateWrtMvars] assignements from defeq contained level mvar not in format: {repr mv}"
          if broke?
          then return S --pre S
          else return (.cons I ntn nln S) --pre (.cons I ntn nln S)
      )

/- does **not** check if candidates are compatible ; keeps assignement from arg `B`-/
@[specialize, inline]
def uniUnion
  (empty? : IdxCollType → Bool) (intersect difference : IdxCollType → IdxCollType → IdxCollType)
  (A B : ListProd3 IdxCollType (ListProd3 Nat Nat Expr) (ListProd3 Nat Nat Level))
  : ListProd3 IdxCollType (ListProd3 Nat Nat Expr) (ListProd3 Nat Nat Level) :=
  A.foldl B (fun inds tn ln R =>
    let (pR,rem) := R.foldl (.nil, inds) (fun is ltn lln (R,inds) =>
      let I := intersect inds is
      if empty? I
      then (.cons is ltn lln R, inds)
      else
        let ninds := difference inds I
        let ntn := tn.foldl ltn (fun i j res TN =>
          match ltn.find? (fun x y _ => i == x && y == j) with
          | .none => .cons i j res TN
          | .some .. => TN
          )
        let nln := ln.foldl lln (fun i j res TN =>
          match lln.find? (fun x y _ => i == x && y == j) with
          | .none => .cons i j res TN
          | .some .. => TN
          )
        ((.cons I ntn nln R), ninds) --(pre (.cons I ntn nln R), ninds)
      )
    if empty? rem
    then pR
    else .cons rem tn ln pR
    )


/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/


import LeanGrowBeta.Data.PathIndex.Query
import LeanGrowBeta.Caching.Formating.Types

open Lean Meta

variable {IdxCollType : Type _}

namespace PaIn


@[specialize, inline]
def embedFwSiUpdateWrtLevel
  (empty? : IdxCollType → Bool) (intersect difference : IdxCollType → IdxCollType → IdxCollType)
  (asInds : IdxCollType) (mv : LMVarId) (lv : Level)
  (sofar : ListProd3 IdxCollType (ListProd Nat Expr) (ListProd Nat Level))
  : MetaM <| ListProd3 IdxCollType (ListProd Nat Expr) (ListProd Nat Level) :=
    sofar.foldlM .nil (fun is tn ln R => do
      let I := intersect asInds is
      if empty? I
      then return .cons is tn ln R
      else
          match mv.name with
          | .num _ pos =>
              match ln.find? (fun x _ => x == pos) with
              | .none =>
                  let D := difference is asInds
                  if empty? D
                  then
                    return .cons I tn (.cons pos lv ln) R
                  else
                    return .cons D tn ln <| .cons I tn (.cons pos lv ln) R
              | .some _ al =>
                  if ← (do let res ← isLevelDefEq al lv ; clearMvarAssignments ; return res)
                  then
                    return .cons is tn ln R
                  else
                    let D := difference is asInds
                    if empty? D
                    then
                      return R
                    else
                      return .cons D tn ln R
          | _ => panic s!"[embedFwSiUpdateWrtLevels] assignements from defeq contained level mvar not in format: {repr mv}"
      )





@[specialize, inline]
def embedFwSiUpdateWrtLevels [Repr IdxCollType]
  (empty? : IdxCollType → Bool) (intersect difference : IdxCollType → IdxCollType → IdxCollType)
  (asInds : IdxCollType) (As : PersistentHashMap LMVarId Level)
  (sofar : ListProd3 IdxCollType (ListProd Nat Expr) (ListProd Nat Level))
  : MetaM <| ListProd3 IdxCollType (ListProd Nat Expr) (ListProd Nat Level) :=
    -- trace set Tracing.Flags.none in
    sofar.foldlM .nil (fun is tn ln S => do
      let I := intersect asInds is
      if empty? I
      then
        mtrace on .zero with s!"[embedFwSiUpdateWrtLevels] empty inter, leve as is"
        return ListProd3.cons is tn ln S
      else
        mtrace on .zero with s!"[embedFwSiUpdateWrtLevels] intersection {repr I}"
        if As.isEmpty
        then return ListProd3.cons is tn ln S
        else
          let D := difference is asInds
          mtrace on .zero with s!"[embedFwSiUpdateWrtLevels] found diff D {repr D}"
          let pre (R : ListProd3 IdxCollType (ListProd Nat Expr) (ListProd Nat Level)) :=
            if empty? D then R else .cons D tn ln R
          let mut ntn := tn
          let mut nln := ln
          let mut broke? := false
          for (mv, lv) in As do
            mtrace on .zero with s!"[embedFwSiUpdateWrtLevels] looking at assignement {repr mv} with val {lv}"
            match mv.name with
            | .num _ pos =>
                match ln.find? (fun x _ => x == pos) with
                | .none =>
                    nln := (.cons pos lv nln)
                | .some _ al => do
                    if ← (do let res ← isLevelDefEq al lv ; clearMvarAssignments ; return res)
                    then
                      continue
                    else
                      broke? := true
                      break
            | _ => panic s!"[embedFwSiUpdateWrtLevels] assignements from defeq contained level mvar not in format: {repr mv}"
          if broke?
          then return pre S
          else return pre (.cons I ntn nln S)
      )




@[specialize, inline]
def embedFwSiUpdateWrtMvar
  (empty? : IdxCollType → Bool) (intersect difference : IdxCollType → IdxCollType → IdxCollType)
  (l1 : LocalContext) (l2 : LocalInstances)
  (asInds : IdxCollType) (mv : MVarId) (lv : Expr)
  (sofar : ListProd3 IdxCollType (ListProd Nat Expr) (ListProd Nat Level))
  : MetaM (ListProd3 IdxCollType (ListProd Nat Expr) (ListProd Nat Level)) :=
    sofar.foldlM .nil (fun is tn ln R =>
      let I := intersect asInds is
      if empty? I
      then return .cons is tn ln R
      else
        match mv.name with
        | .num (.num _ _) pos =>
            match tn.find? (fun x _ => x == pos) with
            | .none =>
                let D := difference is asInds
                if empty? D
                then
                  return .cons I (.cons pos lv tn) ln R
                else
                  return .cons D tn ln <| .cons I (.cons pos lv tn) ln R
            | .some _ al => do
                if (← defEqWiMv al lv l1 l2).isSome
                then
                  return .cons is tn ln R
                else
                  let D := difference is asInds
                  if empty? D
                  then
                    return R
                  else
                    return .cons D tn ln R
        | _ => panic s!"[embedFwSiUpdateWrtMvar] assignements from defeq contained level mvar not in format: {repr mv}"
      )





@[specialize, inline]
def embedFwSiUpdateWrtMvars [Repr IdxCollType]
  (empty? : IdxCollType → Bool) (intersect difference : IdxCollType → IdxCollType → IdxCollType)
  (l1 : LocalContext) (l2 : LocalInstances)
  (asInds : IdxCollType) (As : PersistentHashMap MVarId Expr)
  (sofar : ListProd3 IdxCollType (ListProd Nat Expr) (ListProd Nat Level))
  : MetaM (ListProd3 IdxCollType (ListProd Nat Expr) (ListProd Nat Level)) :=
    -- trace set Tracing.Flags.none in do
    do
    mtrace on .zero with s!"[embedFwSiUpdateWrtMvars] call on asInds {repr asInds}"
    sofar.foldlM .nil (fun is tn ln S => do
      let I := intersect asInds is
      if empty? I
      then
        mtrace on .zero with s!"[embedFwSiUpdateWrtMvars] is had empty intersection , leaving ; is {repr is}"
        return .cons is tn ln S
      else
        mtrace on .zero with s!"[embedFwSiUpdateWrtMvars] found intersection I {repr I}"
        if As.isEmpty
        then return ListProd3.cons is tn ln S
        else
          let D := difference is asInds
          mtrace on .zero with s!"[embedFwSiUpdateWrtMvars] found diff D {repr D}"
          let pre (R : ListProd3 IdxCollType (ListProd Nat Expr) (ListProd Nat Level)) :=
            if empty? D then R else .cons D tn ln R
          let mut ntn := tn
          let mut nln := ln
          let mut broke? := false
          for (mv, lv) in As do
            mtrace on .zero with s!"[embedFwSiUpdateWrtMvars] looking at assignement {repr mv} with val {← ppExpr lv}"
            match mv.name with
            | .num _ pos =>
                match tn.find? (fun x _ => x == pos) with
                | .none =>
                    ntn := (.cons pos lv ntn)
                | .some _ al => do
                    if (← defEqWiMv al lv l1 l2).isSome
                    then
                      continue
                    else
                      broke? := true
                      break
            | _ => panic s!"[embedFwSiUpdateWrtMvars] assignements from defeq contained level mvar not in format: {repr mv}"
          if broke?
          then return pre S
          else return pre (.cons I ntn nln S)
      )




/- does **not** check if candidates are compatible ; keeps assignement fromarg `B`-/
@[specialize, inline]
def embedUnionFwSi
  (empty? : IdxCollType → Bool) (intersect difference : IdxCollType → IdxCollType → IdxCollType)
  (A B : ListProd3 IdxCollType (ListProd Nat Expr) (ListProd Nat Level))
  : ListProd3 IdxCollType (ListProd Nat Expr) (ListProd Nat Level) :=
  A.foldl B (fun inds tn ln R =>
    let (pR,rem) := R.foldl (.nil, inds) (fun is ltn lln (R,inds) =>
      let I := intersect inds is
      if empty? I
      then (.cons is ltn lln R, inds)
      else
        let ninds := difference inds I
        let D := difference is inds
        let pre (R : ListProd3 IdxCollType (ListProd Nat Expr) (ListProd Nat Level)) :=
          (if empty? D then R else .cons D ltn lln R)
        let ntn := tn.foldl ltn (fun i res TN =>
          match ltn.find? (fun x _ => i == x) with
          | .none => .cons i res TN
          | .some .. => TN
          )
        let nln := ln.foldl lln (fun i res TN =>
          match ltn.find? (fun x _ => i == x) with
          | .none => .cons i res TN
          | .some .. => TN
          )
        (pre (.cons I ntn nln R), ninds)
      )
    if empty? rem
    then pR
    else .cons rem tn ln pR
    )




@[specialize, inline]
def embedForwSimpleRevert
  [Repr IdxCollType] [ToString IdxCollType]
  (empty? : IdxCollType → Bool) (intersect union difference : IdxCollType → IdxCollType → IdxCollType)
  (empty : IdxCollType)
  (l1 : LocalContext) (l2 : LocalInstances)
  (E : Expr) (T : PaIn IdxCollType) (workas : List FVarId)
  (constr : IdxCollType) (uni : ListProd3 IdxCollType (ListProd Nat Expr) (ListProd Nat Level))
  : MetaM (Prod5 Bool IdxCollType (ListProd3 IdxCollType (ListProd Nat Expr) (ListProd Nat Level)) LocalContext LocalInstances) :=
  -- trace set Tracing.Flags.none in do
  do
  let built := T.buildCore workas 0
    (fun inds => intersect inds constr)
    intersect empty?
  mtrace on .zero with s!"[embedForwSimpleRevert] call on E {← ppExpr E}"
  mtrace on .zero with s!"[embedForwSimpleRevert] with built {← ppPainHelp l1 l2 built}"
  mtrace on .zero with s!"[embedForwSimpleRevert] and constr {repr constr}"
  mtrace on .one with s!"[embedForwSimpleRevert] and uni {toString uni}"
  built.foldlMcps (empty, uni) (fun e inds (Sc,Su) cont => do
    match ← defEqWiMv E e l1 l2 with
    | .none =>
        mtrace on .zero with s!"[embedForwSimpleRevert] negative defeq of e {← ppExpr e} and E {← ppExpr E} for inds {repr inds}"
        let Su := Su.foldl ListProd3.nil (fun ds ts ls R =>
          let ds := difference ds inds
          if empty? ds
          then R
          else .cons ds ts ls R
          )
        let Sc := difference Sc inds
        cont (Sc, Su)
    | .some (La, Ta) => do
        mtrace on .zero with s!"[embedForwSimpleRevert] positive defeq of e {← ppExpr e} and E {← ppExpr E} for inds {repr inds}"
        let mut broke? := false
        for (_,as) in Ta do
          if as.hasWorkerTR
          then
            broke? := true
            break
        if broke?
        then
          -- If defeq required assigning to expr containing workers, then treat it as a failure
          mtrace on .zero with s!"[embedForwSimpleRevert] assigned workers, discarding"
          let Su := Su.foldl ListProd3.nil (fun ds ts ls R =>
            let ds := difference ds inds
            if empty? ds
            then R
            else .cons ds ts ls R
            )
          let Sc := difference Sc inds
          cont (Sc, Su)
        else
          let fst ← embedFwSiUpdateWrtMvars empty? intersect difference l1 l2 inds Ta Su
          mtrace on .one with s!"[embedForwSimpleRevert] and fst {toString fst}"
          let Su ← embedFwSiUpdateWrtLevels empty? intersect difference inds La fst
          mtrace on .one with s!"[embedForwSimpleRevert] and Su {toString Su}"
          let Sc := Su.foldl empty (fun ds _ _ R =>
            union ds R)
          cont (Sc, Su)
  ) <| fun (resI,resU) => do
    mtrace on .zero with s!"[embedForwSimpleRevert] proceeding with constr {repr resI}"
    mtrace on .one with s!"[embedForwSimpleRevert] and resU {toString resU}"
    if empty? resI
    then return ⟨false,resI,resU,l1,l2⟩
    else return ⟨true,resI,resU,l1,l2⟩




@[specialize, inline]
partial def embedForwSimpleCore
    [expl : Repr IdxCollType] [ToString IdxCollType]
    (empty? : IdxCollType → Bool) (intersect union difference : IdxCollType → IdxCollType → IdxCollType) (empty : IdxCollType)
    (l1 : LocalContext) (l2 : LocalInstances)
    (constr : IdxCollType)
    (revCountMax : Nat)
    (E : Expr) (T : PaIn IdxCollType)
    : MetaM (Prod5 UInt8 IdxCollType (ListProd3 IdxCollType (ListProd Nat Expr) (ListProd Nat Level)) LocalContext LocalInstances) :=
      -- trace set Tracing.Flags.none in
      let inittodo := .cons E T [] .nil
      @queryCore IdxCollType expl l1 l2 (ListProd3 IdxCollType (ListProd Nat Expr) (ListProd Nat Level))
        (embedUnionFwSi empty? intersect difference)
        empty? intersect union
        constr (.cons constr .nil .nil .nil)
        true true false false
        0 revCountMax
        .nil
        inittodo
        (fun E T workas constr uni l1 l2 => do
          mtrace on .zero with s!"[embedForwSimpleCore] workas {repr workas}"
          embedForwSimpleRevert empty?  intersect union difference empty l1 l2 E T workas constr uni)
        (fun _ _ _ constr uni l1 l2 => return ⟨constr,uni,l1,l2⟩)
        (fun _ _ _ constr uni l1 l2 => return ⟨constr,uni,l1,l2⟩)
        (fun _ _ _ _ api constr uni naive? l1 l2 =>
          let constr := intersect api constr
          if empty? constr
          then if naive? then return ⟨0,constr,uni,l1,l2⟩ else return ⟨1,constr,uni,l1,l2⟩
          else
            let uni := uni.foldl .nil (fun is tn ln R =>
              let I := intersect api is
              if empty? I
              then R
              else .cons I tn ln R
              )
            return ⟨2,constr,uni,l1,l2⟩
          )
        (fun _ _ _ _ api constr uni naive? l1 l2 =>
          let constr := intersect api constr
          if empty? constr
          then if naive? then return ⟨0,constr,uni,l1,l2⟩ else return ⟨1,constr,uni,l1,l2⟩
          else
            let uni := uni.foldl .nil (fun is tn ln R =>
              let I := intersect api is
              if empty? I
              then R
              else .cons I tn ln R
              )
            return ⟨2,constr,uni,l1,l2⟩
          )
        (fun _ _ _ _ api constr uni naive? l1 l2 =>
          let constr := intersect api constr
          if empty? constr
          then if naive? then return ⟨0,constr,uni,l1,l2⟩ else return ⟨1,constr,uni,l1,l2⟩
          else
            let uni := uni.foldl .nil (fun is tn ln R =>
              let I := intersect api is
              if empty? I
              then R
              else .cons I tn ln R
              )
            return ⟨2,constr,uni,l1,l2⟩
          )
        (fun _ _ _ _ _ _ api constr uni naive? l1 l2 =>
          let constr := intersect api constr
          if empty? constr
          then if naive? then return ⟨0,constr,uni,l1,l2⟩ else return ⟨1,constr,uni,l1,l2⟩
          else
            let uni := uni.foldl .nil (fun is tn ln R =>
              let I := intersect api is
              if empty? I
              then R
              else .cons I tn ln R
              )
            return ⟨2,constr,uni,l1,l2⟩
          )
        (fun n i e projs constr uni naive? l1 l2 =>
          let nbt := n.toString.toUTF8
          match projs.find? nbt with
          | .none => if naive? then return ⟨0,.none,constr,uni,l1,l2⟩ else return ⟨1,.none,constr,uni,l1,l2⟩
          | .some D =>
              match D.find? (fun _ (j, _) => j == i) with
              | .none => if naive? then return ⟨0,.none,constr,uni,l1,l2⟩ else return ⟨1,.none,constr,uni,l1,l2⟩
              | .some inds (_,pT) =>
                  let constr := intersect constr inds
                  if empty? constr
                  then if naive? then return ⟨0,.none,constr,uni,l1,l2⟩ else return ⟨1,.none,constr,uni,l1,l2⟩
                  else
                    let uni := uni.foldl .nil (fun is tn ln R =>
                      let I := intersect inds is
                      if empty? I
                      then R
                      else .cons I tn ln R
                      )
                    return ⟨2,.some e pT,constr,uni,l1,l2⟩
          )
        (fun i bvs constr uni naive? l1 l2 =>
          match bvs.find_pain_nat i with
          | .none => if naive? then return ⟨0,constr,uni,l1,l2⟩ else return ⟨1,constr,uni,l1,l2⟩
          | .some inds _ =>
              let constr := intersect inds constr
              if empty? constr
              then if naive? then return ⟨0,constr,uni,l1,l2⟩ else return ⟨1,constr,uni,l1,l2⟩
              else
                let uni := uni.foldl .nil (fun is tn ln R =>
                  let I := intersect inds is
                  if empty? I
                  then R
                  else .cons I tn ln R
                  )
                return ⟨2,constr,uni,l1,l2⟩
          )
        (fun i bvs constr uni naive? l1 l2 =>
          match bvs.find_pain_nat i with
          | .none => if naive? then return ⟨0,constr,uni,l1,l2⟩ else return ⟨1,constr,uni,l1,l2⟩
          | .some inds _ =>
              let constr := intersect inds constr
              if empty? constr
              then if naive? then return ⟨0,constr,uni,l1,l2⟩ else return ⟨1,constr,uni,l1,l2⟩
              else
                let uni := uni.foldl .nil (fun is tn ln R =>
                  let I := intersect inds is
                  if empty? I
                  then R
                  else .cons I tn ln R
                  )
                return ⟨2,constr,uni,l1,l2⟩
          )
        (fun i bvs constr uni naive? l1 l2 =>
          match bvs.find_pain_nat i with
          | .none => if naive? then return ⟨0,constr,uni,l1,l2⟩ else return ⟨1,constr,uni,l1,l2⟩
          | .some inds _ =>
              let constr := intersect inds constr
              if empty? constr
              then if naive? then return ⟨0,constr,uni,l1,l2⟩ else return ⟨1,constr,uni,l1,l2⟩
              else
                let uni := uni.foldl .nil (fun is tn ln R =>
                  let I := intersect inds is
                  if empty? I
                  then R
                  else .cons I tn ln R
                  )
                return ⟨2,constr,uni,l1,l2⟩
          )
        -- sorts affected
        (fun i bvs constr uni naive? l1 l2 => do
          if i.hasMVar
          then
            match bvs with
            | .nil => if naive? then return ⟨0,constr,uni,l1,l2⟩ else return ⟨1,constr,uni,l1,l2⟩
            | _ =>
              let (constr, uni) ← bvs.foldlM (constr, uni) (fun inds lv (constr, uni) => do
                match ← defEqNoMv (.sort i) (.sort lv) with
                | .none =>
                  let uni := uni.foldl ListProd3.nil (fun ds ts ls R =>
                    let ds := difference ds inds
                    if empty? ds
                    then R
                    else .cons ds ts ls R
                    )
                  let constr := difference constr inds
                  return (constr, uni)
                | .some (Ls,_) =>
                  let uni ← embedFwSiUpdateWrtLevels empty? intersect difference inds Ls uni
                  let constr := uni.foldl empty (fun ds _ _ R =>
                    union ds R)
                  return (constr, uni)
                )
              mtrace on .zero with s!"[embedForwSimpleCore] looking at sort {i}"
              mtrace on .zero with s!"[embedForwSimpleCore] proceeding with constr {repr constr}"
              mtrace on .one with s!"[embedForwSimpleCore] and uni {toString uni}"
              if empty? constr
              then if naive? then return ⟨0,constr,uni,l1,l2⟩ else return ⟨1,constr,uni,l1,l2⟩
              else return ⟨2,constr,uni,l1,l2⟩
          else
            match bvs.find? (fun _ j => j == i) with
            | .none => if naive? then return ⟨0,constr,uni,l1,l2⟩ else return ⟨1,constr,uni,l1,l2⟩
            | .some inds _ =>
                let constr := intersect inds constr
                if empty? constr
                then if naive? then return ⟨0,constr,uni,l1,l2⟩ else return ⟨1,constr,uni,l1,l2⟩
                else
                  let uni := uni.foldl .nil (fun is tn ln R =>
                    let I := intersect inds is
                    if empty? I
                    then R
                    else .cons I tn ln R
                    )
                  return ⟨2,constr,uni,l1,l2⟩
          )
        (fun i bvs constr uni naive? l1 l2 =>
          match bvs.find? (fun _ j => j == i) with
          | .none => if naive? then return ⟨0,constr,uni,l1,l2⟩ else return ⟨1,constr,uni,l1,l2⟩
          | .some inds _ =>
              let constr := intersect inds constr
              if empty? constr
              then if naive? then return ⟨0,constr,uni,l1,l2⟩ else return ⟨1,constr,uni,l1,l2⟩
              else
                let uni := uni.foldl .nil (fun is tn ln R =>
                  let I := intersect inds is
                  if empty? I
                  then R
                  else .cons I tn ln R
                  )
                return ⟨2,constr,uni,l1,l2⟩
          )
        -- consts affected
        (fun n l bvs constr uni naive? l1 l2 =>
          if !(l.any Level.hasMVar)
          then
            match ListProd.find_pain_const bvs n l with
            | .none => if naive? then return ⟨0,constr,uni,l1,l2⟩ else return ⟨1,constr,uni,l1,l2⟩
            | .some inds _ =>
                let constr := intersect inds constr
                if empty? constr
                then if naive? then return ⟨0,constr,uni,l1,l2⟩ else return ⟨1,constr,uni,l1,l2⟩
                else
                  let uni := uni.foldl .nil (fun is tn ln R =>
                    let I := intersect inds is
                    if empty? I
                    then R
                    else .cons I tn ln R
                    )
                  return ⟨2,constr,uni,l1,l2⟩
          else
            match bvs.find? n.toString.toUTF8 with
            | .none => if naive? then return ⟨0,constr,uni,l1,l2⟩ else return ⟨1,constr,uni,l1,l2⟩
            | .some D => do
                let (constr, uni) ← D.foldlM (constr, uni) (fun inds lvls (constr, uni) => do
                  match ← defEqNoMv (.const n l) (.const n lvls) with
                  | .none =>
                    let uni := uni.foldl ListProd3.nil (fun ds ts ls R =>
                      let ds := difference ds inds
                      if empty? ds
                      then R
                      else .cons ds ts ls R
                      )
                    let constr := difference constr inds
                    return (constr, uni)
                  | .some (Ls,_) =>
                    let uni ← embedFwSiUpdateWrtLevels empty? intersect difference inds Ls uni
                    let constr := uni.foldl empty (fun ds _ _ R =>
                      union ds R)
                    return (constr, uni)
                  )
                mtrace on .zero with s!"[embedForwSimpleCore] looking at const {n} {l}"
                mtrace on .zero with s!"[embedForwSimpleCore] proceeding with constr {repr constr}"
                mtrace on .one with s!"[embedForwSimpleCore] and uni {toString uni}"
                if empty? constr
                then if naive? then return ⟨0,constr,uni,l1,l2⟩ else return ⟨1,constr,uni,l1,l2⟩
                else return ⟨2,constr,uni,l1,l2⟩
          )
        -- tnodes
        (fun n l _ _ _ _ _ _ _ _ _ =>
          throwError s!"[embedForwSimpleCore] unexpected tnode {n} {l}"
          )
        (fun n i j _ workas T constr uni naive? l1 l2 => do
          let ⟨su,a,b,c,d⟩ ← embedForwSimpleRevert empty?  intersect union difference empty l1 l2 (.mvar ⟨lnode n i j⟩) T
            workas constr uni --success (if naive? then nfail else rfail)
          if su then return ⟨2,a,b,c,d⟩ else (if naive? then return ⟨0,a,b,c,d⟩ else return ⟨1,a,b,c,d⟩)
          )



@[specialize]
partial def embedForwSimpleMainWiLoad
    [expl : Repr IdxCollType] [ToString IdxCollType]
    (empty? : IdxCollType → Bool) (intersect union difference : IdxCollType → IdxCollType → IdxCollType) (empty : IdxCollType)
    (thmData : ThmFormat)
    (l1 : LocalContext) (l2 : LocalInstances)
    (constr : IdxCollType)
    (revCountMax : Nat)
    (E : Expr) (T : PaIn IdxCollType)
    : MetaM (Prod5 UInt8 IdxCollType (ListProd3 IdxCollType (ListProd Nat Expr) (ListProd Nat Level)) LocalContext LocalInstances) :=
    do
    clearMvarAssignments -- this is needed so that we may fold over assignement PHachMaps in ↓ and get new assignements only
    thmData.mctx.load
    embedForwSimpleCore empty? intersect union difference empty l1 l2 constr revCountMax E T

@[specialize]
partial def embedForwSimpleMainNoLoad
    [expl : Repr IdxCollType] [ToString IdxCollType]
    (empty? : IdxCollType → Bool) (intersect union difference : IdxCollType → IdxCollType → IdxCollType) (empty : IdxCollType)
    (l1 : LocalContext) (l2 : LocalInstances)
    (constr : IdxCollType)
    (revCountMax : Nat)
    (E : Expr) (T : PaIn IdxCollType)
    : MetaM (Prod5 UInt8 IdxCollType (ListProd3 IdxCollType (ListProd Nat Expr) (ListProd Nat Level)) LocalContext LocalInstances) :=
    do
    clearMvarAssignments -- this is needed so that we may fold over assignement PHachMaps in ↓ and get new assignements only
    embedForwSimpleCore empty? intersect union difference empty l1 l2 constr revCountMax E T

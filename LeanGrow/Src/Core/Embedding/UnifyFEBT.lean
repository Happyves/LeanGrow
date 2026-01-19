
/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/


import LeanGrow.Src.Core.Embedding.UnifyAPI

open Lean Meta PaInG


variable {IdxCollType : Type _}

namespace PaInG


@[specialize, inline]
def uniDefEqCore [Repr IdxCollType]
  (empty? : IdxCollType → Bool) (intersect union difference : IdxCollType → IdxCollType → IdxCollType)
  (empty : IdxCollType)
  (l1 : LocalContext) (l2 : LocalInstances)
  (E e : Expr) (inds : IdxCollType)
  (Sc : IdxCollType) (Su : ListProd3 IdxCollType (ListProd3 Nat Nat Expr) (ListProd3 Nat Nat Level))
  : MetaM (IdxCollType × ListProd3 IdxCollType (ListProd3 Nat Nat Expr) (ListProd3 Nat Nat Level)) :=
  -- trace set Tracing.Flags.none in do
  withReader (fun ctx => {ctx with lctx := l1, localInstances := l2}) do
  mtracing
  match ← defEqWiMv E e l1 l2 with
  | .none =>
      mtrace on .zero with s!"[uniDefEqCore] negative defeq of e {← ppExpr e} and E {← ppExpr E}"
      let Su := Su.foldl ListProd3.nil (fun ds ts ls R =>
        let ds := difference ds inds
        if empty? ds
        then R
        else .cons ds ts ls R
        )
      let Sc := difference Sc inds
      return (Sc, Su)
  | .some (La, Ta) => do
      mtrace on .zero with s!"[uniDefEqCore] positive defeq of e {← ppExpr e} and E {← ppExpr E}"
      let mut broke? := false
      for (_,as) in Ta do
        if as.hasWorkerTR
        then
          broke? := true
          break
      if broke?
      then
        -- If defeq required assigning to expr containing workers, then treat it as a failure
        let Su := Su.foldl ListProd3.nil (fun ds ts ls R =>
          let ds := difference ds inds
          if empty? ds
          then R
          else .cons ds ts ls R
          )
        let Sc := difference Sc inds
        return (Sc, Su)
      else
        let fst ← uniUpdateWrtMvars empty? intersect difference l1 l2 inds Ta Su
        let Su ← uniUpdateWrtLevels empty? intersect difference inds La fst
        let Sc := Su.foldl empty (fun ds _ _ R =>
          union ds R)
        return (Sc, Su)



@[specialize, inline]
def uniFEwBTrevert
  [Repr IdxCollType] [ToString IdxCollType]
  (empty? : IdxCollType → Bool) (intersect union difference : IdxCollType → IdxCollType → IdxCollType)
  (empty : IdxCollType)
  (l1 : LocalContext) (l2 : LocalInstances)
  (E : Expr) (T : PaInG IdxCollType) (workas : List FVarId)
  (constr : IdxCollType) (uni : ListProd3 IdxCollType (ListProd3 Nat Nat Expr) (ListProd3 Nat Nat Level))
  : MetaM (Prod5 Bool IdxCollType (ListProd3 IdxCollType (ListProd3 Nat Nat Expr) (ListProd3 Nat Nat Level)) LocalContext LocalInstances) :=
  -- trace set Tracing.Flags.none in do
  withReader (fun ctx => {ctx with lctx := l1, localInstances := l2}) do
  mtracing
  let built ← T.buildMvarifyTnodesNoCo l1 l2 workas 0
    (fun inds => intersect inds constr)
    intersect empty?
  mtrace on .zero with s!"[uniFEwBTrevert] call on E {← ppExpr E}"
  mtrace on .zero with s!"[uniFEwBTrevert] with built {← ppPaInGHelp l1 l2 built}"
  mtrace on .zero with s!"[uniFEwBTrevert] and constr {repr constr}"
  mtrace on .one with s!"[uniFEwBTrevert] and uni {toString uni}"
  let (resI,resU) ← built.foldlM (empty, uni) (fun e inds (Sc,Su) => do
    uniDefEqCore empty? intersect union difference empty l1 l2 E e inds Sc Su)
  mtrace on .zero with s!"[uniFEwBTrevert] proceeding with constr {repr constr}"
  mtrace on .one with s!"[uniFEwBTrevert] and resU {toString resU}"
  if empty? resI
  then return ⟨false, resI, resU,l1,l2⟩
    else return ⟨true, resI, resU,l1,l2⟩




@[specialize, inline]
def uniTnodes
  (empty? : IdxCollType → Bool) (intersect union : IdxCollType → IdxCollType → IdxCollType) (empty : IdxCollType)
  (l1 : LocalContext) (l2 : LocalInstances)
  (e : Expr) (tnodes : ListProd IdxCollType (Nat × Nat))
  (constr : IdxCollType) (uni : (ListProd3 IdxCollType (ListProd3 Nat Nat Expr) (ListProd3 Nat Nat Level)))
  : MetaM (Prod5 Bool IdxCollType (ListProd3 IdxCollType (ListProd3 Nat Nat Expr) (ListProd3 Nat Nat Level)) LocalContext LocalInstances) :=
    -- trace set Tracing.Flags.none in do
  withReader (fun ctx => {ctx with lctx := l1, localInstances := l2}) do
    mtracing
    mtrace on .zero with s!"[uniTnodes] call on e {← ppExpr e}"
    tnodes.foldlM ⟨false,empty,.nil,l1,l2⟩ (fun is (bIdx,pos) ⟨ match?,sI, sU,l1,l2⟩ => do
      let I := intersect is constr
      if empty? I
      then return ⟨ match?,sI, sU,l1,l2⟩
      else
        let tn := tnode bIdx pos
        let T ← (⟨tn⟩ : FVarId).getType
        let ⟨T,l1,l2⟩ ← mvarifyTnodesRec T l1 l2
        withReader (fun ctx => {ctx with lctx := l1, localInstances := l2}) do
        mtrace on .zero with s!"[uniTnodes] looking at {tn} with mvaified type {← ppExpr T}"
        let mv ← mkMvarStdNoCoE tn T
        match ← defEqWiMv mv e l1 l2 with
        | .none =>
            mtrace on .zero with s!"[uniTnodes] negative defeq"
            return ⟨ match?,sI, sU,l1,l2⟩
        | .some (La, Ta) => do
            mtrace on .zero with s!"[uniTnodes] positive defeq"
            let mut broke? := false
            for (mvtt,as) in Ta do
              if as.hasWorkerTR
              then
                mtrace on .zero with s!"[uniTnodes] assigned woker at {repr mvtt} via {← ppExpr as}"
                broke? := true
                break
            if broke?
            then
              return ⟨ match?,sI, sU,l1,l2⟩
            else
              uni.foldlM ⟨ match?,sI, sU,l1,l2⟩ (fun inds tn ln ⟨ match?,sI, sU,l1,l2⟩ => do
                let II := intersect inds I
                if empty? II
                then return ⟨ match?,sI, sU,l1,l2⟩
                else
                  let mut ntn := tn
                  let mut nln := ln
                  let mut nope? := false
                  for (mv,lv) in La do
                    match mv.name with
                    | .num (.num _ backIdx) pos =>
                        match ln.find? (fun x y _ => x == backIdx && y == pos) with
                        | .none =>
                            nln := .cons backIdx pos lv nln
                        | .some _ _ al =>
                            if ← (do let res ← isLevelDefEq al lv ; clearMvarAssignments ; return res)
                            then
                              continue
                            else
                              nope? := true
                              break
                    | _ => panic s!"[uniTnodes] assignements from defeq contained level mvar not in format: {repr mv}"
                  if nope?
                  then
                    return ⟨ match?,sI, sU,l1,l2⟩
                  else
                    for (mv,lv) in Ta do
                      match mv.name with
                      | .num (.num _ backIdx) pos =>
                          match tn.find? (fun x y _ => x == backIdx && y == pos) with
                          | .none =>
                              ntn := .cons backIdx pos lv ntn
                          | .some _ _ al =>
                              if (← defEqWiMv al lv l1 l2).isSome
                              then
                                continue
                              else
                                nope? := true
                                break
                      | _ => panic s!"[uniTnodes] assignements from defeq contained level mvar not in format: {repr mv}"
                    if nope?
                    then
                      return ⟨ match?,sI, sU,l1,l2⟩
                    else
                      let sI := union II sI
                      let sU := .cons II ntn nln sU
                      return ⟨true,sI, sU,l1,l2⟩
                ))



@[specialize]
partial def uniFEwBTCore
    [expl : Repr IdxCollType] [ToString IdxCollType]
    (empty? : IdxCollType → Bool) (intersect union difference : IdxCollType → IdxCollType → IdxCollType) (empty : IdxCollType)
    (l1 : LocalContext) (l2 : LocalInstances)
    (constr : IdxCollType)
    (revCountMax : Nat)
    (E : Expr) (T : PaInG IdxCollType)
    : MetaM (Prod5 UInt8 IdxCollType (ListProd3 IdxCollType (ListProd3 Nat Nat Expr) (ListProd3 Nat Nat Level)) LocalContext LocalInstances) :=
      trace set TracingFlags.none in
      let inittodo := .cons E T [] .nil
      do
      mtracing
      @queryLCore IdxCollType expl l1 l2 (ListProd3 IdxCollType (ListProd3 Nat Nat Expr) (ListProd3 Nat Nat Level))
        (fun x y => let res := uniUnion empty? intersect difference x y ; trace on .two with s!"[uniFEwBTCore] union res {toString res}" in res )
        empty? intersect union
        constr (.cons constr .nil .nil .nil)
        true true false false
        0 revCountMax
        .nil
        inittodo
        (fun E T workas constr uni l1 l2 => do
          uniFEwBTrevert empty? intersect union difference empty l1 l2 E T workas constr uni)
        (fun e _ tnodes constr uni l1 l2 => do
            uniTnodes empty? intersect union empty l1 l2 e tnodes constr uni)
        (fun sI sS _ _ _ _ _ l1 l2 => return .mk false sI sS l1 l2)
        (fun _ _ _ _ api constr uni naive? l1 l2 => do
          mtrace on .two with s!"[uniFEwBTCore] uni {toString uni}"
          let constr := intersect api constr
          if empty? constr
          then if naive? then return ⟨0,constr, uni, l1,l2⟩ else return ⟨1,constr, uni, l1,l2⟩
          else
            let uni := uni.foldl .nil (fun is tn ln R =>
              let I := intersect api is
              if empty? I
              then R
              else .cons I tn ln R
              )
            return ⟨2,constr, uni, l1,l2⟩
          )
        (fun _ _ _ _ api constr uni naive? l1 l2 => do
          mtrace on .two with s!"[uniFEwBTCore] uni {toString uni}"
          let constr := intersect api constr
          if empty? constr
          then if naive? then return ⟨0,constr, uni, l1,l2⟩ else return ⟨1,constr, uni, l1,l2⟩
          else
            let uni := uni.foldl .nil (fun is tn ln R =>
              let I := intersect api is
              if empty? I
              then R
              else .cons I tn ln R
              )
            return ⟨2,constr, uni, l1,l2⟩
          )
        (fun _ _ _ _ api constr uni naive? l1 l2 => do
          mtrace on .two with s!"[uniFEwBTCore] uni {toString uni}"
          let constr := intersect api constr
          if empty? constr
          then if naive? then return ⟨0,constr, uni, l1,l2⟩ else return ⟨1,constr, uni, l1,l2⟩
          else
            let uni := uni.foldl .nil (fun is tn ln R =>
              let I := intersect api is
              if empty? I
              then R
              else .cons I tn ln R
              )
            return ⟨2,constr, uni, l1,l2⟩
          )
        (fun _ _ _ _ _ _ api constr uni naive? l1 l2 => do
          mtrace on .two with s!"[uniFEwBTCore] uni {toString uni}"
          let constr := intersect api constr
          if empty? constr
          then if naive? then return ⟨0,constr, uni, l1,l2⟩ else return ⟨1,constr, uni, l1,l2⟩
          else
            let uni := uni.foldl .nil (fun is tn ln R =>
              let I := intersect api is
              if empty? I
              then R
              else .cons I tn ln R
              )
            return ⟨2,constr, uni, l1,l2⟩
          )
        (fun n i e projs constr uni naive? l1 l2 => do
          mtrace on .two with s!"[uniFEwBTCore] uni {toString uni}"
          let nbt := n.toString.toUTF8
          match projs.find? nbt with
          | .none => if naive? then return ⟨0,.none,constr, uni, l1,l2⟩ else return ⟨1,.none,constr, uni, l1,l2⟩
          | .some D =>
              match D.find? (fun _ (j, _) => j == i) with
              | .none => if naive? then return ⟨0,.none,constr, uni, l1,l2⟩ else return ⟨1,.none,constr, uni, l1,l2⟩
              | .some inds (_,pT) =>
                  let constr := intersect constr inds
                  if empty? constr
                  then if naive? then return ⟨0,.none,constr, uni, l1,l2⟩ else return ⟨1,.none,constr, uni, l1,l2⟩
                  else
                    let uni := uni.foldl .nil (fun is tn ln R =>
                      let I := intersect inds is
                      if empty? I
                      then R
                      else .cons I tn ln R
                      )
                    return ⟨0,.some e pT,constr, uni, l1,l2⟩
          )
        (fun i bvs constr uni naive? l1 l2 => do
          mtrace on .two with s!"[uniFEwBTCore] uni {toString uni}"
          match bvs.find_PaInG_nat i with
          | .none => if naive? then return ⟨0,constr, uni, l1,l2⟩ else return ⟨1,constr, uni, l1,l2⟩
          | .some inds _ =>
              let constr := intersect inds constr
              if empty? constr
              then if naive? then return ⟨0,constr, uni, l1,l2⟩ else return ⟨1,constr, uni, l1,l2⟩
              else
                let uni := uni.foldl .nil (fun is tn ln R =>
                  let I := intersect inds is
                  if empty? I
                  then R
                  else .cons I tn ln R
                  )
                return ⟨2,constr, uni, l1,l2⟩
          )
        (fun i bvs constr uni naive? l1 l2 => do
          mtrace on .two with s!"[uniFEwBTCore] uni {toString uni}"
          match bvs.find_PaInG_nat i with
          | .none => if naive? then return ⟨0,constr, uni, l1,l2⟩ else return ⟨1,constr, uni, l1,l2⟩
          | .some inds _ =>
              let constr := intersect inds constr
              if empty? constr
              then if naive? then return ⟨0,constr, uni, l1,l2⟩ else return ⟨1,constr, uni, l1,l2⟩
              else
                let uni := uni.foldl .nil (fun is tn ln R =>
                  let I := intersect inds is
                  if empty? I
                  then R
                  else .cons I tn ln R
                  )
                return ⟨2,constr, uni, l1,l2⟩
          )
        (fun i bvs constr uni naive? l1 l2 => do
          mtrace on .two with s!"[uniFEwBTCore] uni {toString uni}"
          match bvs.find_PaInG_nat i with
          | .none => if naive? then return ⟨0,constr, uni, l1,l2⟩ else return ⟨1,constr, uni, l1,l2⟩
          | .some inds _ =>
              let constr := intersect inds constr
              if empty? constr
              then if naive? then return ⟨0,constr, uni, l1,l2⟩ else return ⟨1,constr, uni, l1,l2⟩
              else
                let uni := uni.foldl .nil (fun is tn ln R =>
                  let I := intersect inds is
                  if empty? I
                  then R
                  else .cons I tn ln R
                  )
                return ⟨2,constr, uni, l1,l2⟩
          )
        -- sorts affected
        (fun i bvs constr uni naive? l1 l2 => do
          mtrace on .two with s!"[uniFEwBTCore] uni {toString uni}"
          match bvs with
          | .nil => if naive? then return ⟨0,constr, uni, l1,l2⟩ else return ⟨1,constr, uni, l1,l2⟩
          | _ =>
            let (constr, uni) ← bvs.foldlM (constr, uni) (fun inds lv (constr, uni) => do
              let ⟨lv,l1,l2⟩ ← mvarifyLTnodesIn lv l1 l2
              match ← defEqWiMv (.sort i) (.sort lv) l1 l2  with
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
                uni.foldlMcps (.nil : ListProd3 IdxCollType (ListProd3 Nat Nat Expr) (ListProd3 Nat Nat Level)) (fun indsU tn ln R cont => do
                  let I := intersect inds indsU
                  if empty? I
                  then cont <| .cons indsU tn ln R
                  else
                    let mut ntn := tn
                    let mut nln := ln
                    let mut nope? := false
                    for (mv,lv) in Ls do
                      match mv.name with
                      | .num (.num _ backIdx) pos =>
                          match ln.find? (fun x y _ => x == backIdx && y == pos) with
                          | .none =>
                              nln := .cons backIdx pos lv nln
                          | .some _ _ al =>
                              if ← (do let res ← isLevelDefEq al lv ; clearMvarAssignments ; return res)
                              then
                                continue
                              else
                                nope? := true
                                break
                      | _ => panic s!"[uniFEwBTCore] assignements from defeq contained level mvar not in format: {repr mv}"
                    let D := difference indsU inds
                    if nope?
                    then
                      if empty? D
                      then cont R
                      else cont <| .cons D tn ln R
                    else
                      if empty? D
                      then cont <| .cons I ntn nln R
                      else cont <| .cons I ntn nln <| .cons D tn ln R
                  ) <| fun uni => do
                    let constr := uni.foldl empty (fun ds _ _ R =>
                      union ds R)
                    return (constr, uni)
              )
            mtrace on .zero with s!"[uniFEwBTCore] looking at sort {i}"
            mtrace on .zero with s!"[uniFEwBTCore] proceeding with constr {repr constr}"
            mtrace on .one with s!"[uniFEwBTCore] and uni {toString uni}"
            if empty? constr
            then if naive? then return ⟨0,constr, uni, l1,l2⟩ else return ⟨1,constr, uni, l1,l2⟩
            else return ⟨2,constr, uni, l1,l2⟩
          )
        (fun i bvs constr uni naive? l1 l2 => do
          mtrace on .two with s!"[uniFEwBTCore] uni {toString uni}"
          match bvs.find? (fun _ j => j == i) with
          | .none => if naive? then return ⟨0,constr, uni, l1,l2⟩ else return ⟨1,constr, uni, l1,l2⟩
          | .some inds _ =>
              let constr := intersect inds constr
              if empty? constr
              then if naive? then return ⟨0,constr, uni, l1,l2⟩ else return ⟨1,constr, uni, l1,l2⟩
              else
                let uni := uni.foldl .nil (fun is tn ln R =>
                  let I := intersect inds is
                  if empty? I
                  then R
                  else .cons I tn ln R
                  )
                return ⟨2,constr, uni, l1,l2⟩
          )
        -- consts affected
        (fun n l bvs constr uni naive? l1 l2 => do
            mtrace on .two with s!"[uniFEwBTCore] uni {toString uni}"
            mtrace on .zero with s!"[uniFEwBTCore] const case {n}"
            let na := n.toString.toUTF8
            match bvs.find? na with
            | .none => if naive? then return ⟨0,constr, uni, l1,l2⟩ else return ⟨1,constr, uni, l1,l2⟩
            | .some D => do
                let (constr, uni) ← D.foldlM (constr, uni) (fun inds lvI (constr, uni) => do
                  let mut l1 := l1
                  let mut l2 := l2
                  let mut lv := []
                  for LV in lvI do
                    let r ← mvarifyLTnodesIn LV l1 l2
                    l1 := r.2
                    l2 := r.3
                    lv := r.1 :: lv
                  lv := lv.reverse
                  mtrace on .zero with s!"[uniFEwBTCore] const defeq in context constr {constr} inds {inds} name {n} l {l} lv {lv}"
                  match ← defEqWiMv (.const n l) (.const n lv) l1 l2 with
                  | .none =>
                    mtrace on .zero with s!"[uniFEwBTCore] negative defeq"
                    let uni := uni.foldl ListProd3.nil (fun ds ts ls R =>
                      let ds := difference ds inds
                      if empty? ds
                      then R
                      else .cons ds ts ls R
                      )
                    let constr := difference constr inds
                    return (constr, uni)
                  | .some (Ls,_) =>
                    mtrace on .zero with s!"[uniFEwBTCore] positive"
                    mtrace on .zero with s!"[uniFEwBTCore] uni {toString uni}"
                    uni.foldlMcps (.nil : ListProd3 IdxCollType (ListProd3 Nat Nat Expr) (ListProd3 Nat Nat Level)) (fun indsU tn ln R cont => do
                      mtrace on .zero with s!"[uniFEwBTCore] tn {tn} ln {ln}"
                      let I := intersect inds indsU
                      mtrace on .zero with s!"[uniFEwBTCore] I {I}"
                      if empty? I
                      then cont R --<| .cons indsU tn ln R
                      else
                        let mut ntn := tn
                        let mut nln := ln
                        let mut nope? := false
                        for (mv,lv) in Ls do
                          match mv.name with
                          | .num (.num _ backIdx) pos =>
                              match ln.find? (fun x y _ => x == backIdx && y == pos) with
                              | .none =>
                                  nln := .cons backIdx pos lv nln
                              | .some _ _ al =>
                                  if ← (do let res ← isLevelDefEq al lv ; clearMvarAssignments ; return res)
                                  then
                                    continue
                                  else
                                    mtrace on .zero with s!"[uniFEwBTCore] non equivaent levels {al} {lv}"
                                    nope? := true
                                    break
                          | _ => panic s!"[uniFEwBTCore] assignements from defeq contained level mvar not in format: {repr mv}"
                        let D := difference indsU inds
                        mtrace on .zero with s!"[uniFEwBTCore] D {D}"
                        if nope?
                        then
                          cont R
                          -- if empty? D
                          -- then cont R
                          -- else cont <| .cons D tn ln R
                        else
                          cont <| .cons I ntn nln R
                      ) <| fun uni => do
                        let constr := uni.foldl empty (fun ds _ _ R =>
                          union ds R)
                        return (constr, uni)
                  )
                mtrace on .zero with s!"[uniFEwBTCore] looking at const {n} {l}"
                mtrace on .zero with s!"[uniFEwBTCore] proceeding with constr {repr constr}"
                mtrace on .one with s!"[uniFEwBTCore] and uni {toString uni}"
                if empty? constr
                then if naive? then return ⟨0,constr, uni, l1,l2⟩ else return ⟨1,constr, uni, l1,l2⟩
                else return ⟨2,constr, uni, l1,l2⟩
          )
        (fun _ _ _ _ _   _ _ _ _ _ _ =>
          throwError s!"[] we don't expect tnodes in forward term")
        (fun _ _ _ _ _ _ _ _ _ _ _ _ =>
          throwError s!"[] we don't expect lnodes in forward term")


@[specialize, inline]
partial def uniFEwBTMain
    [Repr IdxCollType] [ToString IdxCollType]
    (empty? : IdxCollType → Bool) (intersect union difference : IdxCollType → IdxCollType → IdxCollType) (empty : IdxCollType)
    (l1 : LocalContext) (l2 : LocalInstances)
    (constr : IdxCollType)
    (revCountMax : Nat)
    (E : Expr) (T : PaInG IdxCollType)
    : MetaM (Prod5 UInt8 IdxCollType (ListProd3 IdxCollType (ListProd3 Nat Nat Expr) (ListProd3 Nat Nat Level)) LocalContext LocalInstances) :=
    do
    clearMvarAssignments -- this is needed so that we may fold over assignement PHachMaps in ↓ and get new assignements only
    uniFEwBTCore empty? intersect union difference empty l1 l2 constr revCountMax E T

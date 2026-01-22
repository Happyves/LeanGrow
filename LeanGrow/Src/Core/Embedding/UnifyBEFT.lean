
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
def uniBEwFTrevert
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
  let built ← T.buildCore l1 l2 workas 0
    (fun inds => intersect inds constr)
    intersect empty?
  mtrace on .zero with s!"[uniBEwFTrevert] call on E {← ppExpr E}"
  mtrace on .zero with s!"[uniBEwFTrevert] with built {← ppPaInGHelp (← getLCtx) (← getLocalInstances) built}"
  mtrace on .zero with s!"[uniBEwFTrevert] and constr {repr constr}"
  mtrace on .one with s!"[uniBEwFTrevert] and uni {toString uni}"
  built.foldlMcps (empty, uni) (fun e inds (Sc,Su) cont => do
    match ← defEqWiMv E e l1 l2 with
    /- *Note* we expect mvars to not get assigned exprs containing workers, as the context
    of these mvars didn't contain them : this is desired, tnode assignements shouln't contain bvars.
    Since we use defeq as a blackbox and aren't sure of the above, we still check for workers
    is assignements below. -/
    | .none =>
        mtrace on .zero with s!"[uniBEwFTrevert] negative defeq of e {← ppExpr e} and E {← ppExpr E} for inds {repr inds}"
        let Su := Su.foldl ListProd3.nil (fun ds ts ls R =>
          let ds := difference ds inds
          if empty? ds
          then R
          else .cons ds ts ls R
          )
        let Sc := difference Sc inds
        cont (Sc, Su)
    | .some (La, Ta) => do
        mtrace on .zero with s!"[uniBEwFTrevert] positive defeq of e {← ppExpr e} and E {← ppExpr E} for inds {repr inds}"
        let mut broke? := false
        for (_,as) in Ta do
          if as.hasWorkerTR
          then
            broke? := true
            break
        if broke?
        then
          -- If defeq required assigning to expr containing workers, then treat it as a failure
          mtrace on .zero with s!"[uniBEwFTrevert] assigned workers, discarding"
          let Su := Su.foldl ListProd3.nil (fun ds ts ls R =>
            let ds := difference ds inds
            if empty? ds
            then R
            else .cons ds ts ls R
            )
          let Sc := difference Sc inds
          cont (Sc, Su)
        else
          let fst ← uniUpdateWrtMvars empty? intersect difference l1 l2 inds Ta Su
          mtrace on .one with s!"[uniBEwFTrevert] and fst {toString fst}"
          let Su ← uniUpdateWrtLevels empty? intersect difference inds La fst
          mtrace on .one with s!"[uniBEwFTrevert] and Su {toString Su}"
          let Sc := Su.foldl empty (fun ds _ _ R =>
            union ds R)
          cont (Sc, Su)
  ) <| fun (resI,resU) => do
    mtrace on .zero with s!"[uniBEwFTrevert] proceeding with constr {repr resI}"
    mtrace on .one with s!"[uniBEwFTrevert] and resU {toString resU}"
    if empty? resI
    then return ⟨false, resI, resU,l1,l2⟩
    else return ⟨true, resI, resU,l1,l2⟩


#check 1

@[specialize, inline]
partial def uniBEwFTCore
    [expl : Repr IdxCollType] [ToString IdxCollType]
    (empty? : IdxCollType → Bool) (intersect union difference : IdxCollType → IdxCollType → IdxCollType) (empty : IdxCollType)
    (l1 : LocalContext) (l2 : LocalInstances)
    (constr : IdxCollType)
    (revCountMax : Nat)
    (E : Expr) (T : PaInG IdxCollType)
    : MetaM (Prod5 UInt8 IdxCollType (ListProd3 IdxCollType (ListProd3 Nat Nat Expr) (ListProd3 Nat Nat Level)) LocalContext LocalInstances) := do
      mtracing
      let inittodo := .cons E T [] .nil
      @queryCore IdxCollType expl l1 l2 (ListProd3 IdxCollType (ListProd3 Nat Nat Expr) (ListProd3 Nat Nat Level))
        (uniUnion empty? intersect difference)
        empty? intersect union
        constr (.cons constr .nil .nil .nil)
        true true false false
        0 revCountMax
        .nil
        inittodo
        (fun E T workas constr uni l1 l2 => do
          mtrace on .zero with s!"[uniBEwFTCore] workas {repr workas}"
          uniBEwFTrevert empty?  intersect union difference empty l1 l2 E T workas constr uni)
        (fun _ _ _ constr uni l1 l2 => return ⟨constr, uni, l1,l2⟩)
        (fun _ _ _ constr uni l1 l2 => return ⟨constr, uni, l1,l2⟩)
        (fun _ _ _ _ api constr uni naive? l1 l2 =>
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
        (fun _ _ _ _ api constr uni naive? l1 l2 =>
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
        (fun _ _ _ _ api constr uni naive? l1 l2 =>
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
        (fun _ _ _ _ _ _ api constr uni naive? l1 l2 =>
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
        (fun n i e projs constr uni naive? l1 l2 =>
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
                    return ⟨2, .some e pT, constr, uni,l1,l2⟩
          )
        (fun i bvs constr uni naive? l1 l2 =>
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
        (fun i bvs constr uni naive? l1 l2 =>
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
        (fun i bvs constr uni naive? l1 l2 =>
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
          if i.hasMVar
          then
            match bvs with
            | .nil => if naive? then return ⟨0,constr, uni, l1,l2⟩ else return ⟨1,constr, uni, l1,l2⟩
            | _ =>
              let fix := bvs.foldl empty (fun x _ y => union x y)
              let constr := intersect constr fix
              let uni := uni.foldl ListProd3.nil (fun ds ef lu R =>
                let I := intersect ds fix
                if empty? I
                then R
                else .cons I ef lu R
                )
              let (constr, uni) ← bvs.foldlM (constr, uni) (fun inds lv (constr, uni) => do
                match ← defEqWiMv (.sort i) (.sort lv) l1 l2 with
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
                  let uni ← uniUpdateWrtLevels empty? intersect difference inds Ls uni
                  let constr := uni.foldl empty (fun ds _ _ R =>
                    union ds R)
                  return (constr, uni)
                )
              mtrace on .zero with s!"[uniBEwFTCore] looking at sort {i}"
              mtrace on .zero with s!"[uniBEwFTCore] proceeding with constr {repr constr}"
              mtrace on .one with s!"[uniBEwFTCore] and uni {toString uni}"
              if empty? constr
              then if naive? then return ⟨0,constr, uni, l1,l2⟩ else return ⟨1,constr, uni, l1,l2⟩
              else return ⟨2,constr, uni, l1,l2⟩
          else
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
        (fun i bvs constr uni naive? l1 l2 =>
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
        (fun n l bvs constr uni naive? l1 l2 =>
          if !(l.any Level.hasMVar)
          then
            match ListProd.find_PaInG_const bvs n l with
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
          else
            match bvs.find? n.toString.toUTF8 with
            | .none => if naive? then return ⟨0,constr, uni, l1,l2⟩ else return ⟨1,constr, uni, l1,l2⟩
            | .some D => do
                let fix := D.foldl empty (fun x _ y => union x y)
                let constr := intersect constr fix
                let uni := uni.foldl ListProd3.nil (fun ds ef lu R =>
                  let I := intersect ds fix
                  if empty? I
                  then R
                  else .cons I ef lu R
                  )
                let (constr, uni) ← D.foldlM (constr, uni) (fun inds lvls (constr, uni) => do
                  match ← defEqWiMv (.const n l) (.const n lvls) l1 l2 with
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
                    let uni ← uniUpdateWrtLevels empty? intersect difference inds Ls uni
                    let constr := uni.foldl empty (fun ds _ _ R =>
                      union ds R)
                    return (constr, uni)
                  )
                mtrace on .zero with s!"[uniBEwFTCore] looking at const {n} {l}"
                mtrace on .zero with s!"[uniBEwFTCore] proceeding with constr {repr constr}"
                mtrace on .one with s!"[uniBEwFTCore] and uni {toString uni}"
                if empty? constr
                then if naive? then return ⟨0,constr, uni, l1,l2⟩ else return ⟨1,constr, uni, l1,l2⟩
                else return ⟨2,constr, uni, l1,l2⟩
          )
        -- tnodes
        (fun n l _ workas T constr uni naive? l1 l2 => do
          let res ←  uniBEwFTrevert empty?  intersect union difference empty l1 l2 (.mvar ⟨tnode n l⟩) T
            workas constr uni --success (if naive? then nfail else rfail)
          match res with
          | .mk a b c d e => return (if a then (Prod5.mk 2 b c d e) else (if naive? then (.mk 0 b c d e) else (.mk 1 b c d e)))
          )

        (fun n i j _ _ _ _ _ _ _ _ =>
          throwError s!"[uniBEwFTCore] unexpected lnode {n} {i} {j}")



#check 1


@[specialize, inline]
partial def uniBEwFTMain
    [Repr IdxCollType] [ToString IdxCollType]
    (empty? : IdxCollType → Bool) (intersect union difference : IdxCollType → IdxCollType → IdxCollType) (empty : IdxCollType)
    (l1 : LocalContext) (l2 : LocalInstances)
    (constr : IdxCollType)
    (revCountMax : Nat)
    (E : Expr) (T : PaInG IdxCollType)
    : MetaM (Prod5 UInt8 IdxCollType (ListProd3 IdxCollType (ListProd3 Nat Nat Expr) (ListProd3 Nat Nat Level)) LocalContext LocalInstances) :=
    do
    clearMvarAssignments -- this is needed so that we may fold over assignement PHachMaps in ↓ and get new assignements only
    let ⟨E,l1,l2⟩ ← mvarifyTnodesRec E l1 l2
    uniBEwFTCore empty? intersect union difference empty l1 l2 constr revCountMax E T


#check 1

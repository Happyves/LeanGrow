
/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/


import LeanGrow.Src.Data.PathIndex.Query

open Lean Meta

variable {IdxCollType : Type _}

namespace PaIn
open PaIn

@[specialize, inline]
def findRevert
  (empty? : IdxCollType → Bool) (intersect union : IdxCollType → IdxCollType → IdxCollType) (empty : IdxCollType)
  : Expr → PaIn IdxCollType → List FVarId → IdxCollType → Unit → LocalContext → LocalInstances → MetaM (Prod5 Bool IdxCollType Unit LocalContext LocalInstances) :=
    fun E T workas constr uni l1 l2 => do
      mtracing
      let built := T.buildCore workas 0
        (fun inds => intersect inds constr)
        intersect empty?
      let pruned ← built.foldlM ListProd.nil (fun e inds S => do
        let e := e.instantiateLooseBvar workas
        return .cons e inds S
        )
      let constr ← pruned.foldlM empty (fun e inds S => do
        if (← defEqWiMv E e l1 l2).isSome
        then
          mtrace on .zero with s!"[findCore] positive defeq of e {← PpExpr e l1 l2} and E {← PpExpr E l1 l2}"
          return union inds S
        else
          mtrace on .zero with s!"[findCore] negative defeq of e {← PpExpr e l1 l2} and E {← PpExpr E l1 l2}"
          return S
        )
      if empty? constr
      then return ⟨false,constr,uni,l1,l2⟩  --fail constr uni
      else return ⟨true,constr,uni,l1,l2⟩ --success constr uni


@[specialize, inline]
partial def findCore [Repr IdxCollType]
    (l1 : LocalContext) (l2 : LocalInstances)
    (empty? : IdxCollType → Bool) (intersect union : IdxCollType → IdxCollType → IdxCollType) (empty : IdxCollType)
    (constr : IdxCollType)
    (revCountMax : Nat)
    (E : Expr) (T : PaIn IdxCollType)
    : MetaM (Prod5 UInt8 IdxCollType Unit LocalContext LocalInstances) :=
      let inittodo := .cons E T [] .nil
      queryCore l1 l2
        (fun x _ => x)
        empty? intersect union
        constr ()
        true true false false
        0 revCountMax
        .nil
        inittodo
        (findRevert empty? intersect union empty)
        (fun _ _ _ constr uni l1 l2 => return ⟨constr,uni,l1,l2⟩)
        (fun _ _ _ _ api constr uni naive? l1 l2 =>
          let constr := intersect api constr
          if empty? constr
          then if naive? then return ⟨0,constr,uni,l1,l2⟩ else return ⟨1,constr,uni,l1,l2⟩
          else return ⟨2,constr,uni,l1,l2⟩
          )
        (fun _ _ _ _ api constr uni naive? l1 l2 =>
          let constr := intersect api constr
          if empty? constr
          then if naive? then return ⟨0,constr,uni,l1,l2⟩ else return ⟨1,constr,uni,l1,l2⟩
          else return ⟨2,constr,uni,l1,l2⟩
          )
        (fun _ _ _ _ api constr uni naive? l1 l2 =>
          let constr := intersect api constr
          if empty? constr
          then if naive? then return ⟨0,constr,uni,l1,l2⟩ else return ⟨1,constr,uni,l1,l2⟩
          else return ⟨2,constr,uni,l1,l2⟩
          )
        (fun _ _ _ _ _ _ api constr uni naive? l1 l2 =>
          let constr := intersect api constr
          if empty? constr
          then if naive? then return ⟨0,constr,uni,l1,l2⟩ else return ⟨1,constr,uni,l1,l2⟩
          else return ⟨2,constr,uni,l1,l2⟩
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
                  else return ⟨2,.some e pT,constr,uni,l1,l2⟩
          )
        (fun i bvs constr uni naive? l1 l2 =>
          match bvs.find_pain_nat i with
          | .none => if naive? then return ⟨0,constr,uni,l1,l2⟩ else return ⟨1,constr,uni,l1,l2⟩
          | .some inds _ =>
              let constr := intersect inds constr
              if empty? constr
              then if naive? then return ⟨0,constr,uni,l1,l2⟩ else return ⟨1,constr,uni,l1,l2⟩
              else return ⟨2,constr,uni,l1,l2⟩
          )
        (fun i bvs constr uni naive? l1 l2 =>
          match bvs.find? i.name.toString.toUTF8 with
          | .none => if naive? then return ⟨0,constr,uni,l1,l2⟩ else return ⟨1,constr,uni,l1,l2⟩
          | .some inds =>
              let constr := intersect inds constr
              if empty? constr
              then if naive? then return ⟨0,constr,uni,l1,l2⟩ else return ⟨1,constr,uni,l1,l2⟩
              else return ⟨2,constr,uni,l1,l2⟩
          )
        (fun i bvs constr uni naive? l1 l2 =>
          match bvs.find? (fun _ j => j == i) with
          | .none => if naive? then return ⟨0,constr,uni,l1,l2⟩ else return ⟨1,constr,uni,l1,l2⟩
          | .some inds _ =>
              let constr := intersect inds constr
              if empty? constr
              then if naive? then return ⟨0,constr,uni,l1,l2⟩ else return ⟨1,constr,uni,l1,l2⟩
              else return ⟨2,constr,uni,l1,l2⟩
          )
        (fun i bvs constr uni naive? l1 l2 =>
          match bvs.find? (fun _ j => j == i) with
          | .none => if naive? then return ⟨0,constr,uni,l1,l2⟩ else return ⟨1,constr,uni,l1,l2⟩
          | .some inds _ =>
              let constr := intersect inds constr
              if empty? constr
              then if naive? then return ⟨0,constr,uni,l1,l2⟩ else return ⟨1,constr,uni,l1,l2⟩
              else return ⟨2,constr,uni,l1,l2⟩
          )
        (fun n l bvs constr uni naive? l1 l2 =>
          match ListProd.find_pain_const bvs n l with
          | .none => if naive? then return ⟨0,constr,uni,l1,l2⟩ else return ⟨1,constr,uni,l1,l2⟩
          | .some inds _ =>
              let constr := intersect inds constr
              if empty? constr
              then if naive? then return ⟨0,constr,uni,l1,l2⟩ else return ⟨1,constr,uni,l1,l2⟩
              else return ⟨2,constr,uni,l1,l2⟩
          )
        (fun i bvs _ _ constr uni naive? l1 l2 =>
          match bvs.find? i.name.toString.toUTF8 with
          | .none => if naive? then return ⟨0,constr,uni,l1,l2⟩ else return ⟨1,constr,uni,l1,l2⟩
          | .some inds =>
              let constr := intersect inds constr
              if empty? constr
              then if naive? then return ⟨0,constr,uni,l1,l2⟩ else return ⟨1,constr,uni,l1,l2⟩
              else return ⟨2,constr,uni,l1,l2⟩
          )




#check PaIn.buildAll
#check defEqWiMv
#check ListProd



def findS
    (l1 : LocalContext) (l2 : LocalInstances)
    (constr : UInt32Array)
    (revCountMax : Nat)
    (E : Expr) (T : PaIn UInt32Array)
    : MetaM (Prod5 UInt8 UInt32Array Unit LocalContext LocalInstances) :=
      findCore l1 l2 UInt32Array.isEmpty UInt32Array.inter UInt32Array.union .empty constr revCountMax E T

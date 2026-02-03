

/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import LeanGrow.Src.SampleGenScore.Gen.Types
import LeanGrow.Src.Data.PathIndex.Operations
import LeanGrow.Src.Data.PathIndex.Indexing
import LeanGrow.Src.Data.PathIndex.Query

open Lean Meta PaIn


variable {IdxCollType : Type _}

namespace PaIn



/-- Expects lnodes to have been loaded-/
@[specialize, inline]
def genQueryBackDefEqCore
  [Repr IdxCollType]
  (union : IdxCollType → IdxCollType → IdxCollType)
  (l1 : LocalContext) (l2 : LocalInstances)
  (E e : Expr) (inds : IdxCollType)
  (Sc : IdxCollType)
  : MetaM IdxCollType :=
  do
  mtracing
  match ← defEqWiMv E e l1 l2 with
  | .none =>
      mtrace on .zero with s!"[genQueryBackDefEqCore] negative defeq of e {← ppExpr e} and E {← ppExpr E}"
      return Sc
  | .some .. => do
        return (union inds Sc)


/-- Expects lnodes to have been loaded-/
@[specialize, inline]
def genQueryBackRevert
  [Repr IdxCollType] [ToString IdxCollType]
  (empty? : IdxCollType → Bool) (intersect union : IdxCollType → IdxCollType → IdxCollType)
  (empty : IdxCollType)
  (l1 : LocalContext) (l2 : LocalInstances)
  (E : Expr) (T : PaIn IdxCollType) (workas : List FVarId)
  (constr : IdxCollType)
  : MetaM (Bool × IdxCollType) :=
  do --trace set Tracing.Flags.none in do
  mtracing
  let built ← T.buildCore l1 l2 workas 0
    (fun inds => intersect inds constr)
    intersect empty?
  mtrace on .zero with s!"[genQueryBackRevert] call on E {← ppExpr E}"
  mtrace on .zero with s!"[genQueryBackRevert] with built {← ppPainHelp l1 l2 built}"
  mtrace on .zero with s!"[genQueryBackRevert] and constr {repr constr}"
  built.foldlMcps empty (fun e inds Sc cont => do
    cont <| ← genQueryBackDefEqCore union l1 l2 E e inds Sc
  ) <| fun resI => do
    mtrace on .zero with s!"[genQueryBackRevert] proceeding with constr {repr resI}"
    if empty? resI
    then return (false,resI)
    else return (true,resI)



/-- Expects lnodes to have been loaded-/
@[specialize, inline]
def genQueryLnodes [Inhabited IdxCollType]
  (empty? : IdxCollType → Bool) (intersect union : IdxCollType → IdxCollType → IdxCollType) (empty : IdxCollType)
  (l1 : LocalContext) (l2 : LocalInstances)
  (e : Expr) (lnodes : CTrie (IdxCollType))
  (constr : IdxCollType)
  : MetaM (IdxCollType × Bool) :=
    do --trace set Tracing.Flags.none in do
    mtracing
    mtrace on .zero with s!"[genQueryLnodes] call on e {← ppExpr e}"
    lnodes.foldMcps (empty, false) (fun mvname is (sI, match?) cont => do
          let I := intersect is constr
          if empty? I
          then cont (sI, match?)
          else
            let mv := Expr.mvar ⟨(String.fromUTF8! mvname).toName⟩
            mtrace on .zero with s!"[genQueryLnodes] looking at {mv} with mvaified type {← ppExpr <| ← inferType mv}"
            match ← defEqWiMv mv e l1 l2 with
            -- *Note* order matters ! The above order should make sure that its the lnode that gets assigned
            -- even if e contained mvarified tnodes
            | .none =>
                mtrace on .zero with s!"[genQueryLnodes] negative defeq"
                cont (sI, match?)
            | .some .. => do
                cont (union I sI, true)
      ) (fun (sI, match?) => return (sI, match?))

/-- Expects lnodes to have been loaded-/
@[specialize, inline]
def genQueryTnodes [ToString IdxCollType]
  (empty? : IdxCollType → Bool) (empty : IdxCollType) (intersect union : IdxCollType → IdxCollType → IdxCollType)
  (l1 : LocalContext) (l2 : LocalInstances)
  (mvn : MVarId)
  (workas: List FVarId) (T : PaIn IdxCollType)
  (constr : IdxCollType)
  (naive? : Bool)
  : MetaM (Prod4 UInt8 IdxCollType LocalContext LocalInstances) :=
  do
  mtracing
  let built ← T.buildCore l1 l2 workas 0
    (fun inds => intersect inds constr)
    intersect empty?
  let tn := Expr.mvar mvn
  mtrace on .zero with s!"[genQueryTnodes] built {toString built}"
  mtrace on .zero with s!"[genQueryTnodes] tnode {← ppExpr <| ← inferType tn}"
  built.foldlMcps empty (fun e inds sI k => do
    mtrace on .zero with s!"[genQueryTnodes] looking at e {← ppExpr e}"
    if e.hasMVar
    then
      mtrace on .zero with s!"[genQueryTnodes] has lnodes: skiped"
      k sI
    else
      match ← defEqWiMv e tn l1 l2 with
      | .none =>
        mtrace on .zero with s!"[genQueryTnodes] not defeq, skip"
        k sI
      | .some .. =>
        k (union inds sI)
    ) <| fun (constr) =>
      if empty? constr
      then (if naive? then return .mk 0 constr l1 l2 else return .mk 1 constr l1 l2)
      else return .mk 2 constr l1 l2





@[specialize]
partial def genQueryBackCore
    [expl : Repr IdxCollType] [ToString IdxCollType] [Inhabited IdxCollType]
    (empty? : IdxCollType → Bool) (intersect union : IdxCollType → IdxCollType → IdxCollType) (empty : IdxCollType)
    (l1 : LocalContext) (l2 : LocalInstances) (constr : IdxCollType)
    (revCountMax : Nat)
    (E : Expr) (T : PaIn IdxCollType)
    : MetaM (Prod5 UInt8 IdxCollType IdxCollType LocalContext LocalInstances) :=
      -- trace set Tracing.Flags.none in
      do
      mtracing
      let inittodo := .cons E T [] .nil
      @queryLCore IdxCollType expl l1 l2 IdxCollType
        union
        empty? intersect union
        constr constr
        true true false false
        0 revCountMax
        .nil
        inittodo
        (fun E T workas constr _ l1 l2 => do
          let (b,u) ←  genQueryBackRevert empty? intersect union empty l1 l2 E T workas constr
          return .mk b u u l1 l2)
        (fun e _ lnodes constr _ l1 l2 => do
            let (u,b) ← genQueryLnodes empty? intersect union empty l1 l2 e lnodes constr
            return .mk b u u l1 l2)
        (fun _ _ _ _ api constr uni naive? l1 l2 => do
          mtrace on .two with s!"[genQueryBackCore] uni {toString uni}"
          let constr := intersect api constr
          if empty? constr
          then if naive? then return .mk 0 constr constr l1 l2 else return  .mk 1 constr constr l1 l2
          else
            return  .mk 2 constr constr l1 l2
          )
        (fun _ _ _ _ api constr uni naive? l1 l2 => do
          mtrace on .two with s!"[genQueryBackCore] uni {toString uni}"
          let constr := intersect api constr
          if empty? constr
          then if naive? then return .mk 0 constr constr l1 l2 else return  .mk 1 constr constr l1 l2
          else
            return  .mk 2 constr constr l1 l2
          )
        (fun _ _ _ _ api constr uni naive? l1 l2 => do
          mtrace on .two with s!"[genQueryBackCore] uni {toString uni}"
          let constr := intersect api constr
          if empty? constr
          then if naive? then return .mk 0 constr constr l1 l2 else return  .mk 1 constr constr l1 l2
          else
            return  .mk 2 constr constr l1 l2
          )
        (fun _ _ _ _ _ _ api constr uni naive? l1 l2 => do
          mtrace on .two with s!"[genQueryBackCore] uni {toString uni}"
          let constr := intersect api constr
          if empty? constr
          then if naive? then return .mk 0 constr constr l1 l2 else return  .mk 1 constr constr l1 l2
          else
            return  .mk 2 constr constr l1 l2
          )
        (fun n i e projs constr uni naive? l1 l2 => do
          mtrace on .two with s!"[genQueryBackCore] uni {toString uni}"
          let nbt := n.toString.toUTF8
          match projs.find? nbt with
          | .none => if naive? then return .mk 0 .none constr constr l1 l2 else return  .mk 1 .none constr constr l1 l2
          | .some D =>
              match D.find? (fun _ (j, _) => j == i) with
              | .none => if naive? then return .mk 0 .none constr constr l1 l2 else return  .mk 1 .none constr constr l1 l2
              | .some inds (_,pT) =>
                  let constr := intersect constr inds
                  if empty? constr
                  then if naive? then return .mk 0 .none constr constr l1 l2 else return  .mk 1 .none constr constr l1 l2
                  else
                    return .mk 2 (.some e pT) constr constr l1 l2
          )
        (fun i bvs constr uni naive? l1 l2 => do
          mtrace on .two with s!"[genQueryBackCore] uni {toString uni}"
          match bvs.find_pain_nat i with
          | .none => if naive? then return .mk 0 constr constr l1 l2 else return  .mk 1 constr constr l1 l2
          | .some inds _ =>
              let constr := intersect inds constr
              if empty? constr
              then if naive? then return .mk 0 constr constr l1 l2 else return  .mk 1 constr constr l1 l2
              else
                return  .mk 2 constr constr l1 l2
          )
        (fun i bvs constr uni naive? l1 l2 => do
          mtrace on .two with s!"[genQueryBackCore] uni {toString uni}"
          match bvs.find? i.name.toString.toUTF8 with
          | .none => if naive? then return .mk 0 constr constr l1 l2 else return  .mk 1 constr constr l1 l2
          | .some inds =>
              let constr := intersect inds constr
              if empty? constr
              then if naive? then return .mk 0 constr constr l1 l2 else return  .mk 1 constr constr l1 l2
              else
                return  .mk 2 constr constr l1 l2
          )
        -- sorts affected
        (fun i bvs constr uni naive? l1 l2 => do
          mtrace on .two with s!"[genQueryBackCore] uni {toString uni}"
          mtrace on .zero with s!"[genQueryBackCore] sort case {i}"
          let (.mk constr l1 l2) ← bvs.foldlM (.mk empty l1 l2 : Prod3 _ _ _) (fun inds lv (.mk sI l1 l2) => do
            let I := intersect constr inds
            if empty? I
            then return .mk sI l1 l2
            else
              let lcase := lv.hasLnodes
              mtrace on .zero with s!"[genQueryBackCore] comparing to {lv} "
              let ⟨i,l1,l2⟩ ← (if lcase then return ⟨i,l1,l2⟩ else mvarifyLTnodesIn i l1 l2)
              match ← defEqWiMv (.sort i) (.sort lv) l1 l2 with
              | .none =>
                mtrace on .zero with s!"[genQueryBackCore] not defeq"
                return .mk sI l1 l2
              | .some .. =>
                mtrace on .zero with s!"[genQueryBackCore] defeq"
                return .mk (union I sI) l1 l2
            )
          mtrace on .zero with s!"[genQueryBackCore] looking at sort {i}"
          mtrace on .zero with s!"[genQueryBackCore] proceeding with constr {repr constr}"
          mtrace on .one with s!"[genQueryBackCore] and uni {toString uni}"
          if empty? constr
          then if naive? then return .mk 0 constr constr l1 l2 else return  .mk 1 constr constr l1 l2
          else return  .mk 2 constr constr l1 l2
          )
        (fun i bvs constr uni naive? l1 l2 => do
          mtrace on .two with s!"[genQueryBackCore] uni {toString uni}"
          match bvs.find? (fun _ j => j == i) with
          | .none => if naive? then return .mk 0 constr constr l1 l2 else return  .mk 1 constr constr l1 l2
          | .some inds _ =>
              let constr := intersect inds constr
              if empty? constr
              then if naive? then return .mk 0 constr constr l1 l2 else return  .mk 1 constr constr l1 l2
              else
                return  .mk 2 constr constr l1 l2
          )
        -- consts affected
        (fun n l bvs constr uni naive? l1 l2 => do
            mtrace on .two with s!"[genQueryBackCore] uni {toString uni}"
            mtrace on .zero with s!"[genQueryBackCore] const case {n} {l}"
            let na := n.toString.toUTF8
            match bvs.find? na with
            | .none => if naive? then return .mk 0 constr constr l1 l2 else return  .mk 1 constr constr l1 l2
            | .some D => do
                let (.mk constr l1 l2) ← D.foldlM (.mk empty l1 l2 : Prod3 _ _ _) (fun inds lvs (.mk sI l1 l2) => do
                  let I := intersect constr inds
                  if empty? I
                  then return .mk sI l1 l2
                  else
                    mtrace on .zero with s!"[genQueryBackCore] comparing to {lvs}"
                    let mut nope? := false
                    let mut l1 := l1
                    let mut l2 := l2
                    for i in l, lv in lvs do
                      let lcase := lv.hasLnodes
                      let ⟨i,ml1,ml2⟩ ← (if lcase then return ⟨i,l1,l2⟩ else mvarifyLTnodesIn i l1 l2)
                      l1 := ml1
                      l2 := ml2
                      mtrace on .zero with s!"[genQueryBackCore] comparing {Expr.sort i} and {Expr.sort lv}"
                      match ← defEqWiMv (.sort i) (.sort lv) l1 l2 with
                      | .none =>
                          mtrace on .zero with s!"[genQueryBackCore] non defeq"
                          nope? := true
                          break
                      | .some .. =>
                        mtrace on .zero with s!"[genQueryBackCore] defeq"
                        continue
                    if nope?
                    then
                      return .mk sI l1 l2
                    else
                      return .mk (union I sI) l1 l2
                  )
                mtrace on .zero with s!"[genQueryBackCore] looking at const {n} {l}"
                mtrace on .zero with s!"[genQueryBackCore] proceeding with constr {repr constr}"
                mtrace on .one with s!"[genQueryBackCore] and uni {toString uni}"
                if empty? constr
                then if naive? then return .mk 0 constr constr l1 l2 else return  .mk 1 constr constr l1 l2
                else return .mk 2 constr uni l1 l2
          )
        -- tnodes affected
        (fun mv _ workas T constr _ naive? l1 l2 => do
          let .mk k? u l1 l2 ←  genQueryTnodes
            empty? empty intersect union l1 l2 mv
            workas T constr naive?
          return .mk k? u u l1 l2
          )

#check 1


@[specialize, inline]
partial def genQueryBackWiLoadMain
    [Repr IdxCollType] [ToString IdxCollType] [Inhabited IdxCollType]
    (empty? : IdxCollType → Bool) (intersect union : IdxCollType → IdxCollType → IdxCollType) (empty : IdxCollType)
    (l1 : LocalContext) (l2 : LocalInstances)
    (constr : IdxCollType)
    (revCountMax : Nat)
    (E : Expr) (T : PaIn IdxCollType)
    (sampleName : Name) (types : Array Expr)
    : MetaM (Prod3 IdxCollType LocalContext LocalInstances) :=
    do
    let _ ← mkLevelMVarOfName (.num sampleName 0)
    let mut i := 0
    for T in types do
      let _ ← mkMvarStdNoCoI (.num sampleName i) T
      i := i+1
    let .mk yes? _ inds l1 l2 ← genQueryBackCore empty? intersect union empty l1 l2 constr revCountMax E T
    if yes? == 3
    then
      return .mk inds l1 l2
    else
      return .mk empty l1 l2

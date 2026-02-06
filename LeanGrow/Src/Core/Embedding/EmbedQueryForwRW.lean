
/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/


import LeanGrow.Src.Core.Embedding.EmbedQueryAPI
import LeanGrow.Src.Core.Embedding.EmbedRWAPI



open Lean Meta PaInG


variable {IdxCollType : Type _}

namespace PaInG

@[specialize, inline]
def embedForwRWDefEqCore
  (thmData : CTrie (Array ThmFormat))
  [Repr IdxCollType]
  (empty? : IdxCollType → Bool) (intersect union difference : IdxCollType → IdxCollType → IdxCollType)
  (empty : IdxCollType)
  (l1 : LocalContext) (l2 : LocalInstances)
  (E e : Expr) (extWorkas : List FVarId) (inds : IdxCollType)
  (Sc : IdxCollType) (Su : ListProd IdxCollType embedForwRWData)
  {β : Sort _} (cont : IdxCollType × ListProd IdxCollType embedForwRWData → MetaM β)
  : MetaM β :=
  do --trace set Tracing.Flags.none in do
  mtracing
  let load : MetaM Unit :=
    match getFirstLnodeDataFrom e with
    | .none => pure ()
    | .some (module, thmIdx) =>
        let moduleB := module.toString.toUTF8
        match thmData.find? moduleB with
        | .none => throwError s!"[embedForwRWDefEqCore] module {module} isn't in thmData"
        | .some thmDs =>
            let thmD := thmDs[thmIdx]!
            thmD.mctx.loadNoCo
  load
  match ← defEqWiMv E e l1 l2 with
  | .none =>
      mtrace on .zero with s!"[uniDefEqCore] negative defeq of e {← ppExpr e} and E {← ppExpr E}"
      let Su := Su.foldl ListProd.nil (fun ds ef R =>
        let ds := difference ds inds
        if empty? ds
        then R
        else .cons ds ef R
        )
      let Sc := difference Sc inds
      cont (Sc, Su)
  | .some (La, Ta) => do
      mtrace on .zero with s!"[uniDefEqCore] positive defeq of e {← ppExpr e} and E {← ppExpr E}"
      let mut broke? := false
      for (_,as) in Ta do
        if as.hasWorkerExcpet extWorkas
        then
          broke? := true
          break
      if broke?
      then
        -- If defeq required assigning to expr containing workers, then treat it as a failure
        let Su := Su.foldl ListProd.nil (fun ds ef R =>
          let ds := difference ds inds
          if empty? ds
          then R
          else .cons ds ef R
          )
        let Sc := difference Sc inds
        cont (Sc, Su)
      else
        let fst ← embedUpdateWrtMvarsNoT empty? intersect difference l1 l2 inds Ta Su
        let Su ← embedUpdateWrtLevelsNoT empty? intersect difference l1 l2 inds La fst
        let Sc := Su.foldl empty (fun ds _ R =>
          union ds R)
        cont (Sc, Su)



@[specialize, inline]
def embedForwRWRevert (thmData : CTrie (Array ThmFormat))
  [Repr IdxCollType] [ToString IdxCollType]
  (empty? : IdxCollType → Bool) (intersect union difference : IdxCollType → IdxCollType → IdxCollType)
  (empty : IdxCollType)
  (l1 : LocalContext) (l2 : LocalInstances)
  (E : Expr) (T : PaInG IdxCollType) (workas extWorkas : List FVarId)
  (constr : IdxCollType) (uni : ListProd IdxCollType embedForwRWData)
  : MetaM (Prod5 Bool IdxCollType (ListProd IdxCollType embedForwRWData) LocalContext LocalInstances) :=
  do --trace set Tracing.Flags.none in do
  mtracing
  let built ← T.buildMvarifyTnodesNoCo l1 l2 workas 0
    (fun inds => intersect inds constr)
    intersect empty?
  mtrace on .zero with s!"[embedForwRWRevert] call on E {← ppExpr E}"
  mtrace on .zero with s!"[embedForwRWRevert] with built {← ppPaInGHelp l1 l2 built}"
  mtrace on .zero with s!"[embedForwRWRevert] and constr {repr constr}"
  mtrace on .one with s!"[embedForwRWRevert] and uni {toString uni}"
  built.foldlMcps (empty, uni) (fun e inds (Sc,Su) cont => do
    embedForwRWDefEqCore thmData empty? intersect union difference empty l1 l2 E e extWorkas inds Sc Su cont
  ) <| fun (resI,resU) => do
    mtrace on .zero with s!"[embedForwRWRevert] proceeding with constr {repr constr}"
    mtrace on .one with s!"[embedForwRWRevert] and resU {toString resU}"
    if empty? resI
    then return ⟨false,resI,resU,l1,l2⟩
    else return ⟨true,resI,resU,l1,l2⟩

#check 1

-- #exit

@[specialize, inline]
def embedLnodesFRW [Inhabited IdxCollType] (thmData : CTrie (Array ThmFormat))
  (empty? : IdxCollType → Bool) (intersect union : IdxCollType → IdxCollType → IdxCollType) (empty : IdxCollType)
  (l1 : LocalContext) (l2 : LocalInstances)
  (e : Expr) (extWorkas : List FVarId) (lnodes : CTrie (ListProd IdxCollType (Nat × Nat)))
  (constr : IdxCollType) (uni : (ListProd IdxCollType embedForwRWData))
  : MetaM (Prod3 IdxCollType (ListProd IdxCollType embedForwRWData) Bool) :=
    do --trace set Tracing.Flags.none in do
    mtracing
    mtrace on .zero with s!"[embedLnodesFRW] call on e {← ppExpr e}"
    lnodes.foldMcps (⟨empty, .nil, false⟩ : Prod3 _ _ _) ( fun module D S cont => do
        D.foldlMcps S (fun is (thmIdx,pos) ⟨sI, sU, match?⟩ cont => do
          let I := intersect is constr
          if empty? I
          then cont ⟨sI, sU, match?⟩
          else
            match thmData.find? module with
            | .none => throwError s!"[embedLnodesFRW] module {String.fromUTF8! module} isn't in thmData"
            | .some thmDs =>
                let thmD := thmDs[thmIdx]!
                thmD.mctx.loadNoCo
                let mv := Expr.mvar ⟨lnode (String.fromUTF8! module).toName thmIdx pos ⟩
                mtrace on .zero with s!"[embedLnodesFRW] looking at {mv} with mvaified type {← ppExpr <| ← inferType mv}"
                match ← defEqWiMv mv e l1 l2 with
                -- *Note* order matters ! The above order should make sure that its the lnode that gets assigned
                -- even if e contained mvarified tnodes
                | .none =>
                    mtrace on .zero with s!"[embedLnodesFRW] negative defeq"
                    cont ⟨sI, sU, match?⟩
                | .some (La, Ta) => do
                    mtrace on .zero with s!"[embedLnodesFRW] positive defeq"
                    let mut broke? := false
                    for (mvtt,as) in Ta do
                      if as.hasWorkerExcpet extWorkas
                      then
                        mtrace on .zero with s!"[embedLnodesFRW] assigned woker at {repr mvtt} via {← ppExpr as}"
                        broke? := true
                        break
                    if broke?
                    then
                      cont ⟨sI, sU, match?⟩
                    else
                      uni.foldlMcps (⟨sI, sU, match?⟩ : Prod3 _ _ _) (fun inds ef ⟨sI, sU, match?⟩ cont => do
                        let II := intersect inds I
                        if empty? II
                        then cont ⟨sI, sU, match?⟩
                        else
                          let mut nope? := false
                          let mut res := ef
                          for (mv, lv) in La do
                            mtrace on .zero with s!"[embedLnodesFRW] looking at assignement {repr mv} with val {lv}"
                            match mv.name with
                            | .num (.num _ _) pos =>
                                match res.llv.find? (fun y _ => y == pos) with
                                | .none =>
                                    mtrace on .zero with s!"[embedLnodesFRW] new, adding it"
                                    res := {res with llv := (.cons pos lv res.llv)}
                                | .some _ al => do
                                    mtrace on .zero with s!"[embedLnodesFRW] comparing to existing { al}"
                                    match ← defEqWiMv (.sort al) (.sort lv) l1 l2 with
                                    | .none =>
                                        nope? := true
                                        break
                                    | .some .. =>
                                        continue
                            | _ => panic s!"[embedLnodesFRW] assignements from defeq contained level mvar not in format: {repr mv}"
                          if nope?
                          then
                            cont ⟨sI, sU, match?⟩
                          else
                            for (mv, lv) in Ta do
                              mtrace on .zero with s!"[embedLnodesFRW] looking at assignement {repr mv} with val {← ppExpr lv}"
                              match mv.name with
                              | .num (.num _ _) pos =>
                                  match res.ln.find? (fun y _ => y == pos) with
                                  | .none =>
                                      mtrace on .zero with s!"[embedLnodesFRW] new, adding it"
                                      res := {res with ln := (.cons pos lv res.ln)}
                                  | .some _ al => do
                                      mtrace on .zero with s!"[embedLnodesFRW] comparing to existing {← ppExpr al}"
                                      match ← defEqWiMv al lv l1 l2 with
                                      | .none =>
                                          nope? := true
                                          break
                                      | .some .. =>
                                          continue
                              | _ => panic s!"[embedLnodesFRW] assignements from defeq contained level mvar not in format: {repr mv}"
                            if nope?
                            then
                              cont ⟨sI, sU, match?⟩
                            else
                              let sI := union II sI
                              let sU := .cons II res sU
                              cont ⟨sI, sU, true⟩
                        )
                          <| fun ⟨sI, sU, match?⟩ => do
                          cont ⟨sI, sU, match?⟩)
                            <| fun ⟨sI, sU, match?⟩ => do
                              cont ⟨sI, sU, match?⟩
                        ) (fun ⟨sI, sU, match?⟩  => return ⟨sI, sU, match?⟩)


-- #exit

#check 1

@[specialize, inline]
partial def embedForwRWCore [Inhabited IdxCollType] (thmData : CTrie (Array ThmFormat))
    [expl : Repr IdxCollType] [ToString IdxCollType]
    (empty? : IdxCollType → Bool) (intersect union difference : IdxCollType → IdxCollType → IdxCollType) (empty : IdxCollType)
    (l1 : LocalContext) (l2 : LocalInstances)
    (constr : IdxCollType)
    (revCountMax : Nat) (extWorkas : List FVarId)
    (E : Expr) (T : PaInG IdxCollType)
    : MetaM (Prod5 UInt8 IdxCollType (ListProd IdxCollType embedForwRWData) LocalContext LocalInstances) := do
      trace set TracingFlags.none in
      do
      mtracing
      let inittodo := .cons E T [] .nil
      @queryLCoreWW IdxCollType expl l1 l2 (ListProd IdxCollType embedForwRWData)
        (fun x y => let res := embedUnionF empty? intersect difference x y
          trace on .two with s!"[embedForwRWCore] union res {toString res}" in res)
        empty? intersect union
        constr (.cons constr ⟨.nil, .nil⟩ .nil)
        true true false false
        0 revCountMax
        .nil
        inittodo
        (fun E T workas constr uni l1 l2 => do
          embedForwRWRevert thmData empty? intersect union difference empty l1 l2 E T workas extWorkas constr uni)
        (fun _ _ _ constr uni l1 l2 => do
            return ⟨false,constr,uni,l1,l2⟩)
        (fun _ _ e _ lnodes constr uni l1 l2 => do
            let ⟨constr,uni,bo⟩ ← embedLnodesFRW thmData empty? intersect union empty l1 l2 e extWorkas lnodes constr uni
            return ⟨bo,constr,uni,l1,l2⟩)
        (fun _ _ _ _ api constr uni naive? l1 l2 => do
          mtrace on .two with s!"[embedForwRWCore] uni {toString uni}"
          let constr := intersect api constr
          if empty? constr
          then if naive? then return ⟨0,constr,uni,l1,l2⟩ else return ⟨1,constr,uni,l1,l2⟩
          else
            let uni := uni.foldl .nil (fun is ef R =>
              let I := intersect api is
              if empty? I
              then R
              else .cons I ef R
              )
            return ⟨2,constr,uni,l1,l2⟩
          )
        (fun _ _ _ _ api constr uni naive? l1 l2 => do
          mtrace on .two with s!"[embedForwRWCore] uni {toString uni}"
          let constr := intersect api constr
          if empty? constr
          then if naive? then return ⟨0,constr,uni,l1,l2⟩ else return ⟨1,constr,uni,l1,l2⟩
          else
            let uni := uni.foldl .nil (fun is ef R =>
              let I := intersect api is
              if empty? I
              then R
              else .cons I ef R
              )
            return ⟨2,constr,uni,l1,l2⟩
          )
        (fun _ _ _ _ api constr uni naive? l1 l2 => do
          mtrace on .two with s!"[embedForwRWCore] uni {toString uni}"
          let constr := intersect api constr
          if empty? constr
          then if naive? then return ⟨0,constr,uni,l1,l2⟩ else return ⟨1,constr,uni,l1,l2⟩
          else
            let uni := uni.foldl .nil (fun is ef R =>
              let I := intersect api is
              if empty? I
              then R
              else .cons I ef R
              )
            return ⟨2,constr,uni,l1,l2⟩
          )
        (fun _ _ _ _ _ _ api constr uni naive? l1 l2 => do
          mtrace on .two with s!"[embedForwRWCore] uni {toString uni}"
          let constr := intersect api constr
          if empty? constr
          then if naive? then return ⟨0,constr,uni,l1,l2⟩ else return ⟨1,constr,uni,l1,l2⟩
          else
            let uni := uni.foldl .nil (fun is ef R =>
              let I := intersect api is
              if empty? I
              then R
              else .cons I ef R
              )
            return ⟨2,constr,uni,l1,l2⟩
          )
        (fun n i e projs constr uni naive? l1 l2 => do
          mtrace on .two with s!"[embedForwRWCore] uni {toString uni}"
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
                    let uni := uni.foldl .nil (fun is ef R =>
                      let I := intersect inds is
                      if empty? I
                      then R
                      else .cons I ef R
                      )
                    return ⟨0,.some e pT,constr,uni,l1,l2⟩
          )
        (fun i bvs constr uni naive? l1 l2 => do
          mtrace on .two with s!"[embedForwRWCore] uni {toString uni}"
          match bvs.find_PaInG_nat i with
          | .none => if naive? then return ⟨0,constr,uni,l1,l2⟩ else return ⟨1,constr,uni,l1,l2⟩
          | .some inds _ =>
              let constr := intersect inds constr
              if empty? constr
              then if naive? then return ⟨0,constr,uni,l1,l2⟩ else return ⟨1,constr,uni,l1,l2⟩
              else
                let uni := uni.foldl .nil (fun is ef R =>
                  let I := intersect inds is
                  if empty? I
                  then R
                  else .cons I ef R
                  )
                return ⟨2,constr,uni,l1,l2⟩
          )
        (fun i bvs constr uni naive? l1 l2 => do
          mtrace on .two with s!"[embedForwRWCore] uni {toString uni}"
          match bvs.find_PaInG_nat i with
          | .none => if naive? then return ⟨0,constr,uni,l1,l2⟩ else return ⟨1,constr,uni,l1,l2⟩
          | .some inds _ =>
              let constr := intersect inds constr
              if empty? constr
              then if naive? then return ⟨0,constr,uni,l1,l2⟩ else return ⟨1,constr,uni,l1,l2⟩
              else
                let uni := uni.foldl .nil (fun is ef R =>
                  let I := intersect inds is
                  if empty? I
                  then R
                  else .cons I ef R
                  )
                return ⟨2,constr,uni,l1,l2⟩
          )
        (fun i bvs constr uni naive? l1 l2 => do
          mtrace on .two with s!"[embedForwRWCore] uni {toString uni}"
          match bvs.find_PaInG_nat i with
          | .none => if naive? then return ⟨0,constr,uni,l1,l2⟩ else return ⟨1,constr,uni,l1,l2⟩
          | .some inds _ =>
              let constr := intersect inds constr
              if empty? constr
              then if naive? then return ⟨0,constr,uni,l1,l2⟩ else return ⟨1,constr,uni,l1,l2⟩
              else
                let uni := uni.foldl .nil (fun is ef R =>
                  let I := intersect inds is
                  if empty? I
                  then R
                  else .cons I ef R
                  )
                return ⟨2,constr,uni,l1,l2⟩
          )
        -- sorts affected
        (fun i bvs constr uni naive? l1 l2 => do
          mtrace on .two with s!"[embedForwRWCore] uni {toString uni}"
          mtrace on .zero with s!"[embedForwRWCore] sort case {i}"
          match bvs with
          | .nil => if naive? then return ⟨0,constr,uni,l1,l2⟩ else return ⟨1,constr,uni,l1,l2⟩
          | _ =>
            let fix := bvs.foldl empty (fun x _ y => union x y)
            let constr := intersect constr fix
            let uni := uni.foldl ListProd.nil (fun ds ef R =>
              let I := intersect ds fix
              if empty? I
              then R
              else .cons I ef R
              )
            let (constr, uni) ← bvs.foldlM (constr, uni) (fun inds lv (constr, uni) => do
              let lcase := lv.hasLnodes
              mtrace on .zero with s!"[embedForwRWCore] comparing to {lv} "
              let ⟨i,l1,l2⟩ ← (if lcase then return ⟨i,l1,l2⟩ else mvarifyLTnodesIn i l1 l2)
              match ← defEqWiMv (.sort i) (.sort lv) l1 l2 with
              | .none =>
                mtrace on .zero with s!"[embedForwRWCore] not defeq"
                let uni := uni.foldl ListProd.nil (fun ds ef R =>
                  let ds := difference ds inds
                  if empty? ds
                  then R
                  else .cons ds ef R
                  )
                let constr := difference constr inds
                return (constr, uni)
              | .some (Ls,_) =>
                mtrace on .zero with s!"[embedForwRWCore] defeq"
                if lcase
                then
                  let uni ← embedUpdateWrtLevelsNoT empty? intersect difference l1 l2 inds Ls uni
                  let constr := uni.foldl empty (fun ds _ R =>
                    union ds R)
                  return (constr, uni)
                else
                  return (constr, uni)
              )
            mtrace on .zero with s!"[embedForwRWCore] looking at sort {i}"
            mtrace on .zero with s!"[embedForwRWCore] proceeding with constr {repr constr}"
            mtrace on .one with s!"[embedForwRWCore] and uni {toString uni}"
            if empty? constr
            then if naive? then return ⟨0,constr,uni,l1,l2⟩ else return ⟨1,constr,uni,l1,l2⟩
            else return ⟨2,constr,uni,l1,l2⟩
          )
        (fun i bvs constr uni naive? l1 l2 => do
          mtrace on .two with s!"[embedForwRWCore] uni {toString uni}"
          match bvs.find? (fun _ j => j == i) with
          | .none => if naive? then return ⟨0,constr,uni,l1,l2⟩ else return ⟨1,constr,uni,l1,l2⟩
          | .some inds _ =>
              let constr := intersect inds constr
              if empty? constr
              then if naive? then return ⟨0,constr,uni,l1,l2⟩ else return ⟨1,constr,uni,l1,l2⟩
              else
                let uni := uni.foldl .nil (fun is ef R =>
                  let I := intersect inds is
                  if empty? I
                  then R
                  else .cons I ef R
                  )
                return ⟨2,constr,uni,l1,l2⟩
          )
        -- consts affected
        (fun n l bvs constr uni naive? l1 l2 => do
            mtrace on .two with s!"[embedForwRWCore] uni {toString uni}"
            mtrace on .zero with s!"[embedForwRWCore] const case {n} {l}"
            let na := n.toString.toUTF8
            match bvs.find? na with
            | .none => if naive? then return ⟨0,constr,uni,l1,l2⟩ else return ⟨1,constr,uni,l1,l2⟩
            | .some D => do
                let fix := D.foldl empty (fun x _ y => union x y)
                let constr := intersect constr fix
                let uni := uni.foldl ListProd.nil (fun ds ef R =>
                  let I := intersect ds fix
                  if empty? I
                  then R
                  else .cons I ef R
                  )
                let (constr, uni) ← D.foldlM (constr, uni) (fun inds lvs (constr, uni) => do
                  mtrace on .zero with s!"[embedForwRWCore] comparing to {lvs}"
                  let mut uni := uni
                  let mut nope? := false
                  let mut l1 := l1
                  let mut l2 := l2
                  for i in l, lv in lvs do
                    mtrace on .zero with s!"[embedForwRWCore] comparing {i} and {lv}"
                    let lcase := lv.hasLnodes
                    let ⟨i,l1',l2'⟩ ← (if lcase then return ⟨i,l1,l2⟩ else mvarifyLTnodesIn i l1 l2)
                    l1 := l1'
                    l2 := l2'
                    match ← defEqWiMv (.sort i) (.sort lv) l1 l2 with
                    | .none =>
                        mtrace on .zero with s!"[embedForwRWCore] non defeq"
                        nope? := true
                        break
                    | .some (Ls,_) =>
                      mtrace on .zero with s!"[embedForwRWCore] defeq"
                      if lcase
                      then
                        uni := ← embedUpdateWrtLevelsNoT empty? intersect difference l1 l2 inds Ls uni
                      else
                        continue
                  if nope?
                  then
                    let nuni := uni.foldl ListProd.nil (fun ds ef R =>
                        let ds := difference ds inds
                        if empty? ds
                        then R
                        else .cons ds ef R
                        )
                    let constr := difference constr inds
                    return (constr, nuni)
                  else
                    let constr := uni.foldl empty (fun ds _ R =>
                      union ds R)
                    return (constr, uni)
                  )
                mtrace on .zero with s!"[embedForwRWCore] looking at const {n} {l}"
                mtrace on .zero with s!"[embedForwRWCore] proceeding with constr {repr constr}"
                mtrace on .one with s!"[embedForwRWCore] and uni {toString uni}"
                if empty? constr
                then if naive? then return ⟨0,constr,uni,l1,l2⟩ else return ⟨1,constr,uni,l1,l2⟩
                else return ⟨2,constr,uni,l1,l2⟩
          )
        (fun _ _ _ _ _ _ _ _ _ _ _ _ =>
          throwError s!"[embedForwRWCore] we don't expect tnodes in forward term"
          )
        (fun _ _ _ _ _ _ _ _ _ _ _ _ =>
          throwError s!"[embedForwRWCore] we don't expect lnodes in forward term")
        extWorkas



#check 1


@[specialize]
partial def embedForwRWTop [Inhabited IdxCollType] (thmData : CTrie (Array ThmFormat))
    [Repr IdxCollType] [ToString IdxCollType]
    (empty? : IdxCollType → Bool) (intersect union difference : IdxCollType → IdxCollType → IdxCollType) (empty : IdxCollType)
    (l1 : LocalContext) (l2 : LocalInstances)
    (constr : IdxCollType)
    (revCountMax : Nat) (extWorkas : List FVarId)
    (E : Expr) (T : PaInG IdxCollType)
    : MetaM (Prod5 UInt8 IdxCollType (ListProd IdxCollType embedForwRWData) LocalContext LocalInstances) := do
    do
    clearMvarAssignments -- this is needed so that we may fold over assignement PHachMaps in ↓ and get new assignements only
    embedForwRWCore thmData empty? intersect union difference empty l1 l2 constr revCountMax extWorkas E T



@[specialize, inline]
def embedForwRWData.eq (l1 : LocalContext) (l2 : LocalInstances) (A B : embedForwRWData) : MetaM Bool := do
  A.llv.foldlMcps [] (fun i l s q =>
    match B.llv.find? (fun x _ => x == i) with
    | .none => return false
    | .some _ L => do
      if ← (do let res ← isLevelDefEq l L ; clearMvarAssignments ; return res)
      then q (i :: s)
      else return false
    ) <| fun s => do
      B.llv.foldlMcps () (fun j _ d q =>
        if s.contains j then q d else return false
        ) <| fun _ => do
          A.ln.foldlMcps [] (fun i l s q =>
            match B.ln.find? (fun x _ => x == i) with
            | .none => return false
            | .some _ L => do
              if ← defEqWiCommonWorker l1 l2 l L
              then q (i :: s)
              else return false
            ) <| fun s => do
              B.ln.foldlMcps () (fun j _ d q =>
                if s.contains j then q d else return false
                ) <| fun _ => do
                  return true

#check 1



@[specialize]
partial def embedForwRWMain [Inhabited IdxCollType]  [Repr IdxCollType] [ToString IdxCollType]
    (thmData : CTrie (Array ThmFormat))
    (empty? : IdxCollType → Bool) (intersect union difference : IdxCollType → IdxCollType → IdxCollType) (empty : IdxCollType)
    (fold : ∀ {β : Type _}, IdxCollType → (init : β) → (f : Nat → β → β) → β)
    (l1 : LocalContext) (l2 : LocalInstances) (sConstr locConstr: IdxCollType)
    (revCountMax : Nat) (extWorkas : List FVarId)
    (E : Expr) (T : PaInG IdxCollType)
    : MetaM (Prod4 IdxCollType (ListProd Nat (ListProd embedForwRWData rwDirs)) LocalContext LocalInstances) :=
    do --trace set Tracing.Flags.none in do
      let core (l1 : LocalContext) (l2 : LocalInstances)
        (here : ListProd IdxCollType embedForwRWData) (conHere : IdxCollType) := do
        match E with
        | .app f a =>
            let ⟨locConstr,resf,l1,l2⟩ ← embedForwRWMain thmData empty? intersect union difference empty fold l1 l2 sConstr locConstr revCountMax extWorkas f T
            let ⟨locConstr',resa,l1,l2⟩ ← embedForwRWMain thmData empty? intersect union difference empty fold l1 l2 sConstr locConstr revCountMax extWorkas a T
            let res ← mergeOccsTwo (fun x y => withLCtx l1 l2 do embedForwRWData.eq l1 l2 x y) .ap resf resa
            let res := mergeOnIndSpe
              (fun x y => x.foldl y (fun x y R => .cons x y R))
              (fun x => .cons x .yes .nil )
              res (listIndxSingleOut fold here)
            let locConstr := union conHere <| union locConstr locConstr'
            return ⟨locConstr,res,l1,l2⟩
        | .lam _ f a _ =>
              let w ← worker extWorkas.length
              let ⟨wfv,a,l1,l2⟩ ← withFreeing w f a l1 l2
              let ⟨cona,resa,l1,l2⟩ ← embedForwRWMain thmData empty? intersect union difference empty fold l1 l2 sConstr locConstr revCountMax (wfv :: extWorkas) a T
              let tmpConf := union locConstr cona
              let ⟨conf,resf,l1,l2⟩ ← embedForwRWMain thmData empty? intersect union difference empty fold l1 l2 tmpConf tmpConf revCountMax extWorkas f T
              let res ← mergeOccsTwo (fun x y => withReader (fun ctx => {ctx with lctx := l1, localInstances := l2}) do embedForwRWData.eq l1 l2 x y) .la resf resa
              let res := mergeOnIndSpe
                (fun x y => x.foldl y (fun x y R => .cons x y R))
                (fun x => .cons x .yes .nil )
                res (listIndxSingleOut fold here)
              let locConstr := union conHere <| union conf cona
              return ⟨locConstr,res,l1,l2⟩
        | .forallE _ f a _ =>
              let w ← worker extWorkas.length
              let ⟨wfv,a,l1,l2⟩ ← withFreeing w f a l1 l2
              let ⟨cona,resa,l1,l2⟩ ← embedForwRWMain thmData empty? intersect union difference empty fold l1 l2 sConstr locConstr revCountMax (wfv :: extWorkas) a T
              let tmpConf := union locConstr cona
              let ⟨conf,resf,l1,l2⟩ ← embedForwRWMain thmData empty? intersect union difference empty fold l1 l2 tmpConf tmpConf revCountMax extWorkas f T
              let res ← mergeOccsTwo (fun x y => withReader (fun ctx => {ctx with lctx := l1, localInstances := l2}) do embedForwRWData.eq l1 l2 x y) .al resf resa
              let res := mergeOnIndSpe
                (fun x y => x.foldl y (fun x y R => .cons x y R))
                (fun x => .cons x .yes .nil )
                res (listIndxSingleOut fold here)
              let locConstr := union conHere <| union conf cona
              return ⟨locConstr,res,l1,l2⟩
        | .letE _ f a z _ =>
              let w ← worker extWorkas.length
              let ⟨wfv,z,l1,l2⟩ ← withFreeingLet w f a z l1 l2
              let ⟨conz,resz,l1,l2⟩ ← embedForwRWMain thmData empty? intersect union difference empty fold l1 l2 sConstr locConstr revCountMax (wfv :: extWorkas) z T
              let tmpConf := union locConstr conz
              let ⟨conf,resf,l1,l2⟩ ← embedForwRWMain thmData empty? intersect union difference empty fold l1 l2 tmpConf tmpConf revCountMax extWorkas f T
              let ⟨cona,resa,l1,l2⟩ ← embedForwRWMain thmData empty? intersect union difference empty fold l1 l2 tmpConf tmpConf revCountMax extWorkas a T
              let res ← mergeOccsThree (fun x y => withReader (fun ctx => {ctx with lctx := l1, localInstances := l2}) do embedForwRWData.eq l1 l2 x y) resf resa resz
              let res := mergeOnIndSpe
                (fun x y => x.foldl y (fun x y R => .cons x y R))
                (fun x => .cons x .yes .nil )
                res (listIndxSingleOut fold here)
              let locConstr := union conHere <| union (union conf cona) conz
              return ⟨locConstr,res,l1,l2⟩
        | .proj stru i maj =>
              -- let real ← mkProjFn! l1 l2 stru i maj
              -- embedForwRWMain thmData empty? intersect union difference empty fold l1 l2 sConstr locConstr revCountMax extWorkas real T
              -- not needed for rw ?
              let ⟨con, resf,l1,l2⟩ ← embedForwRWMain thmData empty? intersect union difference empty fold l1 l2 sConstr locConstr revCountMax extWorkas maj T
              let res := resf.foldl .nil (fun n l R => let fix := l.foldl .nil (fun e d R => .cons e (.pro d) R) ; .cons n fix R)
              let res := mergeOnIndSpe
                (fun x y => x.foldl y (fun x y R => .cons x y R))
                (fun x => .cons x .yes .nil )
                res (listIndxSingleOut fold here)
              let locConstr := union con conHere
              return ⟨locConstr,res,l1,l2⟩
        | .mdata _ f =>
            embedForwRWMain thmData empty? intersect union difference empty fold l1 l2 sConstr locConstr revCountMax extWorkas f T
        | _ =>
          let res := mergeOnIndSpe
                (fun x y => x.foldl y (fun x y R => .cons x y R))
                (fun x => .cons x .yes .nil )
                .nil (listIndxSingleOut fold here)
          return ⟨conHere,res,l1,l2⟩
      mtracing
      mtrace on .zero with s!" looking at {← PpExpr E l1 l2}"
      if ← IsProof E l1 l2
      then
        mtrace on .zero with s!" proof, skipping"
        return .mk empty .nil l1 l2
      else
        let ⟨yes?,conHere,here,l1,l2⟩ ← embedForwRWTop thmData empty? intersect union difference empty l1 l2 sConstr revCountMax extWorkas E T
        mtrace on .zero with s!" found : {yes? == 3}\nIndices {conHere}\nEmbeddings: {here}"
        if yes? == 3
        then core l1 l2 here conHere
        else core l1 l2 .nil empty

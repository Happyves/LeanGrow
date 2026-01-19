
/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/


import LeanGrow.Src.Core.Embedding.EmbedQueryAPI

open Lean Meta PaInG


variable {IdxCollType : Type _}

namespace PaInG


@[specialize, inline]
def embedBackDefEqCore
  (l1 : LocalContext) (l2 : LocalInstances)
  (thmData : CTrie (Array ThmFormat))
  [Repr IdxCollType]
  (empty? : IdxCollType → Bool) (intersect union difference : IdxCollType → IdxCollType → IdxCollType)
  (empty : IdxCollType)
  (E e : Expr) (extWorkas : List FVarId) (inds : IdxCollType)
  (Sc : IdxCollType) (Su : ListProd IdxCollType embedBackData)
  : MetaM (IdxCollType × ListProd IdxCollType embedBackData) := do
  mtracing
  -- trace set Tracing.Flags.none in do
  let rec load : MetaM Unit := do
    mtrace on .zero with s!"[embedBackDefEqCore] looking at e {← ppExpr e}"
    match getFirstLnodeDataFrom e with
    | .none => pure ()
    | .some (module, thmIdx) =>
        mtrace on .zero with s!"[embedBackDefEqCore] getFirstLnodeDataFrom found module {module} and thmIdx {thmIdx}"
        let moduleB := module.toString.toUTF8
        match thmData.find? moduleB with
        | .none => throwError s!"[embedBackDefEqCore] module {module} isn't in thmData"
        | .some thmDs =>
            let thmD := thmDs[thmIdx]!
            thmD.mctx.loadNoCo
  load
  match ← defEqWiMv E e l1 l2 with
  | .none =>
      mtrace on .zero with s!"[embedBackDefEqCore] negative defeq of e {← ppExpr e} and E {← ppExpr E}"
      let Su := Su.foldl ListProd.nil (fun ds ef R =>
        let ds := difference ds inds
        if empty? ds
        then R
        else .cons ds ef R
        )
      let Sc := difference Sc inds
      return (Sc, Su)
  | .some (La, Ta) => do
      mtrace on .zero with s!"[embedBackDefEqCore] positive defeq of e {← ppExpr e} and E {← ppExpr E}"
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
        return (Sc, Su)
      else
        let fst ← embedUpdateWrtMvars empty? intersect difference l1 l2 inds Ta Su
        let Su ← embedUpdateWrtLevels empty? intersect difference l1 l2 inds La fst
        let Sc := Su.foldl empty (fun ds _ R =>
          union ds R)
        return (Sc, Su)


@[specialize, inline]
def embedBackRevert (thmData : CTrie (Array ThmFormat))
  [Repr IdxCollType] [ToString IdxCollType]
  (empty? : IdxCollType → Bool) (intersect union difference : IdxCollType → IdxCollType → IdxCollType)
  (empty : IdxCollType)
  (l1 : LocalContext) (l2 : LocalInstances)
  (E : Expr) (T : PaInG IdxCollType) (workas extWorkas : List FVarId)
  (constr : IdxCollType) (uni : ListProd IdxCollType embedBackData)
  : MetaM (Prod5 Bool IdxCollType (ListProd IdxCollType embedBackData) LocalContext LocalInstances) :=
  -- trace set Tracing.Flags.none in do
  do
  mtracing
  mtrace on .zero with s!"[embedBackRevert] call on E {← ppExpr E}"
  let built ← T.buildMvarifyTnodesNoCo l1 l2 workas 0
    (fun inds => intersect inds constr)
    intersect empty?
  mtrace on .zero with s!"[embedBackRevert] with built {← ppPaInGHelp l1 l2 built}"
  mtrace on .zero with s!"[embedBackRevert] and constr {repr constr}"
  mtrace on .one with s!"[embedBackRevert] and uni {toString uni}"
  let (resI,resU) ← built.foldlM (empty, uni) (fun e inds (Sc,Su) => do
    embedBackDefEqCore l1 l2 thmData empty? intersect union difference empty E e extWorkas inds Sc Su)
  mtrace on .zero with s!"[embedBackRevert] proceeding with constr {repr resI}"
  mtrace on .one with s!"[embedBackRevert] and resU {toString resU}"
  if empty? resI
  then return ⟨false, resI, resU,l1,l2⟩
    else return ⟨true, resI, resU,l1,l2⟩



@[specialize]
def embedLnodes [ToString IdxCollType] (thmData : CTrie (Array ThmFormat))
  (empty? : IdxCollType → Bool) (intersect union : IdxCollType → IdxCollType → IdxCollType) (empty : IdxCollType)
  (l1 : LocalContext) (l2 : LocalInstances)
  (e : Expr) (extWorkas : List FVarId) (lnodes : CTrie (ListProd IdxCollType (Nat × Nat)))
  (constr : IdxCollType) (uni : (ListProd IdxCollType embedBackData))
  : MetaM (Prod5 Bool IdxCollType (ListProd IdxCollType embedBackData) LocalContext LocalInstances) :=
  withReader (fun ctx => {ctx with lctx := l1, localInstances := l2}) do
    mtracing
    -- trace set Tracing.Flags.none in do
    mtrace on .zero with s!"[embedLnodes] call on e {← ppExpr e}"
    lnodes.foldM ⟨false,empty,.nil,l1,l2⟩ (fun module D S => do
      D.foldlM S (fun is (thmIdx,pos) ⟨ match?,sI, sU,l1,l2⟩ => do
          let I := intersect is constr
          if empty? I
          then return ⟨ match?,sI, sU,l1,l2⟩
          else
            match thmData.find? module with
            | .none => throwError s!"[embedLnodes] module {String.fromUTF8! module} isn't in thmData"
            | .some thmDs =>
                let thmD := thmDs[thmIdx]!
                thmD.mctx.loadNoCo
                let mv := Expr.mvar ⟨lnode (String.fromUTF8! module).toName thmIdx pos ⟩
                mtrace on .zero with s!"[embedLnodes] looking at {mv} with mvaified type {← ppExpr <| ← inferType mv}"
                match ← defEqWiMv mv e l1 l2 with
                -- *Note* order matters ! The above order should make sure that its the lnode that gets assigned
                -- even if e contained mvarified tnodes
                | .none =>
                    mtrace on .zero with s!"[embedLnodes] negative defeq"
                    return ⟨ match?,sI, sU,l1,l2⟩
                | .some (La, Ta) => do
                    mtrace on .zero with s!"[embedLnodes] positive defeq"
                    let mut broke? := false
                    for (mvtt,as) in Ta do
                      if as.hasWorkerExcpet extWorkas
                      then
                        mtrace on .zero with s!"[embedLnodes] assigned woker at {repr mvtt} via {← ppExpr as}"
                        broke? := true
                        break
                    if broke?
                    then
                      return ⟨ match?,sI, sU,l1,l2⟩
                    else
                      uni.foldlM ⟨ match?,sI, sU,l1,l2⟩ (fun inds ef ⟨ match?,sI, sU,l1,l2⟩ => do
                        let II := intersect inds I
                        if empty? II
                        then return ⟨ match?,sI, sU,l1,l2⟩
                        else
                          let mut nope? := false
                          let mut res := ef
                          let mut l1 := l1
                          let mut l2 := l2
                          for (mv, lv) in La do
                            mtrace on .zero with s!"[embedLnodes] looking at assignement {repr mv} with val {lv}"
                            match mv.name with
                            | .num (.num _ _) pos =>
                                match res.llv.find? (fun y _ => y == pos) with
                                | .none =>
                                    mtrace on .zero with s!"[embedLnodes] new, adding it"
                                    res := {res with llv := (.cons pos lv res.llv)}
                                | .some _ al => do
                                    mtrace on .zero with s!"[embedLnodes] comparing to existing { al}"
                                    if lv.hasTnodes
                                    then
                                      if al.hasTnodes
                                      then
                                        nope? := true
                                        break
                                      else
                                        let ⟨lv,l1',l2'⟩ ← mvarifyLTnodesIn lv l1 l2
                                        l1 := l1'
                                        l2 := l2'
                                        match ← defEqWiMv (.sort al) (.sort lv) l1 l2 with
                                        | .none =>
                                            nope? := true
                                            break
                                        | .some (La, Ta) =>
                                            match ← embedPropagateAsTnodes l1 l2 res La Ta with
                                            | .some r =>
                                                res := r
                                            | .none =>
                                                nope? := true
                                                break
                                    else
                                      let ⟨al,l1',l2'⟩ ← mvarifyLTnodesIn al l1 l2
                                      l1 := l1'
                                      l2 := l2'
                                      match ← defEqWiMv  (.sort al) (.sort lv) l1 l2 with
                                      | .none =>
                                          nope? := true
                                          break
                                      | .some (La, Ta) =>
                                          match ← embedPropagateAsTnodes l1 l2 res La Ta with
                                          | .some r =>
                                              res := r
                                          | .none =>
                                              nope? := true
                                              break
                            | _ => panic s!"[embedLnodes] assignements from defeq contained level mvar not in format: {repr mv}"
                          if nope?
                          then
                            return ⟨ match?,sI, sU,l1,l2⟩
                          else
                            for (mv, lv) in Ta do
                              mtrace on .zero with s!"[embedLnodes] looking at assignement {repr mv} with val {← ppExpr lv}"
                              match mv.name with
                              | .num (.num _ _) pos =>
                                  match res.ln.find? (fun y _ => y == pos) with
                                  | .none =>
                                      mtrace on .zero with s!"[embedLnodes] new, adding it"
                                      res := {res with ln := (.cons pos lv res.ln)}
                                  | .some _ al => do
                                      mtrace on .zero with s!"[embedLnodes] comparing to existing {← ppExpr al}"
                                      if lv.hasTnodes
                                      then
                                        if al.hasTnodes
                                        then
                                          nope? := true
                                          break
                                        else
                                          let ⟨lv,l1',l2'⟩ ← mvarifyTnodesRec lv l1 l2
                                          l1 := l1'
                                          l2 := l2'
                                          match ← defEqWiMv al lv l1 l2 with
                                          | .none =>
                                              nope? := true
                                              break
                                          | .some (La, Ta) =>
                                              match ← embedPropagateAsTnodes l1 l2 res La Ta with
                                              | .some r =>
                                                  res := r
                                              | .none =>
                                                  nope? := true
                                                  break
                                      else
                                        let ⟨al,l1',l2'⟩ ← mvarifyTnodesRec al l1 l2
                                        l1 := l1'
                                        l2 := l2'
                                        match ← defEqWiMv al lv l1 l2 with
                                        | .none =>
                                            nope? := true
                                            break
                                        | .some (La, Ta) =>
                                            match ← embedPropagateAsTnodes l1 l2 res La Ta with
                                            | .some r =>
                                                res := r
                                            | .none =>
                                                nope? := true
                                                break
                              | _ => panic s!"[embedLnodes] assignements from defeq contained level mvar not in format: {repr mv}"
                            if nope?
                            then
                              return ⟨ match?,sI, sU,l1,l2⟩
                            else
                              let sI := union II sI
                              let sU := .cons II res sU
                              return ⟨true,sI, sU,l1,l2⟩
                        )
                          )

                        )






@[specialize, inline]
def embedTnodes [ToString IdxCollType]
  (empty? : IdxCollType → Bool) (intersect difference : IdxCollType → IdxCollType → IdxCollType)
  (l1 : LocalContext) (l2 : LocalInstances)
  (backIdx : Nat) (pos : Nat)
  (workas extWorkas: List FVarId) (T : PaInG IdxCollType)
  (constr : IdxCollType) (uni : (ListProd IdxCollType embedBackData))
  (naive? : Bool)
  : MetaM (Prod5 UInt8 IdxCollType (ListProd IdxCollType embedBackData) LocalContext LocalInstances) := do
  mtracing
  -- trace set Tracing.Flags.none in do
  let built ← T.buildMvarifyTnodesNoCo l1 l2 workas 0
    (fun inds => intersect inds constr)
    intersect empty?
  let ⟨tn,l1,l2⟩ ← mvarifyTnodesRec (.fvar ⟨.num (.num `t backIdx) pos⟩) l1 l2
  withReader (fun ctx => {ctx with lctx := l1, localInstances := l2}) do
  mtrace on .zero with s!"[embedTnodes] built {toString built}"
  mtrace on .zero with s!"[embedTnodes] tnode {backIdx} {pos} {← ppExpr <| ← inferType tn}"
  built.foldlMcps (constr,uni) (fun e inds (constr,uni) k => do
    mtrace on .zero with s!"[embedTnodes] looking at e {← ppExpr e}"
    if e.hasLnodes
    then
      mtrace on .zero with s!"[embedTnodes] has lnodes: skiped"
      let uni := uni.foldl ListProd.nil (fun ds ef R =>
        let ds := difference ds inds
        if empty? ds
        then R
        else .cons ds ef R
        )
      let constr := difference constr inds
      k (constr, uni)
    else
      match ← defEqWiMv e tn l1 l2 with
      | .none =>
        mtrace on .zero with s!"[embedTnodes] not defeq, skip"
        let uni := uni.foldl ListProd.nil (fun ds ef R =>
          let ds := difference ds inds
          if empty? ds
          then R
          else .cons ds ef R
          )
        let constr := difference constr inds
        k (constr, uni)
      | .some (La,Ta) =>
        let mut broke? := false
        for (mvtt,as) in Ta do
          if as.hasWorkerExcpet extWorkas
          then
            mtrace on .zero with s!"[embedTnodes] assigned woker at {repr mvtt} via {← ppExpr as}"
            broke? := true
            break
        if broke?
        then
          k (constr,uni)
        else
          mtrace on .zero with s!"[embedTnodes] positive defeq, proceeding"
          uni.foldlMcps (constr, (.nil : ListProd IdxCollType embedBackData)) (fun ds ef (constr, R) q => do
            let I := intersect inds ds
            if empty? I
            then q (constr, .cons ds ef R)
            else
              match ← embedPropagateAsTnodes l1 l2 ef La Ta with
              | .none =>
                  mtrace on .zero with s!"[embedTnodes] tnode propa failed"
                  let constr := difference constr I
                  let D := difference ds inds
                  if empty? D
                  then q (constr, R)
                  else q (constr, .cons D ef R)
              | .some nef =>
                  mtrace on .zero with s!"[embedTnodes] tnode propa succeeded"
                  let D := difference ds inds
                  if empty? D
                  then q (constr, .cons I nef R)
                  else q (constr, .cons D ef <| .cons I nef R)
            ) k
    ) <| fun (constr,uni) => do
      mtrace on .zero with s!"[embedTnodes] done with uni {toString uni}, continuation"
      if empty? constr
      then (if naive? then return ⟨0, constr, uni,l1,l2⟩ else return ⟨1, constr, uni,l1,l2⟩)
      else return ⟨2, constr, uni,l1,l2⟩


@[specialize]
partial def embedBackCore (thmData : CTrie (Array ThmFormat))
    [expl : Repr IdxCollType] [ToString IdxCollType]
    (empty? : IdxCollType → Bool) (intersect union difference : IdxCollType → IdxCollType → IdxCollType) (empty : IdxCollType)
    (l1 : LocalContext) (l2 : LocalInstances)
    (constr : IdxCollType)
    (revCountMax : Nat) (extWorkas : List FVarId)
    (E : Expr) (T : PaInG IdxCollType)
    : MetaM (Prod5 UInt8 IdxCollType (ListProd IdxCollType embedBackData) LocalContext LocalInstances) := do
      trace set TracingFlags.none in
      do
      mtracing
      let inittodo := .cons E T [] .nil
      @queryLCore IdxCollType expl l1 l2 (ListProd IdxCollType embedBackData)
        (fun x y => let res := embedUnion empty? intersect difference x y
          trace on .two with s!"[embedBackCore] union res {toString res}" in res)
        empty? intersect union
        constr (.cons constr ⟨.nil, .nil, .nil, .nil⟩ .nil)
        true true false false
        0 revCountMax
        .nil
        inittodo
        (fun E T workas constr uni l1 l2 => do
          embedBackRevert thmData empty? intersect union difference empty l1 l2 E T workas extWorkas constr uni)
        (fun _ _ _ constr uni l1 l2 => do
            return ⟨false,constr,uni,l1,l2⟩)
        (fun _ _ e _ lnodes constr uni l1 l2 =>
            embedLnodes thmData empty? intersect union empty l1 l2 e extWorkas lnodes constr uni
            )
        (fun _ _ _ _ api constr uni naive? l1 l2 => do
          mtrace on .two with s!"[embedBackCore] uni {toString uni}"
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
          mtrace on .two with s!"[embedBackCore] uni {toString uni}"
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
          mtrace on .two with s!"[embedBackCore] uni {toString uni}"
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
          mtrace on .two with s!"[embedBackCore] uni {toString uni}"
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
          mtrace on .two with s!"[embedBackCore] uni {toString uni}"
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
                    return ⟨2,.some e pT,constr,uni,l1,l2⟩
          )
        (fun i bvs constr uni naive? l1 l2 => do
          mtrace on .two with s!"[embedBackCore] uni {toString uni}"
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
          mtrace on .two with s!"[embedBackCore] uni {toString uni}"
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
          mtrace on .two with s!"[embedBackCore] uni {toString uni}"
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
          mtrace on .two with s!"[embedBackCore] uni {toString uni}"
          mtrace on .zero with s!"[embedBackCore] sort case {i}"
          match bvs with
          | .nil => if naive? then return ⟨0,constr,uni,l1,l2⟩ else return ⟨1,constr,uni,l1,l2⟩
          | _ =>
              let .mk constr uni l1 l2 ← bvs.foldlM (.mk constr uni l1 l2 : Prod4 _ _ _ _) (fun inds lv (.mk constr uni l1 l2) => do
                let lcase := lv.hasLnodes
                mtrace on .zero with s!"[embedBackCore] comparing to {lv} "
                let ⟨i,l1,l2⟩ ← (if lcase then return ⟨i,l1,l2⟩ else mvarifyLTnodesIn i l1 l2)
                let load : MetaM Unit :=
                  match getFirstLnodeDataFrom (.sort lv) with
                  | .none => pure ()
                  | .some (module, thmIdx) =>
                      let moduleB := module.toString.toUTF8
                      match thmData.find? moduleB with
                      | .none => throwError s!"[embedBackDefEqCore] module {module} isn't in thmData"
                      | .some thmDs =>
                          let thmD := thmDs[thmIdx]!
                          thmD.mctx.loadNoCo
                load
                match ← defEqWiMv (.sort i) (.sort lv) l1 l2 with
                | .none =>
                  mtrace on .zero with s!"[embedBackCore] not defeq"
                  let uni := uni.foldl ListProd.nil (fun ds ef R =>
                    let ds := difference ds inds
                    if empty? ds
                    then R
                    else .cons ds ef R
                    )
                  let constr := difference constr inds
                  return .mk constr uni l1 l2
                | .some (Ls,_) =>
                  mtrace on .zero with s!"[embedBackCore] defeq"
                  if lcase
                  then
                    let uni ← embedUpdateWrtLevels empty? intersect difference l1 l2 inds Ls uni
                    let constr := uni.foldl empty (fun ds _ R =>
                      union ds R)
                    return .mk constr uni l1 l2
                  else
                    let uni ← uni.foldlM ListProd.nil (fun ds ef R => do
                      let I := intersect ds inds
                      if empty? I
                      then return .cons ds ef R
                      else
                        let D := difference ds inds
                        let pre (R) :=
                          (if empty? D then R else .cons D ef R)
                        match ← embedPropagateAsTnodes l1 l2 ef Ls {} with
                        | .none => return pre R
                        | .some nef => return pre <| .cons I nef R
                      )
                    let constr := uni.foldl empty (fun ds _ R =>
                      union ds R)
                    return .mk constr uni l1 l2
                )
              mtrace on .zero with s!"[embedBackCore] looking at sort {i}"
              mtrace on .zero with s!"[embedBackCore] proceeding with constr {repr constr}"
              mtrace on .one with s!"[embedBackCore] and uni {toString uni}"
              if empty? constr
              then if naive? then return ⟨0,constr,uni,l1,l2⟩ else return ⟨1,constr,uni,l1,l2⟩
              else return ⟨2,constr,uni,l1,l2⟩
          )
        (fun i bvs constr uni naive? l1 l2 => do
          mtrace on .two with s!"[embedBackCore] uni {toString uni}"
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
            mtrace on .two with s!"[embedBackCore] uni {toString uni}"
            mtrace on .zero with s!"[embedBackCore] const case {n} {l}"
            let na := n.toString.toUTF8
            match bvs.find? na with
            | .none => if naive? then return ⟨0,constr,uni,l1,l2⟩ else return ⟨1,constr,uni,l1,l2⟩
            | .some D => do
                let (.mk constr uni l1 l2) ← D.foldlM (.mk constr uni l1 l2 : Prod4 _ _ _ _) (fun inds lvs (.mk constr uni l1 l2) => do
                  mtrace on .zero with s!"[embedBackCore] comparing to {lvs}"
                  let load : MetaM Unit :=
                    match getFirstLnodeDataFrom (.const n lvs) with
                    | .none => pure ()
                    | .some (module, thmIdx) =>
                        let moduleB := module.toString.toUTF8
                        match thmData.find? moduleB with
                        | .none => throwError s!"[embedBackDefEqCore] module {module} isn't in thmData"
                        | .some thmDs =>
                            let thmD := thmDs[thmIdx]!
                            thmD.mctx.loadNoCo
                  load
                  let mut uni := uni
                  let mut nope? := false
                  let mut l1 := l1
                  let mut l2 := l2
                  for i in l, lv in lvs do
                    let lcase := lv.hasLnodes
                    let ⟨i,ml1,ml2⟩ ← (if lcase then return ⟨i,l1,l2⟩ else mvarifyLTnodesIn i l1 l2)
                    l1 := ml1
                    l2 := ml2
                    mtrace on .zero with s!"[embedBackCore] comparing {Expr.sort i} and {Expr.sort lv}"
                    match ← defEqWiMv (.sort i) (.sort lv) l1 l2 with
                    | .none =>
                        mtrace on .zero with s!"[embedBackCore] non defeq"
                        nope? := true
                        break
                    | .some (Ls,_) =>
                      mtrace on .zero with s!"[embedBackCore] defeq"
                      if lcase
                      then
                        uni := ← embedUpdateWrtLevels empty? intersect difference l1 l2 inds Ls uni
                      else
                        uni := ← uni.foldlM ListProd.nil (fun ds ef R => do
                          let I := intersect ds inds
                          if empty? I
                          then return .cons ds ef R
                          else
                            let D := difference ds inds
                            let pre (R) :=
                              (if empty? D then R else .cons D ef R)
                            match ← embedPropagateAsTnodes l1 l2 ef Ls {} with
                            | .none => return pre R
                            | .some nef => return pre <| .cons I nef R
                          )
                  if nope?
                  then
                    let nuni := uni.foldl ListProd.nil (fun ds ef R =>
                        let ds := difference ds inds
                        if empty? ds
                        then R
                        else .cons ds ef R
                        )
                    let constr := difference constr inds
                    return .mk constr nuni l1 l2
                  else
                    let constr := uni.foldl empty (fun ds _ R =>
                      union ds R)
                    return .mk constr uni l1 l2
                  )
                mtrace on .zero with s!"[embedBackCore] looking at const {n} {l}"
                mtrace on .zero with s!"[embedBackCore] proceeding with constr {repr constr}"
                mtrace on .one with s!"[embedBackCore] and uni {toString uni}"
                if empty? constr
                then if naive? then return ⟨0,constr,uni,l1,l2⟩ else return ⟨1,constr,uni,l1,l2⟩
                else return ⟨2,constr,uni,l1,l2⟩
          )
        -- tnodes affected
        (fun backIdx pos _ workas T constr uni naive? l1 l2 =>
          embedTnodes
            empty? intersect difference l1 l2 backIdx pos
            workas extWorkas T constr uni naive?
          )
        (fun _ _ _ _ _ _ _ _ _ _ _ _ =>
          throwError s!"[embedBackCore] we don't expect lnodes in backward term")




@[specialize, inline]
partial def embedBackMain (l1 : LocalContext) (l2 : LocalInstances) (thmData : CTrie (Array ThmFormat))
    [Repr IdxCollType] [ToString IdxCollType]
    (empty? : IdxCollType → Bool) (intersect union difference : IdxCollType → IdxCollType → IdxCollType) (empty : IdxCollType)
    (constr : IdxCollType)
    (revCountMax : Nat) (extWorkas : List FVarId)
    (E : Expr) (T : PaInG IdxCollType)
    : MetaM (Prod5 UInt8 IdxCollType (ListProd IdxCollType embedBackData) LocalContext LocalInstances) := do
    do
    clearMvarAssignments -- this is needed so that we may fold over assignement PHachMaps in ↓ and get new assignements only
    embedBackCore thmData empty? intersect union difference empty l1 l2 constr revCountMax extWorkas E T



/-
Fix notes
- PaIn → PaInG
- defEqNoMv → defEqWiMv

TODO:
- Continue at forwSimple, then do rw with ↓ inmind and processes and sandbox and tests
- use queryLCoreWW at rewrite
- test on library size ?

-/

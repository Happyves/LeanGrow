

/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/


import LeanGrowBeta.Core.Embedding.UnifyAPI
import LeanGrowBeta.Caching.Formating.Types

open Lean Meta PaIn


variable {IdxCollType : Type _}


structure embedBackData where
  ln : ListProd Nat Expr
  llv : ListProd Nat Level
  tn : ListProd3 Nat Nat Expr
  tlv : ListProd3 Nat Nat Level
deriving Inhabited, Repr

instance : ToString embedBackData where
  toString := fun x => s!"⟨ ln := {toString x.ln}, lv := {toString x.llv}, tn := {toString x.tn}, tlv := {toString x.tlv}⟩"


structure embedForwRWData where
  ln : ListProd Nat Expr
  llv : ListProd Nat Level
deriving Inhabited, Repr

instance : ToString embedForwRWData where
  toString := fun x => s!"⟨ ln := {toString x.ln}, lv := {toString x.llv}⟩"


@[specialize]
def embedPropagateAsTnodes (l1 : LocalContext) (l2 : LocalInstances) (ef : embedBackData)
  (La : PersistentHashMap LMVarId Level) (Ta : PersistentHashMap MVarId Expr) :
  MetaM (Option embedBackData) :=
  withReader (fun ctx => {ctx with lctx := l1, localInstances := l2}) do
    -- trace set Tracing.Flags.none in do
    let mut res := ef
    for (mv, lv) in Ta do
      mtrace on .zero with s!"[embedPropagateAsTnodes] looking at assignement {repr mv} with val {← ppExpr lv}"
      match mv.name with
      | .num (.num _ backIdx) pos =>
          match res.tn.find? (fun x y _ => x == backIdx && y == pos) with
          | .none =>
              mtrace on .zero with s!"[embedPropagateAsTnodes] new, adding it"
              res := {res with tn := (.cons backIdx pos lv res.tn)}
          | .some _ _ al =>
              mtrace on .zero with s!"[embedPropagateAsTnodes] comparing to existing {← ppExpr al}"
              if (← defEqWiMv al lv l1 l2).isSome
              then
                continue
              else
                return .none
      | _ => panic s!"[embedPropagateAsTnodes] assignements from defeq contained level mvar not in format: {repr mv}"
    for (mv, lv) in La do
      -- mtrace on .zero with s!"[embedUpdateWrtMvars] looking at assignement {repr mv} with val {← ppExpr lv}"
      match mv.name with
      | .num (.num _ backIdx) pos =>
          match res.tlv.find? (fun x y _ => x == backIdx && y == pos) with
          | .none =>
              mtrace on .zero with s!"[embedPropagateAsTnodes] new, adding it"
              res := {res with tlv := (.cons backIdx pos lv res.tlv)}
          | .some _ _ al =>
              mtrace on .zero with s!"[embedPropagateAsTnodes] comparing to existing {al}"
              if ← (do let res ← isLevelDefEq al lv ; clearMvarAssignments ; return res)
              then
                continue
              else
                return .none
      | _ => panic s!"[embedPropagateAsTnodes] assignements from defeq contained level mvar not in format: {repr mv}"
    return .some res



@[specialize, inline]
def embedUpdateWrtLevel [Repr IdxCollType]
  (empty? : IdxCollType → Bool) (intersect difference : IdxCollType → IdxCollType → IdxCollType)
  (l1 : LocalContext) (l2 : LocalInstances)
  (asInds : IdxCollType) (mv : LMVarId) (lv : Level)
  (sofar : ListProd IdxCollType embedBackData)
  : MetaM <| ListProd IdxCollType embedBackData := do
    -- trace set Tracing.Flags.none in do
    mtrace on .zero with s!"[embedUpdateWrtLevels] call on asInds {repr asInds}"
    sofar.foldlM .nil (fun is ef S => do
      let I := intersect asInds is
      if empty? I
      then
        mtrace on .zero with s!"[embedUpdateWrtLevel] is had empty intersection , leaving ; is {repr is}"
        return .cons is ef S
      else
        mtrace on .zero with s!"[embedUpdateWrtLevel] found intersection I {repr I}"
        let D := difference is asInds
        mtrace on .zero with s!"[embedUpdateWrtLevel] found diff D {repr D}"
        let pre (R : ListProd IdxCollType embedBackData) :=
          if empty? D then R else .cons D ef R
        let res := ef
        mtrace on .zero with s!"[embedUpdateWrtLevel] looking at assignement {repr mv} with val {lv}"
        match mv.name with
        | .num (.num _ _) pos =>
            match res.llv.find? (fun y _ => y == pos) with
            | .none =>
                mtrace on .zero with s!"[embedUpdateWrtLevel] adding it to embed"
                let res := {res with llv := (.cons pos lv res.llv)}
                return pre (.cons I res S)
            | .some _ al => do
                mtrace on .zero with s!"[embedUpdateWrtLevel] comparing to {al}"
                if lv.hasTnodes
                then
                  if al.hasTnodes
                  then
                    return pre S
                  else
                    let ⟨lv,l1,l2⟩ ← mvarifyLTnodesIn lv l1 l2
                    withReader (fun ctx => {ctx with lctx := l1, localInstances := l2}) do
                    match ← defEqWiMv (.sort al) (.sort lv) l1 l2 with
                    | .none =>
                        return pre S
                    | .some (La, Ta) =>
                        match ← embedPropagateAsTnodes l1 l2 res La Ta with
                        | .some r =>
                            return pre (.cons I r S)
                        | .none =>
                            return pre S
                else
                  let ⟨al,l1,l2⟩ ← mvarifyLTnodesIn al l1 l2
                  withReader (fun ctx => {ctx with lctx := l1, localInstances := l2}) do
                  match ← defEqWiMv  (.sort al) (.sort lv) l1 l2 with
                  | .none =>
                      return pre S
                  | .some (La, Ta) =>
                      match ← embedPropagateAsTnodes l1 l2 res La Ta with
                      | .some r =>
                          return pre (.cons I r S)
                      | .none =>
                          return pre S
        | _ => panic s!"[embedUpdateWrtLevels] assignements from defeq contained level mvar not in format: {repr mv}"
    )




@[specialize, inline]
def embedUpdateWrtLevelNotT [Repr IdxCollType]
  (empty? : IdxCollType → Bool) (intersect difference : IdxCollType → IdxCollType → IdxCollType)
  (l1 : LocalContext) (l2 : LocalInstances)
  (asInds : IdxCollType) (mv : LMVarId) (lv : Level)
  (sofar : ListProd IdxCollType embedForwRWData)
  : MetaM <| ListProd IdxCollType embedForwRWData := do
    -- trace set Tracing.Flags.none in do
    mtrace on .zero with s!"[embedUpdateWrtLevelNotTs] call on asInds {repr asInds}"
    sofar.foldlM .nil (fun is ef S => do
      let I := intersect asInds is
      if empty? I
      then
        mtrace on .zero with s!"[embedUpdateWrtLevelNotT] is had empty intersection , leaving ; is {repr is}"
        return .cons is ef S
      else
        mtrace on .zero with s!"[embedUpdateWrtLevelNotT] found intersection I {repr I}"
        let D := difference is asInds
        mtrace on .zero with s!"[embedUpdateWrtLevelNotT] found diff D {repr D}"
        let pre (R : ListProd IdxCollType embedForwRWData) :=
          if empty? D then R else .cons D ef R
        let res := ef
        mtrace on .zero with s!"[embedUpdateWrtLevelNotT] looking at assignement {repr mv} with val {lv}"
        match mv.name with
        | .num (.num _ _) pos =>
            match res.llv.find? (fun y _ => y == pos) with
            | .none =>
                mtrace on .zero with s!"[embedUpdateWrtLevelNotT] adding it to embed"
                let res := {res with llv := (.cons pos lv res.llv)}
                return pre (.cons I res S)
            | .some _ al => do
                mtrace on .zero with s!"[embedUpdateWrtLevelNotT] comparing to {al}"
                match res.llv.find? (fun y _ => y == pos) with
            | .none =>
                mtrace on .zero with s!"[embedUpdateWrtLevel] adding it to embed"
                let res := {res with llv := (.cons pos lv res.llv)}
                return pre (.cons I res S)
            | .some _ al => do
                mtrace on .zero with s!"[embedUpdateWrtLevel] comparing to {al}"
                withReader (fun ctx => {ctx with lctx := l1, localInstances := l2}) do
                match ← defEqWiMv (.sort al) (.sort lv) l1 l2 with
                | .none =>
                    return pre S
                | .some .. =>
                    return pre (.cons I res S)
        | _ => panic s!"[embedUpdateWrtLevels] assignements from defeq contained level mvar not in format: {repr mv}"
    )




@[specialize]
def embedUpdateWrtLevels [Repr IdxCollType]
  (empty? : IdxCollType → Bool) (intersect difference : IdxCollType → IdxCollType → IdxCollType)
  (l1 : LocalContext) (l2 : LocalInstances)
  (asInds : IdxCollType) (As : PersistentHashMap LMVarId Level)
  (sofar : ListProd IdxCollType embedBackData)
  : MetaM <| ListProd IdxCollType embedBackData := do
    -- trace set Tracing.Flags.none in do
    mtrace on .zero with s!"[embedUpdateWrtLevels] call on asInds {repr asInds}"
    sofar.foldlM .nil (fun is ef S => do
      let I := intersect asInds is
      if empty? I
      then
        mtrace on .zero with s!"[embedUpdateWrtLevels] is had empty intersection , leaving ; is {repr is}"
        return .cons is ef S
      else
        mtrace on .zero with s!"[embedUpdateWrtLevels] found intersection I {repr I}"
        if As.isEmpty
        then return ListProd.cons is ef S
        else
          let D := difference is asInds
          mtrace on .zero with s!"[embedUpdateWrtLevels] found diff D {repr D}"
          let pre (R : ListProd IdxCollType embedBackData) :=
            if empty? D then R else .cons D ef R
          let mut res := ef
          let mut broke? := false
          let mut l1 := l1
          let mut l2 := l2
          for (mv, lv) in As do
            mtrace on .zero with s!"[embedUpdateWrtLevels] looking at assignement {repr mv} with val {lv}"
            match mv.name with
            | .num (.num _ _) pos =>
                match res.llv.find? (fun y _ => y == pos) with
                | .none =>
                    mtrace on .zero with s!"[embedUpdateWrtLevels] adding it to embed"
                    res := {res with llv := (.cons pos lv res.llv)}
                | .some _ al => do
                    mtrace on .zero with s!"[embedUpdateWrtLevels] comparing to {al}"
                    if lv.hasTnodes
                    then
                      if al.hasTnodes
                      then
                        broke? := true
                        break
                      else
                        let ⟨lv,l1',l2'⟩ ← mvarifyLTnodesIn lv l1 l2
                        l1 := l1'
                        l2 := l2'
                        match ← defEqWiMv (.sort al) (.sort lv) l1 l2 with
                        | .none =>
                            broke? := true
                            break
                        | .some (La, Ta) =>
                            match ← embedPropagateAsTnodes l1 l2  res La Ta with
                            | .some r =>
                                res := r
                            | .none =>
                                broke? := true
                                break
                    else
                      let ⟨lv,l1',l2'⟩ ← mvarifyLTnodesIn al l1 l2
                      l1 := l1'
                      l2 := l2'
                      match ← defEqWiMv  (.sort al) (.sort lv) l1 l2 with
                      | .none =>
                          broke? := true
                          break
                      | .some (La, Ta) =>
                          match ← embedPropagateAsTnodes l1 l2  res La Ta with
                          | .some r =>
                              res := r
                          | .none =>
                              broke? := true
                              break
            | _ => panic s!"[embedUpdateWrtLevels] assignements from defeq contained level mvar not in format: {repr mv}"
          if broke?
          then return pre S
          else return pre (.cons I res S)
      )




@[specialize, inline]
def embedUpdateWrtLevelsNoT [Repr IdxCollType]
  (empty? : IdxCollType → Bool) (intersect difference : IdxCollType → IdxCollType → IdxCollType)
  (l1 : LocalContext) (l2 : LocalInstances)
  (asInds : IdxCollType) (As : PersistentHashMap LMVarId Level)
  (sofar : ListProd IdxCollType embedForwRWData)
  : MetaM <| ListProd IdxCollType embedForwRWData := do
    -- trace set Tracing.Flags.none in do
    mtrace on .zero with s!"[embedUpdateWrtLevelsNoT] call on asInds {repr asInds}"
    sofar.foldlM .nil (fun is ef S => do
      let I := intersect asInds is
      if empty? I
      then
        mtrace on .zero with s!"[embedUpdateWrtLevelsNoT] is had empty intersection , leaving ; is {repr is}"
        return .cons is ef S
      else
        mtrace on .zero with s!"[embedUpdateWrtLevelsNoT] found intersection I {repr I}"
        if As.isEmpty
        then return ListProd.cons is ef S
        else
          let D := difference is asInds
          mtrace on .zero with s!"[embedUpdateWrtLevelsNoT] found diff D {repr D}"
          let pre (R : ListProd IdxCollType embedForwRWData) :=
            if empty? D then R else .cons D ef R
          let mut res := ef
          let mut broke? := false
          for (mv, lv) in As do
            mtrace on .zero with s!"[embedUpdateWrtLevelsNoT] looking at assignement {repr mv} with val {lv}"
            match mv.name with
            | .num (.num _ _) pos =>
                match res.llv.find? (fun y _ => y == pos) with
                | .none =>
                    mtrace on .zero with s!"[embedUpdateWrtLevelsNoT] adding it to embed"
                    res := {res with llv := (.cons pos lv res.llv)}
                | .some _ al => do
                    mtrace on .zero with s!"[embedUpdateWrtLevelsNoT] comparing to {al}"
                    match ← defEqWiMv (.sort al) (.sort lv) l1 l2 with
                    | .none =>
                        broke? := true
                        break
                    | .some .. =>
                        continue
            | _ => panic s!"[embedUpdateWrtLevelsNoT] assignements from defeq contained level mvar not in format: {repr mv}"
          if broke?
          then return pre S
          else return pre (.cons I res S)
      )





@[specialize, inline]
def embedUpdateWrtMvar [Repr IdxCollType]
  (empty? : IdxCollType → Bool) (intersect difference : IdxCollType → IdxCollType → IdxCollType)
  (l1 : LocalContext) (l2 : LocalInstances)
  (asInds : IdxCollType) (mv : MVarId) (lv : Expr)
  (sofar : ListProd IdxCollType embedBackData)
  : MetaM (ListProd IdxCollType embedBackData) := do
    -- trace set Tracing.Flags.none in do
    sofar.foldlM .nil (fun is ef S => do
      let I := intersect asInds is
      if empty? I
      then
        mtrace on .zero with s!"[embedUpdateWrtMvar] is had empty intersection , leaving ; is {repr is}"
        return .cons is ef S
      else
      mtrace on .zero with s!"[embedUpdateWrtMvar] found intersection I {repr I}"
      let D := difference is asInds
      mtrace on .zero with s!"[embedUpdateWrtMvar] found diff D {repr D}"
      let pre (R : ListProd IdxCollType embedBackData) :=
        if empty? D then R else .cons D ef R
      let res := ef
      mtrace on .zero with s!"[embedUpdateWrtMvar] looking at assignement {repr mv} with val {← ppExpr lv}"
      match mv.name with
      | .num (.num _ _) pos =>
          match res.ln.find? (fun y _ => y == pos) with
          | .none =>
              mtrace on .zero with s!"[embedUpdateWrtMvar] is had empty intersection , leaving ; is {repr is}"
              let res := {res with ln := (.cons pos lv res.ln)}
              return pre (.cons I res S)
          | .some _ al => do
              mtrace on .zero with s!"[embedUpdateWrtMvar] comparing to {← ppExpr al}"
              if lv.hasTnodes
              then
                if al.hasTnodes
                then
                  return pre S
                else
                  let ⟨lv,l1,l2⟩ ← mvarifyTnodesRecWiContextIn lv l1 l2
                  match ← defEqWiMv al lv l1 l2 with
                  | .none =>
                      return pre S
                  | .some (La, Ta) =>
                      match ← embedPropagateAsTnodes l1 l2 res La Ta with
                      | .some r =>
                          return pre (.cons I r S)
                      | .none =>
                          return pre S
              else
                let ⟨al,l1,l2⟩ ← mvarifyTnodesRecWiContextIn al l1 l2
                match ← defEqWiMv al lv l1 l2 with
                | .none =>
                    return pre S
                | .some (La, Ta) =>
                    match ← embedPropagateAsTnodes l1 l2 res La Ta with
                    | .some r =>
                        return pre (.cons I r S)
                    | .none =>
                        return pre S
      | _ => panic s!"[embedUpdateWrtMvar] assignements from defeq contained level mvar not in format: {repr mv}"
      )




@[specialize, inline]
def embedUpdateWrtMvarNoT [Repr IdxCollType]
  (empty? : IdxCollType → Bool) (intersect difference : IdxCollType → IdxCollType → IdxCollType)
  (l1 : LocalContext) (l2 : LocalInstances)
  (asInds : IdxCollType) (mv : MVarId) (lv : Expr)
  (sofar : ListProd IdxCollType embedForwRWData)
  : MetaM (ListProd IdxCollType embedForwRWData) := do
    -- trace set Tracing.Flags.none in do
    sofar.foldlM .nil (fun is ef S => do
      let I := intersect asInds is
      if empty? I
      then
        mtrace on .zero with s!"[embedUpdateWrtMvarNoT] is had empty intersection , leaving ; is {repr is}"
        return .cons is ef S
      else
      mtrace on .zero with s!"[embedUpdateWrtMvarNoT] found intersection I {repr I}"
      let D := difference is asInds
      mtrace on .zero with s!"[embedUpdateWrtMvarNoT] found diff D {repr D}"
      let pre (R : ListProd IdxCollType embedForwRWData) :=
        if empty? D then R else .cons D ef R
      let res := ef
      mtrace on .zero with s!"[embedUpdateWrtMvarNoT] looking at assignement {repr mv} with val {← ppExpr lv}"
      match mv.name with
      | .num (.num _ _) pos =>
          match res.ln.find? (fun y _ => y == pos) with
          | .none =>
              mtrace on .zero with s!"[embedUpdateWrtMvarNoT] is had empty intersection , leaving ; is {repr is}"
              let res := {res with ln := (.cons pos lv res.ln)}
              return pre (.cons I res S)
          | .some _ al => do
              mtrace on .zero with s!"[embedUpdateWrtMvarNoT] comparing to {← ppExpr al}"
              match ← defEqWiMv al lv l1 l2 with
              | .none =>
                  return pre S
              | .some .. =>
                  return pre (.cons I res S)
      | _ => panic s!"[embedUpdateWrtMvar] assignements from defeq contained level mvar not in format: {repr mv}"
      )





@[specialize]
def embedUpdateWrtMvars [Repr IdxCollType]
  (empty? : IdxCollType → Bool) (intersect difference : IdxCollType → IdxCollType → IdxCollType)
  (l1 : LocalContext) (l2 : LocalInstances)
  (asInds : IdxCollType) (As : PersistentHashMap MVarId Expr)
  (sofar : ListProd IdxCollType embedBackData)
  : MetaM (ListProd IdxCollType embedBackData) := do
    -- trace set Tracing.Flags.none in do
    mtrace on .zero with s!"[embedUpdateWrtMvars] call on asInds {repr asInds}"
    sofar.foldlM .nil (fun is ef S => do
      let I := intersect asInds is
      if empty? I
      then
        mtrace on .zero with s!"[embedUpdateWrtMvars] is had empty intersection , leaving ; is {repr is}"
        return .cons is ef S
      else
        mtrace on .zero with s!"[embedUpdateWrtMvars] found intersection I {repr I}"
        if As.isEmpty
        then return ListProd.cons is ef S
        else
          let D := difference is asInds
          mtrace on .zero with s!"[embedUpdateWrtMvars] found diff D {repr D}"
          let pre (R : ListProd IdxCollType embedBackData) :=
            if empty? D then R else .cons D ef R
          let mut res := ef
          let mut broke? := false
          for (mv, lv) in As do
            mtrace on .zero with s!"[embedUpdateWrtMvars] looking at assignement {repr mv} with val {← ppExpr lv}"
            match mv.name with
            | .num (.num _ _) pos =>
                match res.ln.find? (fun y _ => y == pos) with
                | .none =>
                    mtrace on .zero with s!"[embedUpdateWrtMvar] is had empty intersection , leaving ; is {repr is}"
                    res := {res with ln := (.cons pos lv res.ln)}
                | .some _ al => do
                    mtrace on .zero with s!"[embedUpdateWrtMvar] comparing to {← ppExpr al}"
                    if lv.hasTnodes
                    then
                      if al.hasTnodes
                      then
                        broke? := true
                        break
                      else
                        let ⟨lv,l1,l2⟩ ← mvarifyTnodesRecWiContextIn lv l1 l2
                        match ← defEqWiMv al lv l1 l2 with
                        | .none =>
                            broke? := true
                            break
                        | .some (La, Ta) =>
                            match ← embedPropagateAsTnodes l1 l2 res La Ta with
                            | .some r =>
                                res := r
                            | .none =>
                                broke? := true
                                break
                    else
                      let ⟨al,l1,l2⟩ ← mvarifyTnodesRecWiContextIn al l1 l2
                      match ← defEqWiMv al lv l1 l2 with
                      | .none =>
                          broke? := true
                          break
                      | .some (La, Ta) =>
                          match ← embedPropagateAsTnodes l1 l2 res La Ta with
                          | .some r =>
                              res := r
                          | .none =>
                              broke? := true
                              break
            | _ => panic s!"[embedUpdateWrtMvars] assignements from defeq contained level mvar not in format: {repr mv}"
          if broke?
          then return pre S
          else return pre (.cons I res S)
      )




@[specialize, inline]
def embedUpdateWrtMvarsNoT [Repr IdxCollType]
  (empty? : IdxCollType → Bool) (intersect difference : IdxCollType → IdxCollType → IdxCollType)
  (l1 : LocalContext) (l2 : LocalInstances)
  (asInds : IdxCollType) (As : PersistentHashMap MVarId Expr)
  (sofar : ListProd IdxCollType embedForwRWData)
  : MetaM (ListProd IdxCollType embedForwRWData) := do
    -- trace set Tracing.Flags.none in do
    mtrace on .zero with s!"[embedUpdateWrtMvarsNoT] call on asInds {repr asInds}"
    sofar.foldlM .nil (fun is ef S => do
      let I := intersect asInds is
      if empty? I
      then
        mtrace on .zero with s!"[embedUpdateWrtMvarsNoT] is had empty intersection , leaving ; is {repr is}"
        return .cons is ef S
      else
        mtrace on .zero with s!"[embedUpdateWrtMvarsNoT] found intersection I {repr I}"
        if As.isEmpty
        then return ListProd.cons is ef S
        else
          let D := difference is asInds
          mtrace on .zero with s!"[embedUpdateWrtMvarsNoT] found diff D {repr D}"
          let pre (R : ListProd IdxCollType embedForwRWData) :=
            if empty? D then R else .cons D ef R
          let mut res := ef
          let mut broke? := false
          for (mv, lv) in As do
            mtrace on .zero with s!"[embedUpdateWrtMvarsNoT] looking at assignement {repr mv} with val {← ppExpr lv}"
            match mv.name with
            | .num (.num _ _) pos =>
                match res.ln.find? (fun y _ => y == pos) with
                | .none =>
                    mtrace on .zero with s!"[embedUpdateWrtMvar] is had empty intersection , leaving ; is {repr is}"
                    res := {res with ln := (.cons pos lv res.ln)}
                | .some _ al => do
                    mtrace on .zero with s!"[embedUpdateWrtMvar] comparing to {← ppExpr al}"
                    match ← defEqWiMv al lv l1 l2 with
                    | .none =>
                        broke? := true
                        break
                    | .some .. =>
                        continue
            | _ => panic s!"[embedUpdateWrtMvarsNoT] assignements from defeq contained level mvar not in format: {repr mv}"
          if broke?
          then return pre S
          else return pre (.cons I res S)
      )





/- does **not** check if candidates are compatible ; keeps assignement fromarg `B`-/
@[specialize, inline]
def embedUnion
  (empty? : IdxCollType → Bool) (intersect difference : IdxCollType → IdxCollType → IdxCollType)
  (A B : ListProd IdxCollType embedBackData)
  : ListProd IdxCollType embedBackData :=
  A.foldl B (fun inds ef R =>
    let (pR,rem) := R.foldl (.nil, inds) (fun is lef (R,inds) =>
      let I := intersect inds is
      if empty? I
      then (.cons is lef R, inds)
      else
        let ninds := difference inds I
        let D := difference is inds
        let pre (R : ListProd IdxCollType embedBackData) :=
          (if empty? D then R else .cons D lef R)
        let ntn := ef.tn.foldl lef.tn (fun i j res TN =>
          match lef.tn.find? (fun x y _ => i == x && y == j) with
          | .none => .cons i j res TN
          | .some .. => TN
          )
        let ntlv := ef.tlv.foldl lef.tlv (fun i j res TN =>
          match lef.tlv.find? (fun x y _ => i == x && y == j) with
          | .none => .cons i j res TN
          | .some .. => TN
          )
        let nln := ef.ln.foldl lef.ln (fun j res TN =>
          match lef.ln.find? (fun y _ => y == j) with
          | .none => .cons j res TN
          | .some .. => TN
          )
        let nllv := ef.llv.foldl lef.llv (fun j res TN =>
          match lef.llv.find? (fun y _ =>  y == j) with
          | .none => .cons j res TN
          | .some .. => TN
          )
        (pre (.cons I ⟨nln,nllv,ntn,ntlv⟩ R), ninds)
      )
    if empty? rem
    then pR
    else .cons rem ef pR
    )





/- does **not** check if candidates are compatible ; keeps assignement fromarg `B`-/
@[specialize, inline]
def embedUnionF
  (empty? : IdxCollType → Bool) (intersect difference : IdxCollType → IdxCollType → IdxCollType)
  (A B : ListProd IdxCollType embedForwRWData)
  : ListProd IdxCollType embedForwRWData :=
  A.foldl B (fun inds ef R =>
    let (pR,rem) := R.foldl (.nil, inds) (fun is lef (R,inds) =>
      let I := intersect inds is
      if empty? I
      then (.cons is lef R, inds)
      else
        let ninds := difference inds I
        let D := difference is inds
        let pre (R : ListProd IdxCollType embedForwRWData) :=
          (if empty? D then R else .cons D lef R)
        let nln := ef.ln.foldl lef.ln (fun j res TN =>
          match lef.ln.find? (fun y _ => y == j) with
          | .none => .cons j res TN
          | .some .. => TN
          )
        let nllv := ef.llv.foldl lef.llv (fun j res TN =>
          match lef.llv.find? (fun y _ =>  y == j) with
          | .none => .cons j res TN
          | .some .. => TN
          )
        (pre (.cons I ⟨nln,nllv⟩ R), ninds)
      )
    if empty? rem
    then pR
    else .cons rem ef pR
    )

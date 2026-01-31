
/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/


import LeanGrow.Src.Core.Embedding.EmbedQueryBack
import LeanGrow.Src.Core.Embedding.EmbedRWAPI

open Lean Meta PaInG

variable {IdxCollType : Type}


def embedBackData.eq (l1 : LocalContext) (l2 : LocalInstances) (A B : embedBackData) : MetaM Bool := do
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
          A.tlv.foldlMcps [] (fun i j l s q =>
            match B.tlv.find? (fun x y _ => x == i && y == j) with
            | .none => return false
            | .some _ _ L => do
              if ← (do let res ← isLevelDefEq l L ; clearMvarAssignments ; return res)
              then q ((i,j) :: s)
              else return false
            ) <| fun s => do
              B.tlv.foldlMcps () (fun i j _ d q =>
                if s.contains (i,j) then q d else return false
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
                          A.tn.foldlMcps [] (fun i j l s q =>
                            match B.tn.find? (fun x y _ => x == i && y == j) with
                            | .none => return false
                            | .some _ _ L => do
                              if ← defEqWiCommonWorker l1 l2 l L
                              then q ((i,j) :: s)
                              else return false
                            ) <| fun s => do
                              B.tn.foldlMcps () (fun i j _ d q =>
                                if s.contains (i,j) then q d else return false
                                ) <| fun _ => do
                                  return true




@[specialize]
def mergeOccsTwo2 {α : Type _} [ToString α]
  (l1 : LocalContext) (l2 : LocalInstances)
  (Eq? : LocalContext → LocalInstances → α → α → MetaM Bool) (mer : rwDirs → rwDirs → rwDirs)
  (F A : ListProd Nat (ListProd3 α rwDirs (List FVarId))) :
  MetaM <| ListProd Nat (ListProd3 α rwDirs (List FVarId)) :=
  let eq? := Eq? l1 l2
  let rec @[specialize] inner_fst (sofar left : ListProd3 α rwDirs (List FVarId)) : (ListProd3 α rwDirs (List FVarId)) → MetaM (ListProd3 α rwDirs (List FVarId))
    | .nil => return sofar
    | .cons as ds ws more => do
      match ← left.findM? (fun x _ _ => eq? x as) with
      | .none => inner_fst (.cons as (mer .no ds) ws sofar) left more
      | .some _ mds _ => inner_fst (.cons as (mer mds ds) ws sofar) left more
  let rec @[specialize] inner_snd (sofar : ListProd3 α rwDirs (List FVarId)) : ListProd3 α rwDirs (List FVarId) → MetaM (ListProd3 α rwDirs (List FVarId))
    | .nil => return sofar
    | .cons as ds ws more => do
      match ← sofar.findM? (fun x _ _ => eq? x as) with
      | .none => inner_snd (.cons as (mer ds .no) ws sofar) more
      | .some .. => inner_snd sofar more
  let inner := (fun l r => do inner_snd (← inner_fst .nil l r) l)
  let rec @[specialize] main_fst (res :  ListProd Nat (ListProd3 α rwDirs (List FVarId))) :  ListProd Nat (ListProd3 α rwDirs (List FVarId)) → MetaM ( ListProd Nat (ListProd3 α rwDirs (List FVarId)))
    | .nil => return res
    | .cons idx data more =>
      match A.find? (fun x  _ => x == idx) with
      | .none =>
        let newdata := data.map (fun x y z => (x, (mer y .no), z))
        main_fst (.cons idx newdata res) more
      | .some _ odata => do
        let here ← inner data odata
        main_fst (.cons idx here res) more
  let rec @[specialize] main_snd (res :  ListProd Nat (ListProd3 α rwDirs (List FVarId))) :  ListProd Nat (ListProd3 α rwDirs (List FVarId)) → MetaM ( ListProd Nat (ListProd3 α rwDirs (List FVarId)))
    | .nil => return res
    | .cons idx data more =>
      match res.find? (fun x _ => x == idx) with
      | .none =>
        let newdata := data.map (fun x y z => (x, (mer .no y), z))
        main_snd (.cons idx newdata res) more
      | .some .. => main_snd res more
  -- trace set Tracing.Flags.none in
  do
  mtracing
  mtrace  on .zero with s!"[mergeOccsTwo2] Call on F {repr <| F.map (fun x y => (x, y.map (fun x y z => (toString x, y, z))))} A {repr <| A.map (fun x y => (x, y.map (fun x y z => (toString x, y, z))))}"
  let res ← main_snd (← main_fst .nil F) A
  mtrace  on .zero with s!"[mergeOccsTwo2] returning {repr <| res.map (fun x y => (x, y.map (fun x y z => (toString x, y, z))))}"
  return res



@[specialize]
def mergeOccsThree2 {α : Type _} [ToString α]
  (l1 : LocalContext) (l2 : LocalInstances)
  (Eq? : LocalContext → LocalInstances → α → α → MetaM Bool)
  (F A Z : ListProd Nat (ListProd3 α rwDirs (List FVarId))) :
  MetaM <| ListProd Nat (ListProd3 α rwDirs (List FVarId)) :=
  let eq? := Eq? l1 l2
  let rec @[specialize] inner_fst (sofar a z : ListProd3 α rwDirs (List FVarId)) : (ListProd3 α rwDirs (List FVarId)) → MetaM (ListProd3 α rwDirs (List FVarId))
    | .nil => return sofar
    | .cons as ds ws more => do
      match ← a.findM? (fun x _ _ => eq? x as) with
      | .none =>
        match ← z.findM? (fun x _ _ => eq? x as) with
        | .none => inner_fst (.cons as (.le ds .no .no) ws sofar) a z more
        | .some _ zds _ => inner_fst (.cons as (.le ds .no zds) ws sofar) a z more
      | .some _ ads _ =>
        match ← z.findM? (fun x _ _ => eq? x as) with
        | .none => inner_fst (.cons as (.le ds ads .no) ws sofar) a z more
        | .some _ zds _ => inner_fst (.cons as (.le ds ads zds) ws sofar) a z more
  let rec @[specialize] inner_snd (sofar z : ListProd3 α rwDirs (List FVarId)) : (ListProd3 α rwDirs (List FVarId)) → MetaM (ListProd3 α rwDirs (List FVarId))
    | .nil => return sofar
    | .cons as ds ws more => do
      match ← sofar.findM? (fun x _ _ => eq? x as) with
      | .none =>
        match ← z.findM? (fun x _ _ => eq? x as) with
        | .none => inner_snd (.cons as (.le .no ds .no) ws sofar) z more
        | .some _ zds _ => inner_snd (.cons as (.le .no ds zds) ws sofar) z more
      | .some ..=> inner_snd (sofar) z more
  let rec @[specialize] inner_thd (sofar : ListProd3 α rwDirs (List FVarId)) : ListProd3 α rwDirs (List FVarId) → MetaM (ListProd3 α rwDirs (List FVarId))
    | .nil => return sofar
    | .cons as ds ws more => do
      match ← sofar.findM? (fun x _ _ => eq? x as) with
      | .none => inner_thd (.cons as (.le .no .no ds) ws sofar) more
      | .some .. => inner_thd (sofar) more
  let inner := fun l r w => do inner_thd (← inner_snd (← inner_fst .nil r w l) l r) w
  let rec @[specialize] main_fst (res : ListProd Nat (ListProd3 α rwDirs (List FVarId))) : ListProd Nat (ListProd3 α rwDirs (List FVarId)) → MetaM (ListProd Nat (ListProd3 α rwDirs (List FVarId)))
    | .nil => return res
    | .cons idx data more => do
      match A.find? (fun x _ => x == idx) with
      | .none =>
        match Z.find? (fun x _ => x == idx) with
        | .none =>
          let newdata := data.map (fun x y z => (x, rwDirs.le y .no .no, z))
          main_fst (.cons idx newdata  res) more
        | .some _ zd =>
          let newdata ←  inner data .nil zd
          main_fst (.cons idx newdata  res) more
      | .some _ ad =>
        match Z.find? (fun x _ => x == idx) with
        | .none =>
          let newdata ← inner data ad .nil
          main_fst (.cons idx newdata  res) more
        | .some _ zd =>
          let newdata ← inner data ad zd
          main_fst (.cons idx newdata  res) more
  let rec @[specialize] main_snd (res : ListProd Nat (ListProd3 α rwDirs (List FVarId))) : ListProd Nat (ListProd3 α rwDirs (List FVarId)) → MetaM (ListProd Nat (ListProd3 α rwDirs (List FVarId)))
    | .nil  => return res
    | .cons idx data more => do
      match res.find? (fun x _ => x == idx) with
      | .none =>
        match Z.find? (fun x _ => x == idx) with
        | .none =>
          let newdata := data.map (fun x y z => (x, .le .no y .no, z))
          main_fst (.cons idx newdata  res) more
        | .some _ zd =>
          let newdata ← inner .nil data zd
          main_fst (.cons idx newdata  res) more
      | .some .. => main_snd res more
  let rec @[specialize] main_thd (res : ListProd Nat (ListProd3 α rwDirs (List FVarId))) : ListProd Nat (ListProd3 α rwDirs (List FVarId)) → MetaM (ListProd Nat (ListProd3 α rwDirs (List FVarId)))
    | .nil => return res
    | .cons idx data more => do
      match res.find? (fun x _ => x == idx) with
      | .none =>
        let newdata := data.map (fun x y z => (x, .le .no .no y, z))
        main_thd (.cons idx newdata  res) more
      | _ => main_thd res more
  -- trace set Tracing.Flags.none in
  do
  mtracing
  mtrace  on .zero with s!"[mergeOccsTwo] Call on F {repr <| F.map (fun x y => (x, y.map (fun x y z => (toString x, y, z))))} A {repr <| A.map (fun x y => (x, y.map (fun x y z => (toString x, y, z))))} Z {repr <| Z.map (fun x y => (x, y.map (fun x y z => (toString x, y, z))))}"
  let res ← main_thd (← main_snd (← main_fst .nil F) A) Z
  mtrace  on .zero with s!"[mergeOccsTwo] returning {repr <| res.map (fun x y => (x, y.map (fun x y z => (toString x, y, z))))}"
  return res



@[specialize]
partial def embedBackRWMain {IdxCollType : Type _}
    (l1 : LocalContext) (l2 : LocalInstances)
    (thmData : CTrie (Array ThmFormat))
    [Repr IdxCollType] [ToString IdxCollType]
    (fold : ∀ {β : Type _}, IdxCollType → (init : β) → (f : Nat → β → β) → β)
    (empty? : IdxCollType → Bool) (intersect union difference : IdxCollType → IdxCollType → IdxCollType) (empty : IdxCollType)
    (sConstr locConstr : IdxCollType)
    (revCountMax : Nat) (extWorkas : List FVarId)
    (E : Expr) (T : PaInG IdxCollType)
    : MetaM (Prod4 IdxCollType (ListProd Nat (ListProd3 embedBackData rwDirs (List FVarId))) LocalContext LocalInstances) :=
      -- trace set Tracing.Flags.none in do
      do
      mtracing
      mtrace  on .zero with s!"[embedBackRWMain] call on {← PpExpr E l1 l2} with workers {repr extWorkas}"
      if ← IsProof E l1 l2
      then
        return .mk empty .nil l1 l2
      else
        let rec @[inline] m2 (l1 : LocalContext) (l2 : LocalInstances) := mergeOccsTwo2 l1 l2 embedBackData.eq
        let lISO := listIndxSingleOut fold
        let ⟨yes?,inds,here,l1,l2⟩ ← embedBackMain l1 l2 thmData
          empty? intersect union difference empty
          sConstr revCountMax extWorkas E T
        let main (l1 : LocalContext) (l2 : LocalInstances)
          (here : (ListProd IdxCollType embedBackData)) (conHere : IdxCollType) := do
          match E with
            | .app f a =>
                let ⟨locConstr,resf,l1,l2⟩ ← embedBackRWMain l1 l2 thmData fold empty? intersect union difference empty sConstr locConstr revCountMax extWorkas f T
                let ⟨locConstr',resa,l1,l2⟩ ← embedBackRWMain l1 l2 thmData fold empty? intersect union difference empty sConstr locConstr revCountMax extWorkas a T
                let res ← m2 l1 l2 .ap resf resa
                let res := mergeOnIndSpe
                  (fun x y => x.foldl y (fun x y R => .cons x y R))
                  (fun x => .cons x .yes extWorkas .nil )
                  res (lISO here)
                let locConstr := union conHere <| union locConstr locConstr'
                return ⟨locConstr,res,l1,l2⟩
            | .lam _ f a _ =>
                  let ⟨conf,resf,l1,l2⟩ ← embedBackRWMain l1 l2 thmData fold empty? intersect union difference empty locConstr locConstr revCountMax extWorkas f T
                  let w ← worker extWorkas.length
                  let ⟨wfv,a,l1,l2⟩ ← withFreeing w f a l1 l2
                  let ⟨cona,resa,l1,l2⟩ ← embedBackRWMain l1 l2 thmData fold empty? intersect union difference empty sConstr locConstr revCountMax (wfv :: extWorkas) a T
                  let res ← m2 l1 l2 .la resf resa
                  let res := mergeOnIndSpe
                    (fun x y => x.foldl y (fun x y R => .cons x y R))
                    (fun x => .cons x .yes extWorkas .nil )
                    res (lISO here)
                  let locConstr := union conHere <| union conf cona
                  return ⟨locConstr,res,l1,l2⟩
            | .forallE _ f a _ =>
                  let ⟨conf,resf,l1,l2⟩ ← embedBackRWMain l1 l2 thmData fold empty? intersect union difference empty locConstr locConstr revCountMax extWorkas f T
                  let w ← worker extWorkas.length
                  let ⟨wfv,a,l1,l2⟩ ← withFreeing w f a l1 l2
                  let ⟨cona,resa,l1,l2⟩ ← embedBackRWMain l1 l2 thmData fold empty? intersect union difference empty sConstr locConstr revCountMax (wfv :: extWorkas) a T
                  let res ← m2 l1 l2 .al resf resa
                  let res := mergeOnIndSpe
                    (fun x y => x.foldl y (fun x y R => .cons x y R))
                    (fun x => .cons x .yes extWorkas .nil )
                    res (lISO here)
                  let locConstr := union conHere <| union conf cona
                  return ⟨locConstr,res,l1,l2⟩
            | .letE _ f a z _ =>
                  let ⟨conf,resf,l1,l2⟩ ← embedBackRWMain l1 l2 thmData fold empty? intersect union difference empty locConstr locConstr revCountMax extWorkas f T
                  let ⟨cona,resa,l1,l2⟩ ← embedBackRWMain l1 l2 thmData fold empty? intersect union difference empty locConstr locConstr revCountMax extWorkas a T
                  let w ← worker extWorkas.length
                  let ⟨wfv,z,l1,l2⟩ ← withFreeingLet w f a z l1 l2
                  let ⟨conz,resz,l1,l2⟩ ← embedBackRWMain l1 l2 thmData fold empty? intersect union difference empty sConstr locConstr revCountMax (wfv :: extWorkas) z T
                  let res ← mergeOccsThree2 l1 l2 embedBackData.eq resf resa resz
                  let res := mergeOnIndSpe
                    (fun x y => x.foldl y (fun x y R => .cons x y R))
                    (fun x => .cons x .yes extWorkas .nil )
                    res (lISO here)
                  let locConstr := union conHere <| union (union conf cona) conz
                  return ⟨locConstr,res,l1,l2⟩
            | .proj stru i maj =>
                  let real ← mkProjFn! l1 l2 stru i maj
                  embedBackRWMain l1 l2 thmData fold empty? intersect union difference empty sConstr locConstr revCountMax extWorkas real T
                  -- let ⟨con,resf,l1,l2⟩ ← embedBackRWMain l1 l2 thmData fold empty? intersect union difference empty sConstr locConstr revCountMax extWorkas f T
                  -- let res := resf.foldl .nil (fun n l R => let fix := l.foldl .nil (fun e d R => .cons e (.pro d) R) ; .cons n fix R)
                  -- let res := mergeOnIndSpe
                  --   (fun x y => x.foldl y (fun x y R => .cons x y R))
                  --   (fun x => .cons x .yes extWorkas .nil )
                  --   res (lISO here)
                  -- let locConstr := union con conHere
                  -- return ⟨locConstr,res,l1,l2⟩
            | .mdata _ f =>
                  embedBackRWMain l1 l2 thmData fold empty? intersect union difference empty sConstr locConstr revCountMax extWorkas f T
            | _ =>
              let res := mergeOnIndSpe
                    (fun x y => x.foldl y (fun x y R => .cons x y R))
                    (fun x => .cons x .yes extWorkas .nil )
                    .nil (lISO .nil)
              return ⟨conHere,res,l1,l2⟩
        if yes? != 3
        then
          mtrace  on .zero with s!"[embedBackRWMain] not here 1"
          main l1 l2 .nil empty
        else
          mtrace on .one with s!"[embedBackRWMain] here {inds} : emb via ln {← here.foldlM [] (fun _ a b => return (← a.ln.foldlM ListProd.nil (fun y z w => return .cons y (← PpExpr z l1 l2) w)) :: b)}"
          main l1 l2 here inds

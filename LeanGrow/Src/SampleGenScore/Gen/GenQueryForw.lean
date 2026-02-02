
/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import LeanGrow.Src.SampleGenScore.Gen.Types



open Lean Meta

variable {IndexColType : Type}



namespace PaIn


@[specialize, inline]
private def merge1
  (intersect : IndexColType → IndexColType → IndexColType) (empty? : IndexColType → Bool)
  (start : ListProd IndexColType IndexColType)
  (L R : ListProd IndexColType IndexColType)
  : MetaM (ListProd IndexColType IndexColType):=
  let rec @[specialize] comp (done : ListProd IndexColType IndexColType) (l r : IndexColType) : (ListProd IndexColType IndexColType) → MetaM (ListProd IndexColType IndexColType)
    | .nil => return done
    | .cons nx1 nx2 more => do
        let I1 := intersect nx1 l
        if empty? I1
        then comp done l r more
        else
          let I2 := intersect nx2 r
          if empty? I2
          then comp done l r more
          else
            comp (.cons I1 I2 done) l r more
  let rec @[specialize] go (done : ListProd IndexColType IndexColType) : (ListProd IndexColType IndexColType) → MetaM (ListProd IndexColType IndexColType)
    | .nil =>
      return done
    | .cons l r more => do
        let nx := (← comp .nil l r R).foldl done (fun x y R => .cons x y R)
        go nx more
  go start L


@[specialize, inline]
private def merge2 {α : Type _} (eq : α → α → Bool)
  (start : ListProd IndexColType IndexColType)
  (L R : ListProd IndexColType α)
  : ListProd IndexColType IndexColType :=
  let rec @[specialize] go (done : ListProd IndexColType IndexColType)
    : ListProd IndexColType α → ListProd IndexColType IndexColType
    | .nil => done
    | .cons nx1 nx2 more =>
        match L.find? (fun _ y => eq y nx2) with
        | .none => .nil
        | .some x _ => go (.cons x nx1 done) more
  go start R


@[specialize, inline]
private def merge2'
  (start : ListProd IndexColType IndexColType)
  (L R : CTrie IndexColType)
  : ListProd IndexColType IndexColType :=
  R.fold start (fun n i res =>
    match L.find? n with
    | .none => res
    | .some I => .cons I i res
    )


@[specialize,inline]
private def merge3 {α : Type _}
  (start : ListProd IndexColType IndexColType)
  (L R : ListProd IndexColType α) (eq : α → α → MetaM Bool)
  : MetaM <| ListProd IndexColType IndexColType :=
  let rec @[specialize] go (done : ListProd IndexColType IndexColType)
    : ListProd IndexColType α → MetaM (ListProd IndexColType IndexColType)
    | .nil => return done
    | .cons nx1 nx2 more =>
        L.foldlMcps (false,done) (fun x y s@(_,D) q => do
          if !(← eq y nx2)
          then q s
          else q (true, .cons x nx1 D)
          ) (fun (seen?, ndone) =>
            if seen?
            then go ndone more
            else return .nil)
  go start R



@[specialize, inline]
private def merge4
  (intersect difference : IndexColType → IndexColType → IndexColType) (empty? : IndexColType → Bool)
  (start : ListProd IndexColType IndexColType)
  (L R : ListProd IndexColType IndexColType)
  : MetaM (ListProd IndexColType IndexColType):=
  let rec @[specialize] comp (done : ListProd IndexColType IndexColType) (lrem rrem l r : IndexColType) : (ListProd IndexColType IndexColType) → MetaM (ListProd IndexColType IndexColType)
    | .nil =>
        if empty? lrem || empty? rrem
        then return done
        else return .cons lrem rrem done
    | .cons nx1 nx2 more => do
        let I1 := intersect nx1 l
        if empty? I1
        then comp done lrem rrem  l r more
        else
          let I2 := intersect nx2 r
          if empty? I2
          then comp done lrem rrem  l r more
          else
            let lrem := difference lrem I1
            let rrem := difference rrem I2
            comp (.cons I1 I2 done) lrem rrem l r more
  let rec @[specialize] go (done : ListProd IndexColType IndexColType) : (ListProd IndexColType IndexColType) → MetaM (ListProd IndexColType IndexColType)
    | .nil =>
      return done
    | .cons l r more => do
        let nx := (← comp .nil l r l r R).foldl done (fun x y R => .cons x y R)
        go nx more
  go start L




/-- Q is ltx, l is hyps with lnodes-/
@[specialize, inline]
partial def genQueryForwIncludeCore [Repr IndexColType]
  (intersect difference : IndexColType → IndexColType → IndexColType) (empty? : IndexColType → Bool)
  (l1 : LocalContext) (l2 : LocalInstances) (Q l : PaIn IndexColType)
  : MetaM <| ListProd IndexColType IndexColType :=
    let rec @[specialize] go (Q l : PaIn IndexColType) : MetaM <| ListProd IndexColType IndexColType :=
      do -- trace set Tracing.Flags.none in do
      match Q, l with
      | _, .dead =>
          mtrace on .zero with s!"[genQueryForwIncludeCore] l is dead"
          return .nil
      | .dead, _=>
          mtrace on .zero with s!"[genQueryForwIncludeCore] Q is dead"
          return .nil
      | .br fvars _ bvars sorts consts lits apf apa api laf laa lai alf ala ali lef lea lez lei projs proofsOf proofs,
        .br fvars' mvars' bvars' sorts' consts' lits' apf' apa' api' laf' laa' lai' alf' ala' ali' lef' lea' lez' lei' projs' proofsOf' proofs' =>
          do
          if (empty? api && !(empty? api')) || (empty? lai && !(empty? lai')) || (empty? ali && !(empty? ali')) || (empty? lei && !(empty? lei'))
          then
            mtrace on .zero with s!"[genQueryForwIncludeCore] early return due to missing branch : api {repr api} api' {repr api'} ; lai {repr lai} lai' {repr lai'} ; ali {repr ali} ali' {repr ali'} ; lei {repr lei} lei' {repr lei'}"
            return .nil
          else
            let QB := Q.buildNoLoBvCore 0 id intersect empty?
            let IL : ListProd IndexColType IndexColType := ← do
              let R ← mvars'.foldM .nil (fun nb inds R => do
                      let mv := Expr.mvar ⟨(String.fromUTF8! nb).toName⟩
                      let R ← QB.foldlM R (fun e qinds R => do
                        mtrace on .zero with s!"[genQueryForwIncludeCore] defeq e {← ppExpr e} vs lnode {repr mv} of type {← ppExpr <| ← inferType mv}"
                        match ← defEqWiMv mv e l1 l2 with
                        | .none =>
                            mtrace on .zero with s!"[genQueryForwIncludeCore] negative defeq"
                            return R
                        | .some .. =>
                            mtrace on .zero with s!"[genQueryForwIncludeCore] positive defeq"
                            return .cons qinds inds R
                        )
                      return R
                )
              return R
            mtrace on .zero with s!"[genQueryForwIncludeCore] IL : {repr IL}"
            let IG := merge2' IL fvars fvars'
            mtrace on .zero with s!"[genQueryForwIncludeCore] IG : {repr IG}"
            let IB := merge2 (· == ·) IG bvars bvars'
            mtrace on .zero with s!"[genQueryForwIncludeCore] IB : {repr IB}"
            let IS ← merge3 IB sorts sorts' (fun u u' => do
              match ← defEqWiMv (.sort u) (.sort u') l1 l2 with
              | .none => return false
              | .some ..=> return true
              )
            mtrace on .zero with s!"[genQueryForwIncludeCore] IS : {repr IS}"
            let IC : ListProd IndexColType IndexColType := ← do
              (CTrie.intersect_val_pairs' consts consts').foldlM IS (fun cs cs' R => do
                merge3 R cs cs' (fun lv lv' => do
                  -- ugly but can't be bothered to get clean version
                  for u in lv, u' in lv' do
                    match ← defEqWiMv (.sort u) (.sort u') l1 l2 with
                    | .none => return false
                    | .some .. => continue
                  return true
                  ))
            mtrace on .zero with s!"[genQueryForwIncludeCore] IC : {repr IC}"
            let II := merge2 (· == ·) IC lits lits'
            mtrace on .zero with s!"[genQueryForwIncludeCore] II : {repr II}"
            let Iap := ← do if !(empty? api') then merge1 intersect empty? II (← go apf apf') (← go apa apa') else return .nil
            mtrace on .zero with s!"[genQueryForwIncludeCore] Iap : {repr Iap}"
            let Ila := ← do if !(empty? lai') then merge1 intersect empty? Iap (← go laf laf') (← go laa laa') else return .nil
            mtrace on .zero with s!"[genQueryForwIncludeCore] Ila : {repr Ila}"
            let Ial := ← do if !(empty? ali') then merge1 intersect empty? Ila (← go alf alf') (← go ala ala') else return .nil
            mtrace on .zero with s!"[genQueryForwIncludeCore] Ial : {repr Ial}"
            let Ile := ← do if !(empty? lei') then merge1 intersect empty? Ial (← merge1 intersect empty? .nil (← go lef lef') (← go lea lea')) (← go lez lez') else return .nil
            mtrace on .zero with s!"[genQueryForwIncludeCore] Ile : {repr Ile}"
            let IP : ListProd IndexColType IndexColType := ← do
              (CTrie.intersect_val_pairs' projs projs').foldlM Ile (fun cs cs' R => do
                cs.foldlM R (fun _ (i,p1) R => do
                  cs'.foldlM R (fun _ (j,p2) R => do
                    if i == j
                    then
                      let res ← go p1 p2
                      return res.foldl R (fun x y w => .cons x y w)
                    else
                      return R
                    )))
            mtrace on .zero with s!"[genQueryForwIncludeCore] IP : {repr IP}"
            -- ↓ is so that we assign lnodes inside proofs, in a way that matching IndexColTypes don't get duplicated
            let final ← merge4 intersect difference empty? IP (← go proofsOf proofsOf') (← go proofs proofs')
            mtrace on .zero with s!"[genQueryForwIncludeCore] final : {repr final}"
            return final
    go Q l

#check 1

#check List.queryPass
#check List.queryPassM


@[specialize, inline]
partial def genQueryForwWiLoadMain [Repr IndexColType]
  (intersect difference : IndexColType → IndexColType → IndexColType) (empty? : IndexColType → Bool)
  (l1 : LocalContext) (l2 : LocalInstances)
  (sampleName : Name) (types : Array Expr)
  (Q : PaIn IndexColType)
  {valType : Type _} (scores : SetTrie valType (PaIn IndexColType))
  : MetaM (Prod3 (List valType) (List (SetTrie valType (PaIn IndexColType))) Bool) :=
    do
    let _ ← mkLevelMVarOfName (.num sampleName 0)
    let mut i := 0
    for T in types do
      let _ ← mkMvarStdWiCoI (.num sampleName i) T l1 l2
      i := i+1
    List.queryPassNotifyM
      (fun x y => do
          match ← genQueryForwIncludeCore intersect difference empty? l1 l2 x y with
          | .nil => return false
          | _ => return true)
      Q [scores]


@[specialize, inline]
partial def genQueryForwNoLoadMain [Repr IndexColType]
  (intersect difference : IndexColType → IndexColType → IndexColType) (empty? : IndexColType → Bool)
  (l1 : LocalContext) (l2 : LocalInstances)
  (Q : PaIn IndexColType)
  {valType : Type _} (scores : SetTrie valType (PaIn IndexColType))
  : MetaM (Prod3 (List valType) (List (SetTrie valType (PaIn IndexColType))) Bool) :=
    List.queryPassNotifyM
      (fun x y => do
          match ← genQueryForwIncludeCore intersect difference empty? l1 l2 x y with
          | .nil => return false
          | _ => return true)
      Q [scores]

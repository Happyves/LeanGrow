
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



@[specialize]
private def merge3 {α : Type _}
  (start : ListProd IndexColType IndexColType)
  (L R : ListProd IndexColType α) (eq : α → α → MetaM Bool)
  : MetaM <| ListProd IndexColType IndexColType :=
  let rec @[specialize] go (done : ListProd IndexColType IndexColType)
    : ListProd IndexColType α → MetaM (ListProd IndexColType IndexColType)
    | .nil => return done
    | .cons nx1 nx2 more =>
        L.foldlMcps done (fun x y D q => do
          if ← eq y nx2
          then q (.cons x nx1 D)
          else q D
          ) (fun ndone =>
            go ndone more)
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


#check 1

/-- Q is ltx, l is hyps with lnodes-/
@[specialize, inline]
partial def genQueryForwInterCore [Repr IndexColType]
  (intersect difference : IndexColType → IndexColType → IndexColType) (empty? : IndexColType → Bool)
  (l1 : LocalContext) (l2 : LocalInstances) (Q l : PaIn IndexColType)
  : MetaM <| ListProd IndexColType IndexColType :=
    do
    mtracing
    let rec @[specialize] go (Q l : PaIn IndexColType) : MetaM <| ListProd IndexColType IndexColType :=
      do -- trace set Tracing.Flags.none in do
      match Q, l with
      | _, .dead =>
          mtrace on .zero with s!"[genQueryForwInterCore] l is dead"
          return .nil
      | .dead, _=>
          mtrace on .zero with s!"[genQueryForwInterCore] Q is dead"
          return .nil
      | .br fvars _ bvars sorts consts lits apf apa api laf laa lai alf ala ali lef lea lez lei projs proofsOf proofs,
        .br fvars' mvars' bvars' sorts' consts' lits' apf' apa' api' laf' laa' lai' alf' ala' ali' lef' lea' lez' lei' projs' proofsOf' proofs' =>
          do
          let IL : ListProd IndexColType IndexColType := ← do
            match mvars' with
            | .leaf =>
              return .nil
            | _ =>
              let QB ← Q.buildNoLoBvCore l1 l2 0 id intersect empty?
              let R ← mvars'.foldM (ListProd.nil : ListProd IndexColType IndexColType) (fun nb inds R => do
                let mv := Expr.mvar ⟨(String.fromUTF8! nb).toName⟩
                let R ← QB.foldlM R (fun e qinds R => do
                  mtrace on .zero with s!"[genQueryForwInterCore] defeq e {← ppExpr e} vs lnode {repr mv} of type {← ppExpr <| ← inferType mv}"
                  let welab ← defEqWiMv mv e l1 l2
                  match welab with
                  | .none =>
                      mtrace on .zero with s!"[genQueryForwInterCore] negative defeq"
                      return R
                  | .some .. =>
                      mtrace on .zero with s!"[genQueryForwInterCore] positive defeq"
                      return ListProd.cons qinds inds R
                  )
                return R
              )
              return R
          mtrace on .zero with s!"[genQueryForwInterCore] IL : {repr IL}"
          let IG := (CTrie.intersect_val_pairs' fvars fvars' ).foldl IL ListProd.cons -- debt : let-decls not unflded ...
          mtrace on .zero with s!"[genQueryForwInterCore] IG : {repr IG}"
          let IB := merge2 (· == ·) IG bvars bvars'
          mtrace on .zero with s!"[genQueryForwInterCore] IB : {repr IB}"
          let IS ← merge3 IB sorts sorts' (fun u u' => do
            match ← defEqWiMv (.sort u) (.sort u') l1 l2 with
            | .none => return false
            | .some ..=> return true
            )
          mtrace on .zero with s!"[genQueryForwInterCore] IS : {repr IS}"
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
          mtrace on .zero with s!"[genQueryForwInterCore] IC : {repr IC}"
          let II := merge2 (· == ·) IC lits lits'
          mtrace on .zero with s!"[genQueryForwInterCore] II : {repr II}"
          let Iap := ← merge1 intersect empty? II (← go apf apf') (← go apa apa')
          mtrace on .zero with s!"[genQueryForwInterCore] Iap : {repr Iap}"
          let Ila := ← merge1 intersect empty? Iap (← go laf laf') (← go laa laa')
          mtrace on .zero with s!"[genQueryForwInterCore] Ila : {repr Ila}"
          let Ial := ← merge1 intersect empty? Ila (← go alf alf') (← go ala ala')
          mtrace on .zero with s!"[genQueryForwInterCore] Ial : {repr Ial}"
          let Ile := ← merge1 intersect empty? Ial (← merge1 intersect empty? .nil (← go lef lef') (← go lea lea')) (← go lez lez')
          mtrace on .zero with s!"[genQueryForwInterCore] Ile : {repr Ile}"
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
          mtrace on .zero with s!"[genQueryForwInterCore] IP : {repr IP}"
          -- ↓ is so that we assign lnodes inside proofs, in a way that matching IndexColTypes don't get duplicated
          let final ← merge4 intersect difference empty? IP (← go proofsOf proofsOf') (← go proofs proofs')
          mtrace on .zero with s!"[genQueryForwInterCore] final : {repr final}"
          return final
    go Q l

#check 1

#check List.queryPass
#check List.queryPassM


@[specialize, inline]
partial def genQueryForwWiLoadMain [Repr IndexColType]
  (intersect difference union : IndexColType → IndexColType → IndexColType) (empty? : IndexColType → Bool)
  (empty : IndexColType) (subsetOf : IndexColType → IndexColType → Bool)
  (l1 : LocalContext) (l2 : LocalInstances)
  (sampleName : Name) (types : Array Expr)
  (Q : PaIn IndexColType)
  {valType : Type _} (scores : SetTrieP valType IndexColType PaIn)
  : MetaM (Prod3 Bool (List valType) (List (SetTrieP valType IndexColType PaIn))) :=
    do
    let _ ← mkLevelMVarOfName (.num sampleName 0)
    let mut i := 0
    for T in types do
      let _ ← mkMvarStdNoCoI (.num sampleName i) T
      i := i+1
    let res ← SetTrieP.queryPassNotifyM
      (fun x y  _ => do
          let I ← genQueryForwInterCore intersect difference empty? l1 l2 x y
          let U := I.foldl empty (fun _ l U => union l U)
          return (U,())
          )
      subsetOf
      () Q scores
    return .mk res.1 res.2 res.3


@[specialize, inline]
partial def genQueryForwNoLoadMain [Repr IndexColType]
  (intersect difference union : IndexColType → IndexColType → IndexColType) (empty? : IndexColType → Bool)
  (empty : IndexColType) (subsetOf : IndexColType → IndexColType → Bool)
  (l1 : LocalContext) (l2 : LocalInstances)
  (Q : PaIn IndexColType)
  {valType : Type _} (scores : SetTrieP valType IndexColType PaIn)
  : MetaM (Prod3 Bool (List valType) (List (SetTrieP valType IndexColType PaIn))) :=
    do
    let res ← SetTrieP.queryPassNotifyM
      (fun x y  _ => do
          let I ← genQueryForwInterCore intersect difference empty? l1 l2 x y
          let U := I.foldl empty (fun _ l U => union l U)
          return (U,())
          )
      subsetOf
      () Q scores
    return .mk res.1 res.2 res.3

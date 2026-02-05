
/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import LeanGrow.Src.Data.PathIndex.Indexing
import LeanGrow.Src.Data.PathIndex.Operations
import LeanGrow.Src.Data.PathIndex.Insert
import LeanGrow.Src.SampleGenScore.Gen.Types
import LeanGrow.Src.Utils.Lean.MetaAPI

open Lean Meta

variable {IdxCollType : Type _}




/-- Will require types to have been loaded ! -/
@[specialize, inline]
def generaliseToLnodesCore [Repr IdxCollType]
  (fold : ∀ {β : Type _}, IdxCollType → (init : β) → (f : Nat → β → β) → β)
  (emptyCol : IdxCollType) (insert union: IdxCollType → IdxCollType → IdxCollType)
  (l1 : LocalContext) (l2 : LocalInstances)
  (sampleName : Name)
  (genCondition : (occWeight : Nat) → (branchWeight : Nat) → (branchDistrib : Array Nat) → (commonType : Expr) → (branchDepth : Nat) → Bool)
  -- ↑ typically : (w / totalWeigth ≥ ratio) && (T != .sort 0)
  (weights : Array Nat)
  (todo : ListProd Expr IdxCollType) (types : Array Expr) (safePaIn : PaIn IdxCollType)
  (drdepth : Nat)
  : MetaM (Prod5 (List IdxCollType) (PaIn IdxCollType) (Array Expr) LocalContext LocalInstances) :=
    do
    mtracing
    let Res ← todo.foldlM ((.mk ListProd4.nil 0 #[]) : Prod3 (ListProd4 Expr Expr IdxCollType Nat) Nat (Array Nat)) (fun e is Res => do
      let T ← InferType e l1 l2
      let W := getCPIweights fold weights is
      return .mk (.cons e T is W Res.1) (W + Res.2) (Res.3.push W)
      )
    let preprocessed := Res.1
    mtrace on .zero with (← preprocessed.foldlM s!"[generaliseToLnodesCore] preprocessed \n" (fun e T is W msg => return s!" e {← ppExpr e}\n T {← ppExpr T}\n is {repr is}\n w {W}\n" ++ msg))
    let totalWeigth := Res.2
    let distrib := Res.3
    mtrace on .zero with s!"[generaliseToLnodesCore] totalWeigth {totalWeigth}"
    let processed ← preprocessed.foldlM ListProd3.nil (fun e T is w L => do
      let (res,added?) ← L.foldlM (ListProd3.nil, false) (fun le τ W L => do
        if L.2
        then return (.cons le τ W L.1, L.2)
        else
          if (← defEqWiMv T τ l1 l2).isSome
          then return (.cons (ListProd.cons e is le) τ (w + W) L.1, true)
          else return (.cons le τ W L.1, L.2)
        )
      if added?
      then return res
      else return .cons (ListProd.cons e is .nil) T w res
      )
    mtrace on .zero with (← processed.foldlM s!"[generaliseToLnodesCore] processed \n" (fun es T W msg => return s!" es inds {repr <| es.foldl emptyCol (fun _ is R => union is R)}\n T {← ppExpr T}}\n w {W}\n" ++ msg))
    processed.foldlMcps (.mk safePaIn types [] l1 l2 : Prod5 _ _ _ _ _) (fun es T w (.mk P1 P2 P3 l1 l2) q => do
      if !(genCondition w totalWeigth distrib T drdepth)
      then
        mtrace on .zero with s!"[generaliseToLnodesCore] type ↓ not generalised, adding terms\n {← ppExpr T}"
        es.foldlMcps (.mk P1 l1 l2 : Prod3 _ _ _) (fun e is (.mk rP l1 l2) q1 => do
          q1 <| ← rP.insertMulti l1 l2 e is emptyCol insert
          ) <| fun | .mk nP l1 l2 => do q (.mk nP P2 P3 l1 l2)
      else
        mtrace on .zero with s!"[generaliseToLnodesCore] type ↓ will be generalised\n {← ppExpr T}"
        let ws := T.getWorkerFVarIds.toArray
        let .mk T l1 l2 ← (do
          if ws.isEmpty
          then return (.mk T l1 l2 : Prod3 ..)
          else
            mtrace on .zero with s!"[generaliseToLnodesCore] abstracted loose bvars (workers) to {← ppExpr T}"
            T.abstractLetFvarAll l1 l2 ws)
        let mut i := 0
        let mut found? := false
        for τ in P2 do
          mtrace on .one with s!"[generaliseToLnodesCore] comparing to {← ppExpr τ}"
          if (← defEqWiMv τ T l1 l2).isSome
          then
            mtrace on .zero with s!"[generaliseToLnodesCore] type matches known type of index {i}"
            found? := true
            break
          else
            i := i+1
        if found?
        then
          let ln := Expr.mvar ⟨.num sampleName i⟩
          let toadd := (mkAppN ln (ws.map Expr.fvar))
          let addinds := es.foldl emptyCol (fun _ is R => union is R)
          let .mk nP l1 l2 ← P1.insertMulti l1 l2 toadd addinds emptyCol insert
          q (.mk nP P2 (addinds :: P3) l1 l2)
        else
          mtrace on .zero with s!"[generaliseToLnodesCore] type not found adding it as new type of index {i}"
          let ln ← mkMvarStdNoCoE (.num sampleName i) T -- i is types.size
          let types := P2.push T
          let toadd := (mkAppN ln (ws.map Expr.fvar))
          let addinds := es.foldl emptyCol (fun _ is R => union is R)
          let .mk nP l1 l2 ← P1.insertMulti l1 l2 toadd addinds emptyCol insert
          q (.mk nP types (addinds :: P3) l1 l2)
      ) <| fun | .mk P1 P2 P3 l1 l2 => return .mk P3 P1 P2 l1 l2


@[specialize, inline]
def getFreqPatInds
  (fold : ∀ {β : Type _}, IdxCollType → (init : β) → (f : Nat → β → β) → β)
  (weights : Array Nat)
  (freqCondition : (occWeight : Nat) → (branchWeight : Nat) → (branchDistrib : Array Nat) → (branchDepth : Nat) → Bool)
  -- ↑ typically :  W / normalize ≥ ratio
  {α : Type _} (next :  ListProd IdxCollType α)
  (normalize : Nat) (branchDistrib : Array Nat) (drdepth : Nat)
  (start : List IdxCollType) : List IdxCollType :=
    next.foldl (start) (fun is _ R =>
      let W := getCPIweights fold weights is
      if freqCondition W normalize branchDistrib drdepth
      then (is :: R)
      else R
      )



@[specialize, inline]
def getFreqPatIndsCT
  (fold : ∀ {β : Type _}, IdxCollType → (init : β) → (f : Nat → β → β) → β)
  (weights : Array Nat)
  (freqCondition : (occWeight : Nat) → (branchWeight : Nat) → (branchDistrib : Array Nat) → (branchDepth : Nat) → Bool)
  -- ↑ typically :  W / normalize ≥ ratio
  {α : Type _} (next :  CTrie (ListProd IdxCollType α))
  (normalize : Nat) (branchDistrib : Array Nat) (drdepth : Nat)
  (start : List IdxCollType) : List IdxCollType :=
    (next.fold start (fun _ D R =>
      getFreqPatInds fold weights freqCondition D normalize branchDistrib drdepth R
      ))

@[specialize, inline]
def getFreqPatIndsCT'
  (fold : ∀ {β : Type _}, IdxCollType → (init : β) → (f : Nat → β → β) → β)
  (weights : Array Nat)
  (freqCondition : (occWeight : Nat) → (branchWeight : Nat) → (branchDistrib : Array Nat) → (branchDepth : Nat) → Bool)
  -- ↑ typically :  W / normalize ≥ ratio
  (next :  CTrie (IdxCollType))
  (normalize : Nat) (branchDistrib : Array Nat) (drdepth : Nat)
  (start : List IdxCollType) : List IdxCollType :=
    (next.fold start (fun _ is R =>
      let W := getCPIweights fold weights is
      if freqCondition W normalize branchDistrib drdepth
      then (is :: R)
      else R
      ))


@[specialize, inline]
def getFreqPatInds2
  (fold : ∀ {β : Type _}, IdxCollType → (init : β) → (f : Nat → β → β) → β)
  (intersect : IdxCollType → IdxCollType → IdxCollType)
  (weights : Array Nat)
  (freqCondition : (occWeight : Nat) → (branchWeight : Nat) → (branchDistrib : Array Nat) → (branchDepth : Nat) → Bool)
  -- ↑ typically :  W / normalize ≥ ratio
  (fL fR:  List IdxCollType)
  (normalize : Nat) (branchDistrib : Array Nat) (drdepth : Nat)
  (start : List IdxCollType) : List IdxCollType :=
    fL.foldl (fun res lis =>
      fR.foldl (fun res ris =>
        let I := intersect lis ris
        let W := getCPIweights fold weights I
        if freqCondition W normalize branchDistrib drdepth
          then I :: res
          else res
      ) res ) start



@[specialize, inline]
def getFreqPatInds3
  (fold : ∀ {β : Type _}, IdxCollType → (init : β) → (f : Nat → β → β) → β)
  (intersect : IdxCollType → IdxCollType → IdxCollType) (empty? : IdxCollType → Bool)
  (weights : Array Nat)
  (freqCondition : (occWeight : Nat) → (branchWeight : Nat) → (branchDistrib : Array Nat) → (branchDepth : Nat) → Bool)
  -- ↑ typically : W / normalize ≥ ratio
  (L R Z:  List IdxCollType)
  (normalize : Nat) (branchDistrib : Array Nat) (drdepth : Nat)
  (start : List IdxCollType) : List IdxCollType :=
    L.foldl (fun res lis =>
      R.foldl (fun res ris =>
        let I1 := intersect lis ris
        if empty? I1
        then res
        else
          Z.foldl (fun res zis =>
            let I2 := intersect I1 zis
            let W := getCPIweights fold weights I2
            if freqCondition W normalize branchDistrib drdepth
            then I2 :: res
            else res) res
      ) res ) start



@[specialize, inline]
partial def PaIn.dedup
  (insert : Nat → IdxCollType → IdxCollType)
  (union : IdxCollType → IdxCollType → IdxCollType) (empty : IdxCollType)
  (size : IdxCollType → Nat) (contains : Nat → IdxCollType → Bool)
  (fold : ∀ {β : Type _}, IdxCollType → (init : β) → (f : Nat → β → β) → β)
  (T : PaIn IdxCollType) (weights : Array Nat) (toMerge : List IdxCollType)
  : MetaM (Prod3 (PaIn IdxCollType) (Array Nat) (RBMap Nat Nat instOrdNat.compare)) :=
  let toReInd := toMerge.foldl union empty
  let off := weights.size - size toReInd
  let A := Array.replicate (off + toMerge.length) (0 : Nat)
  let .mk trans A _ : Prod3 (RBMap Nat Nat instOrdNat.compare) (Array Nat) Nat :=
    weights.size.fold (fun i _ P@(.mk rb A I) =>
      if contains i toReInd
      then P
      else (.mk (rb.insert i I) (A.set! I (weights[i]!)) (I+1))) (.mk {} A 0)
  let (trans,A,_) := toMerge.foldl (fun (rb,A, i) l =>
    (fold l rb (fun I rb => rb.insert I i ) , A.set! i (getCPIweights fold weights l), i+1)) (trans,A,off)
  let go (n : Nat) : Nat :=
    match trans.find? n with
    | .none => n
    | .some x => x
  let rec @[specialize, inline] fixInds (is : IdxCollType) : IdxCollType := fold is empty (fun n Is => insert (go n) Is)
  let rec @[specialize] late : (PaIn IdxCollType) → (PaIn IdxCollType)
    | .dead => .dead
    | .br fvars mvars bvars sorts consts lits apf apa api laf laa lai alf ala ali lef lea lez lei projs proofsOf proofs =>
        let nfvars := fvars.map (fun is => fixInds is)
        let nmvars := mvars.map (fun is => fixInds is)
        let nbvars := bvars.mapTR (fun is x => (fixInds is,x))
        let nsorts := sorts.mapTR (fun is x => (fixInds is,x))
        let nconsts := consts.map (fun L => .some (L.mapTR (fun is x => (fixInds is,x))))
        let nlits := lits.mapTR (fun is x => (fixInds is,x))
        let napf := late apf
        let napa := late apa
        let napi := fixInds api
        let nlaf := late laf
        let nlaa := late laa
        let nlai := fixInds lai
        let nalf := late alf
        let nala := late ala
        let nali := fixInds ali
        let nlef := late lef
        let nlea := late lea
        let nlez := late lez
        let nlei := fixInds lei
        let nprojs := projs.map (fun L => .some (L.mapTR (fun is (x,t) => (fixInds is,x, late t))))
        let nproofsOf := late proofsOf
        let nproofs := late proofs
        .br nfvars nmvars nbvars nsorts nconsts nlits napf napa napi nlaf nlaa nlai nalf nala nali nlef nlea nlez nlei nprojs nproofsOf nproofs
  return .mk (late T) A trans



@[specialize]
def PaIn.getTotalDistrib
  (empty : IdxCollType) (union : IdxCollType → IdxCollType → IdxCollType)
  (fold : ∀ {β : Type _}, IdxCollType → (init : β) → (f : Nat → β → β) → β)
  (weights : Array Nat)
  (T : PaIn IdxCollType) : Nat × Array Nat :=
  match T with
  | .dead => (0, #[])
  | .br fvars mvars bvars sorts consts lits _ _ api _ _ lai _ _ ali _ _ _ lei projs proofsOf _ =>
      let is := ((0 : Nat), #[])
      let is := fvars.fold is (fun _ is (W,d) =>
        let w := getCPIweights fold weights is
        (W + w, d.push w))
      let is := mvars.fold is (fun _ is (W,d) =>
        let w := getCPIweights fold weights is
        (W + w, d.push w))
      let is := bvars.foldl is (fun is _ (W,d) =>
        let w := getCPIweights fold weights is
        (W + w, d.push w))
      let is := sorts.foldl is (fun is _ (W,d) =>
        let w := getCPIweights fold weights is
        (W + w, d.push w))
      let is := (consts.fold is (fun _ D is =>
                  (D.foldl is (fun is _ (W,d) =>
                    let w := getCPIweights fold weights is
                    (W + w, d.push w)))))
      let (W,d) := lits.foldl is (fun is _ (W,d) =>
        let w := getCPIweights fold weights is
        (W + w, d.push w))
      let w := getCPIweights fold weights api
      let W := W + w
      let d := d.push w
      let w := getCPIweights fold weights lai
      let W := W + w
      let d := d.push w
      let w := getCPIweights fold weights ali
      let W := W + w
      let d := d.push w
      let w := getCPIweights fold weights lei
      let W := W + w
      let d := d.push w
      let (W,d) := (projs.fold (W,d) (fun _ D is =>
                  (D.foldl is (fun is _ (W,d) =>
                    let w := getCPIweights fold weights is
                    (W + w, d.push w)))))
      let (pw, pd) := (proofsOf.getTotalDistrib empty union fold weights)
      let W := W + pw
      let d := d ++ pd
      (W,d)

#check 1

@[inline, specialize]
def painBuildExtendStack
  (intersect difference : IdxCollType → IdxCollType → IdxCollType) (empty? : IdxCollType → Bool)
  (l1 : LocalContext) (l2 : LocalInstances)
  (stack : ListProd IdxCollType (List FVarId)) (bindas : ListProd Expr IdxCollType) :
  MetaM (Prod3 (ListProd IdxCollType (List FVarId)) LocalContext LocalInstances) :=
  let rec @[specialize] inner (T : Expr) (inds : IdxCollType)
    (toSplit new : ListProd IdxCollType (List FVarId)) (l1 : LocalContext) (l2 : LocalInstances)
    : ListProd IdxCollType (List FVarId) → MetaM (Prod4 (ListProd IdxCollType (List FVarId)) (ListProd IdxCollType (List FVarId)) LocalContext LocalInstances)
    | .nil => do
        if empty? inds
        then return .mk toSplit new l1 l2
        else
          let w ← worker 0
          let .mk wt l1 l2 ← WithLocalDecl w T l1 l2
          let new := .cons inds [wt] new
          return .mk toSplit new l1 l2
    | .cons sinds workas more => do
        let I := intersect sinds inds
        if empty? I
        then
          inner T inds (.cons sinds workas toSplit) new l1 l2 more
        else
          let w ← worker workas.length
          let .mk wt l1 l2 ← WithLocalDecl w T l1 l2
          let new := .cons I (wt :: workas) new
          let D1 := difference sinds inds
          let D2 := difference inds sinds
          let toSplit := if empty? D1 then toSplit else .cons D2 workas toSplit
          if empty? D2
          then return .mk (toSplit.foldl more ListProd.cons) new l1 l2
          else inner T D2 toSplit new l1 l2 more
  let rec @[specialize] outer
    (old new : ListProd IdxCollType (List FVarId)) (l1 : LocalContext) (l2 : LocalInstances)
    : ListProd Expr IdxCollType → MetaM (Prod3 (ListProd IdxCollType (List FVarId)) LocalContext LocalInstances)
    | .nil => return .mk new l1 l2
    | .cons T inds more => do
        let .mk old new l1 l2 ← inner T inds .nil new l1 l2 old
        outer old new l1 l2 more
  outer stack .nil l1 l2 bindas


@[specialize, inline]
partial def generalizePaInCore [Repr IdxCollType]
  (fold : ∀ {β : Type _}, IdxCollType → (init : β) → (f : Nat → β → β) → β) (empty : IdxCollType)
  (insert intersect union difference : IdxCollType → IdxCollType → IdxCollType)
  (empty? : IdxCollType → Bool)
  (l1 : LocalContext) (l2 : LocalInstances)
  (genCondition : (occWeight : Nat) → (branchWeight : Nat) → (branchDistrib : Array Nat) → (commonType : Expr) → (branchDepth : Nat) → Bool)
  (freqCondition : (occWeight : Nat) → (branchWeight : Nat) → (branchDistrib : Array Nat) → (branchDepth : Nat) → Bool)
  (sampleName : Name)
  (T : PaIn IdxCollType) (weights : Array Nat) (types : Array Expr)
  : MetaM (Prod5 (List IdxCollType) (PaIn IdxCollType) (Array Expr) LocalContext LocalInstances) :=
  do
  mtracing
  let rec @[specialize] go (l1 : LocalContext) (l2 : LocalInstances)
    (stack : ListProd IdxCollType (List FVarId)) (T : PaIn IdxCollType) (types : Array Expr) (drdepth : Nat)
    : MetaM (Prod5 (List IdxCollType) (PaIn IdxCollType) (Array Expr) LocalContext LocalInstances) :=
    match T with
    | .dead => return .mk [] T types l1 l2
    | .br poiT mvars bvars sorts consts lits apf apa api laf laa lai alf ala ali lef lea lez lei projs proofsOf proofs =>
        do
        let branchInds := T.getIndices empty union
        let (normalize, distrib) := T.getTotalDistrib empty union fold weights
        let (PL) := getFreqPatIndsCT' fold weights freqCondition mvars normalize distrib drdepth []
        let (PB) := getFreqPatInds fold weights freqCondition bvars normalize distrib drdepth PL
        let (PS) := getFreqPatInds fold weights freqCondition sorts normalize distrib drdepth PB
        let PC := getFreqPatIndsCT fold weights freqCondition consts normalize distrib drdepth PS
        let ( PLi) := getFreqPatInds fold weights freqCondition lits normalize distrib drdepth PC
        let .mk Papf apf types l1 l2 ← go l1 l2 stack apf types (drdepth + 1)
        let .mk Papa apa types l1 l2 ← go l1 l2 stack apa types (drdepth + 1)
        let Pap := getFreqPatInds2 fold intersect weights freqCondition Papf Papa normalize distrib drdepth PLi
        let .mk Plaf laf types l1 l2 ← go l1 l2 stack laf types (drdepth + 1)
        let bindas ← laf.buildMultiCore l1 l2 stack 0 id intersect empty?
        let .mk stackLA l1 l2 ← painBuildExtendStack intersect difference empty? l1 l2 stack bindas
        -- todo ↑ debug stack wrt sus ... ↓ don't forget to increase depths in calls to go under binders as in ↓
        let .mk Plaa laa types l1 l2 ← go l1 l2 stackLA laa types (drdepth + 1)
        let Pla := getFreqPatInds2 fold intersect weights freqCondition Plaf Plaa normalize distrib drdepth Pap
        let .mk Palf alf types l1 l2 ← go l1 l2 stack alf types (drdepth + 1)
        let bindas ← alf.buildMultiCore l1 l2 stack 0 id intersect empty?
        let .mk stackAL l1 l2 ← painBuildExtendStack intersect difference empty? l1 l2 stack bindas
        let .mk Pala ala types l1 l2 ← go l1 l2 stackAL ala types (drdepth + 1)
        let Pal := getFreqPatInds2 fold intersect weights freqCondition Palf Pala normalize distrib drdepth Pla
        let .mk Plef lef types l1 l2 ← go l1 l2 stack lef types (drdepth + 1)
        let .mk Plea lea types l1 l2 ← go l1 l2 stack lea types (drdepth + 1)
        let bindas ← lef.buildMultiCore l1 l2 stack 0 id intersect empty?
        let .mk stackLe l1 l2 ← painBuildExtendStack intersect difference empty? l1 l2 stack bindas
        let .mk Plez lez types l1 l2 ← go l1 l2 stackLe lez types (drdepth + 1)
        let Ple := getFreqPatInds3 fold intersect empty? weights freqCondition Plef Plea Plez normalize distrib drdepth Pal
        let ((.mk (finalFreqPatInds,types) l1 l2), projs) ← projs.foldMapM (.mk (Ple,types) l1 l2 : Prod3 ..) ( fun data (.mk S l1 l2) => do
              data.foldlMcps (.mk ((.nil : ListProd IdxCollType (Nat × PaIn IdxCollType)), S) l1 l2 : Prod3 ..) (fun pinds  (pidx,nx) (.mk (pbr,S) l1 l2) q1 => do
                let .mk Ploc loc types l1 l2 ← go l1 l2 stack nx types (drdepth + 1)
                q1 (.mk (.cons pinds (pidx, loc) pbr, (Ploc ++ S.1, types)) l1 l2)
                  ) <| fun | .mk (pbr,S) l1 l2 => return ((.mk S l1 l2), .some pbr)
          )
        mtrace on .zero with s!"[generaliseToLnodesCore] finalFreqPatInds {repr finalFreqPatInds}"
        let joinedFreqPatInds := finalFreqPatInds.foldl union empty
        let toGenInds := difference branchInds joinedFreqPatInds
        let recBr :=
          PaIn.br poiT mvars bvars sorts consts lits apf apa api laf laa lai alf ala ali lef lea lez lei projs proofsOf proofs
        -- mtrace on .one with s!"[generaliseToLnodesCore] at branch:\n {repr <| ← (T.buildMultiCore stack 0 id intersect empty?).foldlM ListProd.nil (fun e is R => return .cons s!"{(← ppExpr e)}" is R)}"
        mtrace on .one with s!"[generaliseToLnodesCore] recuresion yielded:\n {repr <| ← (← recBr.buildMultiCore l1 l2 stack 0 id intersect empty?).foldlM ListProd.nil (fun e is R => return .cons s!"{(← ppExpr e)}" is R)}"
        let toGenVals ← recBr.buildMultiCore l1 l2 stack 0 (fun x => intersect x toGenInds) intersect empty?
        mtrace on .zero with s!"[generaliseToLnodesCore] terms to generalize:\n {repr <| ← toGenVals.foldlM ListProd.nil (fun e is R => return .cons s!"{(← ppExpr e)}" is R)}"
        let .mk genIds genP types l1 l2 ← generaliseToLnodesCore
          fold empty insert union l1 l2 sampleName genCondition
          weights toGenVals types .dead drdepth
        mtrace on .zero with s!"[generaliseToLnodesCore] genIds {repr genIds}"
        mtrace on .one with s!"[generaliseToLnodesCore] genP:\n {repr <| ← (← genP.buildMultiCore l1 l2 stack 0 id intersect empty?).foldlM ListProd.nil (fun e is R => return .cons s!"{(← ppExpr e)}" is R)}"
        let freqP := recBr.deleteOfInds toGenInds difference empty empty?
        mtrace on .one with s!"[generaliseToLnodesCore] freqP:\n {repr <| ← (← freqP.buildMultiCore l1 l2 stack 0 id intersect empty?).foldlM ListProd.nil (fun e is R => return .cons s!"{(← ppExpr e)}" is R)}"
        let newP := PaIn.merge union empty freqP genP
        mtrace on .one with s!"[generaliseToLnodesCore] merged to:\n {repr <| ← (← newP.buildMultiCore l1 l2 stack 0 id intersect empty?).foldlM ListProd.nil (fun e is R => return .cons s!"{(← ppExpr e)}" is R)}"
        let definiteFreqPatInds := genIds.foldl (fun R is =>
            let W := getCPIweights fold weights is
            if freqCondition W normalize distrib drdepth
            -- so we compare the weight of the generalized pattern to the old distrib
            then is :: R else R
            ) finalFreqPatInds
        return .mk definiteFreqPatInds newP types l1 l2
  go l1 l2 .nil T types 0

#check 1




partial def getLiveLnodes (T : PaIn IdxCollType) : UInt32Array × UInt32Array :=
  let rec go (doneE doneL : UInt32Array) : List (PaIn IdxCollType) → UInt32Array × UInt32Array
    | [] => (doneE, doneL)
    | T :: more =>
      match T with
      | .dead => go doneE doneL more
      | .br _ mvars _ sorts consts _ apf apa _ laf laa _  alf ala _  lef lea lez _  projs proofsOf proofs =>
          let ndoneE := (mvars.fold doneE (fun n _ S =>
            match (String.fromUTF8! n).toName with
            | .num _ i => S.oInsert i.toUInt32
            | _ => S
                ))
          let doneL := sorts.foldl doneL (fun _ lv R =>
            lv.onAllSubtermsFold R (fun
              | .mvar ⟨(.num _ i)⟩, L => L.oInsert i.toUInt32
              | _, L => L)
            )
          let ndoneL := (consts.fold doneL (fun _ d R =>
              let R := d.foldl R (fun _ lvs R =>
                lvs.foldl (fun R lv =>
                  lv.onAllSubtermsFold R (fun
                    | .mvar ⟨.num (.num _ i) _⟩, L => L.oInsert i.toUInt32
                    | _, L => L)) R)
              R
            ))
          let nmore := (projs.fold more (fun _ d S =>
                d.foldl S (fun _ (_,t) S => t :: S)
                ))
          go ndoneE ndoneL (apf :: apa :: laf :: laa :: alf :: ala :: lef :: lea :: lez :: proofsOf :: proofs :: nmore)
  go .empty .empty [T]



partial def lnodeGarbageCollection
  (T : PaIn IdxCollType) (allTypes cleanTypes: Array Expr)
  : ((PaIn IdxCollType) × Array Expr × Nat) :=
  trace set TracingFlags.all in
  let (liveE,_) := getLiveLnodes T
  trace on .zero with s!"[lnodeGarbageCollection] live {liveE}" in
  let rec @[specialize] extend (done : UInt32Array) : List Nat → UInt32Array
    | [] => done
    | i :: is =>
        let T := allTypes[i]!
        let deps := T.onAllSubtermsFold is (fun
          | .mvar ⟨.num (.num _ i) _⟩, L =>
            if done.oContains i.toUInt32
            then L
            else L.insert i
          | _ , L => L)
        extend (done.oInsert i.toUInt32) deps
  let extended := extend (.emptyWithCapacity liveE.size) (liveE.foldl [] (fun i l => i.toNat :: l))
  trace on .zero with s!"[lnodeGarbageCollection] extended {extended}" in
  let (cleanTypes,transE) : Array Expr × RBMap Nat Nat instOrdNat.compare :=
    extended.foldl (cleanTypes,{}) (fun I (cleanTypes,rb) =>
      let I := I.toNat
      let T := allTypes[I]!
      let T := T.onAllSubtermsTR (fun
        | .mvar ⟨.num (.num k j) s⟩ =>
          match rb.find? j with
          | .none => panic s!"[lnodeGarbageCollection] untranslatable {j}"
          -- crutially relies on the fact that `Lean.Expr.translateToLnodes` and
          -- `getLiveLnodes` preserve dependence in increasing order
          | .some J => .mvar ⟨.num (.num k J) s⟩
        | x => x)
      match cleanTypes.findIdx? (fun x => x == T) with
      | .some j =>
        (cleanTypes, rb.insert I j)
      | .none =>
        let s := cleanTypes.size
        (cleanTypes.push T, rb.insert I s)
        )
  -- let (sizeL,transL) : UInt32 × RBMap UInt32 UInt32 UInt32.instOrd.compare :=
  --   liveL.foldl (0,{}) (fun I (i,rb) => (i+1, rb.insert I i))
  -- let goE (n : Nat) : Nat :=
  --   match transE.find? n with
  --   | .none => panic s!"[lnodeGarbageCollection] encountered non-extended-live index (expr) {n}"
  --   | .some x => x
  -- let goL (n : UInt32) : UInt32 :=
  --   match transL.find? n with
  --   | .none => panic s!"[lnodeGarbageCollection] encountered non-extended-live index (level) {n}"
  --   | .some x => x
  trace on .one with s!"[lnodeGarbageCollection] allTypes {allTypes}" in
  -- let ntypes : Array Expr := allTypes.size.fold (fun i _ A =>
  --   match transE.find? i.toUInt32 with
  --   | .none => A
  --   | .some I =>
  --       let T := types[i]!
  --       let nT := T.onAllSubtermsTR (fun
  --         | .mvar ⟨.num (.num k j) s⟩ => .mvar ⟨.num (.num k (goE j.toUInt32).toNat) s⟩
  --         | .sort u => .sort (u.onAllSubtermsTR (fun
  --             | .mvar ⟨.num (.num k j) s⟩ => .mvar ⟨.num (.num k (goL j.toUInt32).toNat) s⟩
  --             | x => x))
  --         | .const n lvs => .const n <| lvs.mapTR
  --           (fun u => (Level.onAllSubtermsTR  u (fun
  --               | .mvar ⟨.num (.num k j) s⟩ => .mvar ⟨.num (.num k (goL j.toUInt32).toNat) s⟩
  --               | x => x)))
  --         | x => x)
  --       A.set! I.toNat nT
  --   ) (Array.replicate sizeE.toNat (failExpr "lnodeGarbageCollection"))
  trace on .one with s!"[lnodeGarbageCollection] cleanTypes {cleanTypes}" in
  let rec @[specialize] fixLnodes : (PaIn IdxCollType) → (PaIn IdxCollType)
    | x@(.dead) => x
    | .br fvars mvars bvars sorts consts lits apf apa api laf laa lai alf ala ali lef lea lez lei projs proofsOf proofs =>
        let mvars := mvars.fold CTrie.empty (fun n is S =>
          match (String.fromUTF8! n).toName with
          | .num mod t =>
              match transE.find? t with
              | .none => S
              | .some I => S.insert (Name.num mod I).toString.toUTF8 is
          | _ => S
          )
        -- let sorts := sorts.foldl ListProd.nil (fun is u R =>
        --   let u := (u.onAllSubtermsTR (fun
        --       | .mvar ⟨.num (.num k j) s⟩ => .mvar ⟨.num (.num k (goL j.toUInt32).toNat) s⟩
        --       | x => x))
        --   .cons is u R)
        -- let consts := (consts.fold CTrie.empty (fun n d S =>
        --       let new := d.foldl ListProd.nil (fun is lvs R =>
        --         let lvs := lvs.mapTR
        --           (fun u => (Level.onAllSubtermsTR  u (fun
        --               | .mvar ⟨.num (.num k j) s⟩ => .mvar ⟨.num (.num k (goL j.toUInt32).toNat) s⟩
        --               | x => x)))
        --         .cons is lvs R
        --         )
        --       S.insert n new
        --   ))
        .br fvars mvars bvars sorts consts lits
            (fixLnodes apf) (fixLnodes apa) api (fixLnodes laf) (fixLnodes laa) lai
            (fixLnodes alf) (fixLnodes ala) ali (fixLnodes lef) (fixLnodes lea) (fixLnodes lez) lei
            (projs.map (fun L => .some (L.map (fun x (y,z) => (x,y, fixLnodes z)))))
            (fixLnodes proofsOf) (fixLnodes proofs)
  (fixLnodes T, cleanTypes, 1)-- sizeL.toNat)


#check 1

-- #exit

/-- new types will have to be loaded !-/
@[specialize, inline]
def generalizePaInMain [Repr IdxCollType]
  (fold : ∀ {β : Type _}, IdxCollType → (init : β) → (f : Nat → β → β) → β) (empty : IdxCollType)
  (insert : Nat → IdxCollType → IdxCollType)
  (insertMulti intersect union difference : IdxCollType → IdxCollType → IdxCollType) (empty? : IdxCollType → Bool)
  (size : IdxCollType → Nat) (contains : Nat → IdxCollType → Bool)
  (l1 : LocalContext) (l2 : LocalInstances)
  (genCondition : (occWeight : Nat) → (branchWeight : Nat) → (branchDistrib : Array Nat) → (commonType : Expr) → (branchDepth : Nat) → Bool)
  (freqCondition : (occWeight : Nat) → (branchWeight : Nat) → (branchDistrib : Array Nat) → (branchDepth : Nat) → Bool)
  (sampleName : Name)
  (T : PaIn IdxCollType) (weights : Array Nat) (types : Array Expr) (lvlNum : Nat)
  : MetaM (Prod7 (PaIn IdxCollType) (Array Expr) Nat (Array Nat) (RBMap Nat Nat instOrdNat.compare) LocalContext LocalInstances) :=
    do
    mtracing
    mtrace on .zero with s!"[generalizePaInMain] loading lnodes"
    for j in [:lvlNum] do
      let _ ← mkLevelMVarOfName (.num sampleName j)
    let mut i := 0
    for T in types do
      let _ ← mkMvarStdNoCoI (.num sampleName i) T
      i := i+1
    mtrace on .zero with s!"[generalizePaInMain] clear assignements"
    clearMvarAssignments
    mtrace on .zero with s!"[generalizePaInMain] generalising"
    let .mk freqInd T types l1 l2 ← generalizePaInCore
      fold empty insertMulti intersect union difference empty? l1 l2 genCondition freqCondition sampleName
      T weights types
    mtrace on .one with s!"[generalizePaInMain] generalised PaIn {← T.pp l1 l2 [] 0 intersect empty?}"
    mtrace on .zero with s!"[generalizePaInMain] found freqInd {repr freqInd}, deduplicating"
    let .mk T weights trans ← T.dedup insert union empty size contains fold weights freqInd
    mtrace on .zero with s!"[generalizePaInMain] running lnode garbadge collection"
    let (T,types,lvlNum) := lnodeGarbageCollection T types #[]
    return .mk T types lvlNum weights trans l1 l2

#check PaIn.dedup

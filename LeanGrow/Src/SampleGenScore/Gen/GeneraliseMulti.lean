
/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/


import LeanGrow.Src.SampleGenScore.Gen.GeneraliseCore

open Lean Meta

variable {IdxCollType : Type _}




/-- Will require types to have been loaded ! -/
@[specialize, inline]
def generaliseToLnodesCoreMulti [Repr IdxCollType]
  (fold : ∀ {β : Type _}, IdxCollType → (init : β) → (f : Nat → β → β) → β)
  (emptyCol : IdxCollType) (insert union: IdxCollType → IdxCollType → IdxCollType)
  (l1 : LocalContext) (l2 : LocalInstances)
  (sampleName : Name)
  (genCondition : (occWeight : Nat) → (branchWeight : Nat) → (branchDistrib : Array Nat) → (commonType : Expr) → (branchDepth : Nat) → Bool)
  (weights : Array Nat)
  (todo : ListProd Expr IdxCollType)
  (types : Array Expr)
  (safePaIn : PaIn IdxCollType)
  (drdepth : Nat)
  : MetaM (Prod5 (List IdxCollType) (PaIn IdxCollType) (Array Expr) LocalContext LocalInstances) :=
    do
    mtracing
    let Res ← todo.foldlM ((.mk ListProd4.nil 0 #[]) : Prod3 (ListProd4 Expr Expr IdxCollType Nat) Nat (Array Nat)) (fun e is Res => do
      let T ← InferType e l1 l2
      let T ← WhnfR T l1 l2
      let W := getCPIweights fold weights is
      return .mk (.cons e T is W Res.1) (W + Res.2) (Res.3.push W)
      )
    let preprocessed := Res.1
    mtrace on .zero with (← preprocessed.foldlM s!"[generaliseToLnodesCoreMulti] preprocessed \n" (fun e T is W msg => return s!" e {← ppExpr e}\n T {← ppExpr T}\n is {repr is}\n w {W}\n" ++ msg))
    let totalWeigth := Res.2
    let distrib := Res.3
    mtrace on .zero with s!"[generaliseToLnodesCoreMulti] totalWeigth {totalWeigth}"
    let processed ← preprocessed.foldlM ListProd3.nil (fun e T is w L => do
      let (res,added?) ← L.foldlM (ListProd3.nil, false) (fun le τ W L => do
        if L.2
        then return (.cons le τ W L.1, L.2)
        else
          if (← defEqForGen l1 l2 τ T)
          then return (.cons (ListProd.cons e is le) τ (w + W) L.1, true)
          else return (.cons le τ W L.1, L.2)
        )
      if added?
      then return res
      else return .cons (ListProd.cons e is .nil) T w res
      )
    mtrace on .zero with (← processed.foldlM s!"[generaliseToLnodesCoreMulti] processed \n" (fun es T W msg => return s!" es inds {repr <| es.foldl emptyCol (fun _ is R => union is R)}\n T {← ppExpr T}}\n w {W}\n" ++ msg))
    processed.foldlMcps (.mk safePaIn types [] l1 l2 : Prod5 _ _ _ _ _) (fun es T w (.mk P1 P2 P3 l1 l2) q => do
      if !(genCondition w totalWeigth distrib T drdepth)
      then
        mtrace on .zero with s!"[generaliseToLnodesCoreMulti] type ↓ not generalised, adding terms\n {← ppExpr T}"
        es.foldlMcps (.mk P1 l1 l2 : Prod3 _ _ _) (fun e is (.mk rP l1 l2) q1 => do
          q1 <| ← rP.insertMulti l1 l2 e is emptyCol insert
          ) <| fun | .mk nP l1 l2 => do q (.mk nP P2 P3 l1 l2)
      else
        mtrace on .zero with s!"[generaliseToLnodesCoreMulti] type ↓ will be generalised\n {← ppExpr T}"
        let ws := T.getWorkerFVarIds.toArray
        let .mk T l1 l2 ← (do
          if ws.isEmpty
          then return (.mk T l1 l2 : Prod3 ..)
          else
            mtrace on .zero with s!"[generaliseToLnodesCoreMulti] abstracted loose bvars (workers) to {← ppExpr T}"
            T.abstractLetFvarAll l1 l2 ws)
        mtrace on .zero with s!"[generaliseToLnodesCore] type not found adding it as new type of index {types.size}"
        let ln ← mkMvarStdNoCoE (.num sampleName types.size) T
        let types := P2.push T
        let toadd := (mkAppN ln (ws.map Expr.fvar))
        let addinds := es.foldl emptyCol (fun _ is R => union is R)
        let .mk nP l1 l2 ← P1.insertMulti l1 l2 toadd addinds emptyCol insert
        q (.mk nP types (addinds :: P3) l1 l2)
        ) <| fun | .mk P1 P2 P3 l1 l2 => return .mk P3 P1 P2 l1 l2


#check 1


@[inline, specialize]
partial def Array.findIdxIdx? {α : Type _} (A : Array α) (p : Nat → α → Bool) : Option Nat :=
  let rec @[specialize] go (i : Nat) :=
    if h : i < A.size
    then
      if p i A[i]
      then .some i
      else go (i+1)
    else
      .none
  go 0


#check 1




partial def lnodeGarbageCollectionMulti
  (T : PaIn IdxCollType) (allTypes cleanTypes: Array Expr)
  : ((PaIn IdxCollType) × Array Expr × Nat) :=
  trace set TracingFlags.none in
  let (liveE,_) := getLiveLnodes T
  trace on .zero with s!"[lnodeGarbageCollection] live {liveE}" in
  let rec @[specialize] extend (done : UInt32Array) : List Nat → UInt32Array
    | [] => done
    | i :: is =>
        let T := allTypes[i]!
        let deps := T.onAllSubtermsFold is (fun
          | .mvar ⟨(.num _ i)⟩, L =>
            if done.oContains i.toUInt32
            then L
            else L.insert i
          | _ , L => L)
        extend (done.oInsert i.toUInt32) deps
  let extended := extend (.emptyWithCapacity liveE.size) (liveE.foldl [] (fun i l => i.toNat :: l))
  trace on .zero with s!"[lnodeGarbageCollection] extended {extended}" in
  let .mk cleanTypes transE _ : Prod3 (Array Expr) (RBMap Nat Nat instOrdNat.compare) (List Nat) :=
    extended.foldl (.mk cleanTypes {} []) (fun I (.mk cleanTypes rb seen) =>
      let I := I.toNat
      let T := allTypes[I]!
      let T := T.onAllSubtermsTR (fun
        | .mvar ⟨(.num k j)⟩ =>
          match rb.find? j with
          | .none => panic s!"[lnodeGarbageCollection] untranslatable {j}"
          -- crutially relies on the fact that `Lean.Expr.translateToLnodes` and
          -- `getLiveLnodes` preserve dependence in increasing order
          | .some J => .mvar ⟨(.num k J)⟩
        | x => x)
      match cleanTypes.findIdxIdx? (fun i x => !(seen.orderedContains i) && x == T) with
      | .some j =>
        .mk cleanTypes (rb.insert I j) (seen.orderedEraseOrLeave j)
      | .none =>
        let s := cleanTypes.size
        .mk (cleanTypes.push T) (rb.insert I s) seen
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





@[specialize, inline]
partial def generalizePaInCoreMulti [Repr IdxCollType]
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
        mtrace on .zero with s!"[generaliseToLnodesCoreMulti] finalFreqPatInds {repr finalFreqPatInds}"
        let joinedFreqPatInds := finalFreqPatInds.foldl union empty
        let toGenInds := difference branchInds joinedFreqPatInds
        let recBr :=
          PaIn.br poiT mvars bvars sorts consts lits apf apa api laf laa lai alf ala ali lef lea lez lei projs proofsOf proofs
        -- mtrace on .one with s!"[generaliseToLnodesCoreMulti] at branch:\n {repr <| ← (T.buildMultiCore stack 0 id intersect empty?).foldlM ListProd.nil (fun e is R => return .cons s!"{(← ppExpr e)}" is R)}"
        mtrace on .one with s!"[generaliseToLnodesCoreMulti] recuresion yielded:\n {repr <| ← (← recBr.buildMultiCore l1 l2 stack 0 id intersect empty?).foldlM ListProd.nil (fun e is R => return .cons s!"{(← ppExpr e)}" is R)}"
        let toGenVals ← recBr.buildMultiCore l1 l2 stack 0 (fun x => intersect x toGenInds) intersect empty?
        mtrace on .zero with s!"[generaliseToLnodesCoreMulti] terms to generalize:\n {repr <| ← toGenVals.foldlM ListProd.nil (fun e is R => return .cons s!"{(← ppExpr e)}" is R)}"
        let .mk genIds genP types l1 l2 ← generaliseToLnodesCoreMulti
          fold empty insert union l1 l2 sampleName genCondition
          weights toGenVals types .dead drdepth
        mtrace on .zero with s!"[generaliseToLnodesCoreMulti] genIds {repr genIds}"
        mtrace on .one with s!"[generaliseToLnodesCoreMulti] genP:\n {repr <| ← (← genP.buildMultiCore l1 l2 stack 0 id intersect empty?).foldlM ListProd.nil (fun e is R => return .cons s!"{(← ppExpr e)}" is R)}"
        let freqP := recBr.deleteOfInds toGenInds difference empty empty?
        mtrace on .one with s!"[generaliseToLnodesCoreMulti] freqP:\n {repr <| ← (← freqP.buildMultiCore l1 l2 stack 0 id intersect empty?).foldlM ListProd.nil (fun e is R => return .cons s!"{(← ppExpr e)}" is R)}"
        let newP := PaIn.merge union empty freqP genP
        mtrace on .one with s!"[generaliseToLnodesCoreMulti] merged to:\n {repr <| ← (← newP.buildMultiCore l1 l2 stack 0 id intersect empty?).foldlM ListProd.nil (fun e is R => return .cons s!"{(← ppExpr e)}" is R)}"
        let definiteFreqPatInds := genIds.foldl (fun R is =>
            let W := getCPIweights fold weights is
            if freqCondition W normalize distrib drdepth
            -- so we compare the weight of the generalized pattern to the old distrib
            then is :: R else R
            ) finalFreqPatInds
        return .mk definiteFreqPatInds newP types l1 l2
  go l1 l2 .nil T types 0

#check 1


/-- new types will have to be loaded !-/
@[specialize, inline]
def generalizePaInMainMulti [Repr IdxCollType]
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
    let .mk freqInd T types l1 l2 ← generalizePaInCoreMulti
      fold empty insertMulti intersect union difference empty? l1 l2 genCondition freqCondition sampleName
      T weights types
    mtrace on .one with s!"[generalizePaInMain] generalised PaIn {← T.pp l1 l2 [] 0 intersect empty?}"
    mtrace on .zero with s!"[generalizePaInMain] found freqInd {repr freqInd}, deduplicating"
    let .mk T weights trans ← T.dedup insert union empty size contains fold weights freqInd
    mtrace on .zero with s!"[generalizePaInMain] deleting top mvars"
    let .mk T weights ntrans ← T.removeTopMvars insert union empty size contains fold weights
    let trans := translateMerge trans ntrans
    mtrace on .zero with s!"[generalizePaInMain] running lnode garbadge collection"
    let (T,types,lvlNum) := lnodeGarbageCollectionMulti T types #[]
    return .mk T types lvlNum weights trans l1 l2

#check PaIn.dedup

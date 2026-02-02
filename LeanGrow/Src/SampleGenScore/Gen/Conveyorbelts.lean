

/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import LeanGrow.Src.SampleGenScore.Gen.GeneraliseCore
import LeanGrow.Src.Data.PathIndex.Build
import LeanGrow.Src.Data.PathIndex.Find

open Lean Meta

variable {IdxCollType : Type _}

@[inline]
partial def Lean.Level.translateToLnodes (e : Level)
  (sampleName : Name) : Level :=
    let mvi := ⟨.num sampleName 0⟩
    e.onAllSubtermsTR (fun
      | .param .. => .mvar mvi
      | x => x)


partial def Lean.Expr.translateToLnodes (l1 : LocalContext) (l2 : LocalInstances) (e : Expr)
  (sampleName : Name) (types : Array Expr) (dict : NameMap MVarId)
  : MetaM (Prod4 Expr (Prod (Array Expr) (NameMap MVarId)) LocalContext LocalInstances) :=
  do
  mtrace on .one with s!"[translateToLnodes] call on {← ppExpr e}"
  e.onAllSubtermsWiWorkerCpsSkipTravState l1 l2 (⟨types, dict⟩ : Prod (Array Expr) (NameMap MVarId))
    (fun e _ s@⟨types, dict⟩ l1 l2 => do
      match e with
      | .fvar fid =>
          if fid.isWorker
          then
            return .mk (.ok e) s l1 l2
          else
            match dict.find? fid.name with
            | .some rep => return .mk (.ok (.mvar rep)) s l1 l2
            | .none =>
                let T ← fid.GetType l1 l2
                mtrace on .zero with s!"[translateToLnodes] unknown {repr fid}  of type {← ppExpr T}"
                let .mk T (types, dict) l1 l2 ← (do
                  if T.hasFVar
                  then T.translateToLnodes l1 l2 sampleName types dict
                  else return Prod4.mk T (types, dict) l1 l2)
                match types.findIdx? (fun t => t == T) with -- defeq not needed (??), nor desired due to workers ...
                | .some i =>
                    mtrace on .zero with s!"[translateToLnodes] same type as {i}"
                    let rep : MVarId := ⟨.num sampleName i⟩
                    let dict := dict.insert fid.name rep
                    return .mk  (.ok (.mvar rep)) ⟨types,dict⟩ l1 l2
                | .none =>
                    let rep : MVarId := ← mkMvarStdIndexNoCoI (.num sampleName types.size) T 0
                    let types := types.push T
                    let dict := dict.insert fid.name rep
                    mtrace on .zero with s!"[translateToLnodes] translate {repr fid} to {repr rep}  of type {← ppExpr T}"
                    return .mk  (.ok (.mvar rep)) ⟨types,dict⟩ l1 l2

      | .sort u =>
          return .mk  (.ok (.sort (u.translateToLnodes sampleName))) s l1 l2
      | .const n us =>
          return .mk  (.ok (.const n (us.mapTR (fun x => x.translateToLnodes sampleName)))) s l1 l2
      | _ => return .mk  (.ok e) s l1 l2
      )

#check 1
#check CTrie.upsertM


@[specialize, inline]
partial def cvb_thms_sampleClassify
  [Repr IdxCollType]
  (emptyCol : IdxCollType) (singleton : Nat → IdxCollType) (insert : Nat → IdxCollType → IdxCollType)
  (l1 : LocalContext) (l2 : LocalInstances)
  (sampleThm : Name) (sampleGoal : Expr) (sampleHyps : List Expr) -- should contain lnodes ...
  (sorted : (CTrie (Prod5 Nat Nat (ListProd Nat (List Nat)) (PaIn IdxCollType) (PaIn IdxCollType))))
  : MetaM (CTrie (Prod5 Nat Nat (ListProd Nat (List Nat)) (PaIn IdxCollType) (PaIn IdxCollType))) := do
    let sampleThm := sampleThm.toString.toUTF8
    sorted.upsertM sampleThm (fun
      | .none => do
          let .mk ngT _ _ ← PaIn.dead.insert l1 l2 sampleGoal 0 emptyCol singleton insert
          let .mk nhi tshd nhT ← sampleHyps.foldlM (fun (.mk nhi tshd nT) e => do
            let .mk iT _ _ ← nT.insert l1 l2 e nhi emptyCol singleton insert
            return .mk (nhi + 1) (nhi :: tshd) iT
            ) (.mk 0 [] PaIn.dead : Prod3 ..)
          return .some <| .mk 1 nhi (.cons 0 tshd .nil) ngT nhT
      | .some (Prod5.mk initSamIdx initHypIdx iD igT ihT) => do
          let .mk ngT _ _ ← igT.insert l1 l2 sampleGoal initSamIdx emptyCol singleton insert
          let .mk nhi tshd nhT ← sampleHyps.foldlM (fun (.mk nhi tshd nT) e => do
            let .mk iT _ _ ← nT.insert l1 l2 e nhi emptyCol singleton insert
            return .mk (nhi + 1) (nhi :: tshd) iT
            ) (.mk initHypIdx [] ihT : Prod3 ..)
          return .some <| .mk (initSamIdx+1) nhi (.cons initSamIdx tshd iD) ngT nhT
      )

#check 1

@[specialize, inline]
partial def cvb_goal_hyp_sampleClassify
  [Repr IdxCollType]
  (emptyCol : IdxCollType) (singleton : Nat → IdxCollType) (insert : Nat → IdxCollType → IdxCollType)
  (empty? : IdxCollType → Bool) (intersect union : IdxCollType → IdxCollType → IdxCollType) (head : IdxCollType → Nat)
  (l1 : LocalContext) (l2 : LocalInstances)
  (sampleThm : Name) (sampleGoal : Expr) (sampleHyps : List Expr) -- should contain lnodes ...
  (state : Prod3 Nat (PaIn IdxCollType) (Array (Prod4 Nat Nat (ListProd ByteArray (List Nat)) (PaIn IdxCollType))))
  : MetaM (Prod3 Nat (PaIn IdxCollType) (Array (Prod4 Nat Nat (ListProd ByteArray (List Nat)) (PaIn IdxCollType)))) := do
  let .mk initSamIdx goalPain sorted := state
  let sampleThm := sampleThm.toString.toUTF8
  let I := goalPain.getIndices emptyCol union
  let .mk stat res _ _ _ ← goalPain.findCore l1 l2 empty? intersect union emptyCol I 2 sampleGoal
  if stat == 3
  then
    let idx := head res
    let sorted ← sorted.modifyM idx (fun (.mk initHypIdx w dic hs) => do
      let .mk nhi tshd nhT ← sampleHyps.foldlM (fun (.mk nhi tshd nT) e => do
        let .mk iT _ _ ← nT.insert l1 l2 e nhi emptyCol singleton insert
        return .mk (nhi + 1) (nhi :: tshd) iT
        ) (.mk initHypIdx [] PaIn.dead : Prod3 ..)
      return .mk nhi (w+1) (.cons sampleThm tshd dic) (PaIn.merge union emptyCol nhT hs))
    return .mk (initSamIdx+1) goalPain sorted
  else
    let .mk ngT _ _ ← goalPain.insert l1 l2 sampleGoal initSamIdx emptyCol singleton insert
    let .mk nhi tshd nhT ← sampleHyps.foldlM (fun (.mk nhi tshd nT) e => do
      let .mk iT _ _ ← nT.insert l1 l2 e nhi emptyCol singleton insert
      return .mk (nhi + 1) (nhi :: tshd) iT
      ) (.mk 0 [] PaIn.dead : Prod3 ..)
    let sorted := sorted.push (.mk nhi 1 (.cons sampleThm tshd .nil) nhT)
    return .mk (initSamIdx+1) ngT sorted


#check 1


@[specialize, inline]
partial def cvb_thms_genGoal [Repr IdxCollType]
  (fold : ∀ {β : Type _}, IdxCollType → (init : β) → (f : Nat → β → β) → β) (empty : IdxCollType)
  (insert : Nat → IdxCollType → IdxCollType)
  (insertMulti intersect union difference : IdxCollType → IdxCollType → IdxCollType) (empty? : IdxCollType → Bool)
  (size : IdxCollType → Nat) (contains : Nat → IdxCollType → Bool)
  (l1 : LocalContext) (l2 : LocalInstances)
  (genCondition : (occWeight : Nat) → (branchWeight : Nat) → (branchDistrib : Array Nat) → (commonType : Expr) → (branchDepth : Nat) → Bool)
  (freqCondition : (occWeight : Nat) → (branchWeight : Nat) → (branchDistrib : Array Nat) → (branchDepth : Nat) → Bool)
  (samIdx : Nat) (goalPain : PaIn IdxCollType)
  (sampleName : Name) (types : Array Expr)
  : MetaM (Prod5 (PaIn IdxCollType) (Array Nat) Nat (RBMap Nat Nat instOrdNat.compare) (Array Expr)) := do
    let weights := Array.replicate samIdx (1 : Nat)
    mtrace on .zero with s!" generalising"
    let .mk freqInd T types l1 l2 ← generalizePaInCore
      fold empty insertMulti intersect union difference empty? l1 l2 genCondition freqCondition sampleName
      goalPain weights types
    mtrace on .one with s!" generalised PaIn {← T.pp l1 l2 [] 0 intersect empty?}"
    mtrace on .zero with s!" found freqInd {repr freqInd}, deduplicating"
    let .mk T weights trans ← T.dedup insert union empty size contains fold weights freqInd
    mtrace on .zero with s!" running lnode garbadge collection"
    let (T,types,_) := lnodeGarbageCollection T types
    let total := weights.foldl (fun x y => x+y) 0
    return .mk T weights total trans types

#check 1

private def translate (hs : List Nat) (trans : (RBMap Nat Nat instOrdNat.compare)) : List Nat :=
  hs.foldl (fun ths i =>
      match Lean.RBMap.find? trans i with
      | .none => panic! s!"[cvb_thms_genHyps] untranslatable {i}"
      | .some t => ths.insert t
      ) []


@[specialize, inline]
partial def cvb_thms_genHyps [Repr IdxCollType]
  (fold : ∀ {β : Type _}, IdxCollType → (init : β) → (f : Nat → β → β) → β) (empty : IdxCollType)
  (insert : Nat → IdxCollType → IdxCollType)
  (insertMulti intersect union difference : IdxCollType → IdxCollType → IdxCollType) (empty? : IdxCollType → Bool)
  (size : IdxCollType → Nat) (contains : Nat → IdxCollType → Bool)
  (l1 : LocalContext) (l2 : LocalInstances)
  (genCondition : (occWeight : Nat) → (branchWeight : Nat) → (branchDistrib : Array Nat) → (commonType : Expr) → (branchDepth : Nat) → Bool)
  (freqCondition : (occWeight : Nat) → (branchWeight : Nat) → (branchDistrib : Array Nat) → (branchDepth : Nat) → Bool)
  (hypIdx : Nat) (hypsPain : PaIn IdxCollType) (samHypDict : ListProd Nat (List Nat))
  (sampleName : Name) (types : Array Expr)
  : MetaM (Prod4 (SetTrie (Nat × Nat) (PaIn IdxCollType)) Nat (RBMap Nat Nat instOrdNat.compare) (Array Expr)) := do
    let weights := Array.replicate hypIdx (1 : Nat)
    mtrace on .zero with s!" generalising"
    let .mk freqInd T types l1 l2 ← generalizePaInCore
      fold empty insertMulti intersect union difference empty? l1 l2 genCondition freqCondition sampleName
      hypsPain weights types
    mtrace on .one with s!" generalised PaIn {← T.pp l1 l2 [] 0 intersect empty?}"
    mtrace on .zero with s!" found freqInd {repr freqInd}, deduplicating"
    let .mk T weights trans ← T.dedup insert union empty size contains fold weights freqInd
    mtrace on .zero with s!" running lnode garbadge collection"
    let (T,types,_) := lnodeGarbageCollection T types
    let total := weights.foldl (fun x y => x+y) 0
    let Tis := T.getIndices empty union
    let toST ← samHypDict.foldlM ListProd.nil (fun samIdx hs R => do
      let ths : List Nat := translate hs trans
      let W := ths.foldl (fun w i => w + weights[i]!) 0
      let iths := ths.foldl (fun r i => insert i r) empty
      let compl := difference Tis iths
      let P := T.deleteOfInds compl difference empty empty?
      return .cons P (samIdx, W) R
      -- should we add samIdx to disambiguate leaves to avoid merge durring cleaning ??
      )
    -- use SetTriePG.ofList here ↓
    @SetTrie.ofListMcps _ ((PaIn IdxCollType)) ((PaIn IdxCollType)) _ _ _ _
      (PaIn.dead)
      (fun ( x) ( y) q => do q ( (PaIn.merge union empty x y) ))
      (fun ( y ) => -- ↑↓ requires for samples to use a single lnode per type, so that max doesn't treat them as distinct
        match y.max intersect empty? size with
        | .none => (OptionProd.none : OptionProd (IdxCollType × (ListProd Expr IdxCollType)) Nat)
        | .some inds m =>
            let res := PaIn.buildCore y [] 0 (fun x => intersect x inds) intersect empty?
            let is := res.foldl empty (fun _ i R => union i R)
            OptionProd.some (is, res) m)
      (fun ( x ) (is,_) q => do
        let real ← x.sharesIndicesWith intersect empty? is
        if real then q (.some ()) else q .none)
      (fun ( x) (is,_) _ =>  (x.deleteOfInds is difference empty empty?) )
      (fun ( x ) => match x.clean empty empty? with | .dead => true | _ => false)
      (fun (_,es) q => do
            es.foldlMcps (.mk .dead {} {} : Prod3 ..) (fun e is (.mk T l1 l2) q => do
              let res ← PaIn.insertMulti l1 l2 e is T empty insertMulti
              q res) <| fun res => q res.1)
          (fun (_,es) τ q => do
            es.foldlMcps τ (fun e is ( T) q => do
              let res ← PaIn.insertMulti l1 l2 e is T empty insertMulti
              q res.1) <| fun res => q res)
      toST
      <| fun st => do
          return .mk st total trans types

#check 1



@[specialize, inline]
partial def cvb_goal_hyp_genGoal [Repr IdxCollType]
  (fold : ∀ {β : Type _}, IdxCollType → (init : β) → (f : Nat → β → β) → β) (empty : IdxCollType)
  (shiftAdd : IdxCollType → Nat → IdxCollType)
  (insert : Nat → IdxCollType → IdxCollType)
  (insertMulti intersect union difference : IdxCollType → IdxCollType → IdxCollType) (empty? : IdxCollType → Bool)
  (size : IdxCollType → Nat) (contains : Nat → IdxCollType → Bool)
  (l1 : LocalContext) (l2 : LocalInstances)
  (genCondition : (occWeight : Nat) → (branchWeight : Nat) → (branchDistrib : Array Nat) → (commonType : Expr) → (branchDepth : Nat) → Bool)
  (freqCondition : (occWeight : Nat) → (branchWeight : Nat) → (branchDistrib : Array Nat) → (branchDepth : Nat) → Bool)
  (sampleName : Name) (types : Array Expr)
  (state : Prod3 Nat (PaIn IdxCollType) (Array (Prod4 Nat Nat (ListProd ByteArray (List Nat)) (PaIn IdxCollType))))
  : MetaM (Prod5 (PaIn IdxCollType) (Array Nat) Nat (Array (Prod3 Nat (ListProd ByteArray (List Nat)) (PaIn IdxCollType))) (Array Expr)) := do
  let .mk _ goalPain sorted := state
  let weights := sorted.map Prod4.snd
  mtrace on .zero with s!" generalising"
  let .mk freqInd T types _ _ ← generalizePaInCore
    fold empty insertMulti intersect union difference empty? l1 l2 genCondition freqCondition sampleName
    goalPain weights types
  mtrace on .one with s!" generalised PaIn {← T.pp l1 l2 [] 0 intersect empty?}"
  mtrace on .zero with s!" found freqInd {repr freqInd}, deduplicating"
  let .mk T weights trans ← T.dedup insert union empty size contains fold weights freqInd
  mtrace on .zero with s!" running lnode garbadge collection"
  let (T,types,_) := lnodeGarbageCollection T types
  let total := weights.foldl (fun x y => x+y) 0
  let mut next := Array.replicate weights.size (Prod3.mk 0 (ListProd.nil : (ListProd ByteArray (List Nat))) PaIn.dead)
  for (ini,new) in trans do
    let .mk hypI _ dict hyps := sorted[ini]!
    next := next.modify new (fun (Prod3.mk hi di pi) =>
      let D := dict.foldl di (fun x y R => .cons x (y.map (· + hi)) R)
      let pi := pi.mapInds (fun x => shiftAdd x hi) empty
      let P := PaIn.merge union empty pi hyps
      .mk (hi + hypI) D P
      )
  return Prod5.mk T weights total next types

#check PaIn.merge


/-- Won't preserve order-/
@[specialize]
partial def SetTrie.mergeLeaves {γ : Sort _}
  (fold : α → γ → γ) (ini : γ)
  (T : SetTrie α β) : SetTrie γ β :=
    let rec @[specialize] inner (toL : γ) (leaf? : Bool) (done : List (SetTrie α β)) : List (SetTrie α β) → Prod3 Bool γ (List (SetTrie α β))
      | [] => .mk leaf? toL done
      | .leaf v :: more => inner (fold v toL) true done more
      | nx :: more => inner toL leaf? (nx :: done) more
    match T with
    | .root c =>
        let .mk leaf? toL c := inner ini false [] c
        let c := c.mapTRR (mergeLeaves fold ini)
        if leaf? then .root ((.leaf toL) :: c) else .root c
    | .node t c =>
        let .mk leaf? toL c := inner ini false [] c
        let c := c.mapTRR (mergeLeaves fold ini)
        if leaf? then .node t ((.leaf toL) :: c) else .node t c
    | .leaf a => .leaf (fold a ini)



@[specialize, inline]
partial def cvb_goal_hyp_genHyps [Repr IdxCollType]
  (fold : ∀ {β : Type _}, IdxCollType → (init : β) → (f : Nat → β → β) → β) (empty : IdxCollType)
  (insert : Nat → IdxCollType → IdxCollType)
  (insertMulti intersect union difference : IdxCollType → IdxCollType → IdxCollType) (empty? : IdxCollType → Bool)
  (size : IdxCollType → Nat) (contains : Nat → IdxCollType → Bool)
  (l1 : LocalContext) (l2 : LocalInstances)
  (genCondition : (occWeight : Nat) → (branchWeight : Nat) → (branchDistrib : Array Nat) → (commonType : Expr) → (branchDepth : Nat) → Bool)
  (freqCondition : (occWeight : Nat) → (branchWeight : Nat) → (branchDistrib : Array Nat) → (branchDepth : Nat) → Bool)
  (entry : Prod3 Nat (ListProd ByteArray (List Nat)) (PaIn IdxCollType))
  (sampleName : Name) (types : Array Expr)
  : MetaM (Prod4 (SetTrie (CTrie Nat) (PaIn IdxCollType)) (Array Nat) Nat (Array Expr)) := do
    let .mk hypIdx dict hypsPain := entry
    let weights := Array.replicate hypIdx (1 : Nat)
    mtrace on .zero with s!" generalising"
    let .mk freqInd T types l1 l2 ← generalizePaInCore
      fold empty insertMulti intersect union difference empty? l1 l2 genCondition freqCondition sampleName
      hypsPain weights types
    mtrace on .one with s!" generalised PaIn {← T.pp l1 l2 [] 0 intersect empty?}"
    mtrace on .zero with s!" found freqInd {repr freqInd}, deduplicating"
    let .mk T weights trans ← T.dedup insert union empty size contains fold weights freqInd
    mtrace on .zero with s!" running lnode garbadge collection"
    let (T,types,_) := lnodeGarbageCollection T types
    let total := weights.foldl (fun x y => x+y) 0
    let Tis := T.getIndices empty union
    let toST ← dict.foldlM ListProd.nil (fun thm hs R => do
      let ths : List Nat := translate hs trans
      let W := ths.foldl (fun w i => w + weights[i]!) 0
      let iths := ths.foldl (fun r i => insert i r) empty
      let compl := difference Tis iths
      let P := T.deleteOfInds compl difference empty empty?
      return .cons P (thm, W) R
      -- should we add samIdx to disambiguate leaves to avoid merge durring cleaning ??
      )
    -- use SetTriePG.ofList here ↓
    @SetTrie.ofListMcps _ ((PaIn IdxCollType)) ((PaIn IdxCollType)) _ _ _ _
      (PaIn.dead)
      (fun ( x) ( y) q => do q ( (PaIn.merge union empty x y) ))
      (fun ( y ) => -- ↑↓ requires for samples to use a single lnode per type, so that max doesn't treat them as distinct
        match y.max intersect empty? size with
        | .none => (OptionProd.none : OptionProd (IdxCollType × (ListProd Expr IdxCollType)) Nat)
        | .some inds m =>
            let res := PaIn.buildCore y [] 0 (fun x => intersect x inds) intersect empty?
            let is := res.foldl empty (fun _ i R => union i R)
            OptionProd.some (is, res) m)
      (fun ( x ) (is,_) q => do
        let real ← x.sharesIndicesWith intersect empty? is
        if real then q (.some ()) else q .none)
      (fun ( x) (is,_) _ =>  (x.deleteOfInds is difference empty empty?) )
      (fun ( x ) => match x.clean empty empty? with | .dead => true | _ => false)
      (fun (_,es) q => do
            es.foldlMcps (.mk .dead {} {} : Prod3 ..) (fun e is (.mk T l1 l2) q => do
              let res ← PaIn.insertMulti l1 l2 e is T empty insertMulti
              q res) <| fun res => q res.1)
          (fun (_,es) τ q => do
            es.foldlMcps τ (fun e is ( T) q => do
              let res ← PaIn.insertMulti l1 l2 e is T empty insertMulti
              q res.1) <| fun res => q res)
      toST
      <| fun st => do
          let st := st.mergeLeaves (fun (n,v) t => t.upsert n (fun
              | .none => .some v
              | .some w => .some (w+v))
              ) CTrie.empty
          return .mk st weights total types

#check 1
#check SetTrie.map

@[specialize, inline]
partial def cvb_thms_genMain [Repr IdxCollType]
  (fold : ∀ {β : Type _}, IdxCollType → (init : β) → (f : Nat → β → β) → β) (empty : IdxCollType)
  (insert : Nat → IdxCollType → IdxCollType)
  (insertMulti intersect union difference : IdxCollType → IdxCollType → IdxCollType) (empty? : IdxCollType → Bool)
  (size : IdxCollType → Nat) (contains : Nat → IdxCollType → Bool)
  (l1 : LocalContext) (l2 : LocalInstances)
  (genCondition : (occWeight : Nat) → (branchWeight : Nat) → (branchDistrib : Array Nat) → (commonType : Expr) → (branchDepth : Nat) → Bool)
  (freqCondition : (occWeight : Nat) → (branchWeight : Nat) → (branchDistrib : Array Nat) → (branchDepth : Nat) → Bool)
  (sampleName : Name) (types : Array Expr)
  (sorted : CTrie (Prod5 Nat Nat (ListProd Nat (List Nat)) (PaIn IdxCollType) (PaIn IdxCollType)))
  : MetaM ((Array Expr) × (CTrie (thmGenDataEntry IdxCollType))) := do
    sorted.foldMapM types (fun entry types => do
      let .mk gT gW gw _ types ← cvb_thms_genGoal
        fold empty insert insertMulti intersect union difference
        empty? size contains l1 l2 genCondition freqCondition
        entry.1 entry.4 sampleName types
      let .mk hT hw _ types ← cvb_thms_genHyps
        fold empty insert insertMulti intersect union difference
        empty? size contains l1 l2 genCondition freqCondition
        entry.2 entry.5 entry.3 sampleName types
      return (types, .some (.mk gT gW gw hT hw))
      )


#check 1

@[specialize, inline]
partial def cvb_goal_hyp_genMain [Repr IdxCollType]
  (fold : ∀ {β : Type _}, IdxCollType → (init : β) → (f : Nat → β → β) → β) (empty : IdxCollType)
  (shiftAdd : IdxCollType → Nat → IdxCollType)
  (insert : Nat → IdxCollType → IdxCollType)
  (insertMulti intersect union difference : IdxCollType → IdxCollType → IdxCollType) (empty? : IdxCollType → Bool)
  (size : IdxCollType → Nat) (contains : Nat → IdxCollType → Bool)
  (l1 : LocalContext) (l2 : LocalInstances)
  (genCondition : (occWeight : Nat) → (branchWeight : Nat) → (branchDistrib : Array Nat) → (commonType : Expr) → (branchDepth : Nat) → Bool)
  (freqCondition : (occWeight : Nat) → (branchWeight : Nat) → (branchDistrib : Array Nat) → (branchDepth : Nat) → Bool)
  (sampleName : Name) (types : Array Expr)
  (state : Prod3 Nat (PaIn IdxCollType) (Array (Prod4 Nat Nat (ListProd ByteArray (List Nat)) (PaIn IdxCollType))))
  : MetaM ((Array Expr) × (goalhypGenData IdxCollType)) := do
  let .mk gT gW gw next types ← cvb_goal_hyp_genGoal
    fold empty shiftAdd insert insertMulti intersect union difference
    empty? size contains l1 l2 genCondition freqCondition
    sampleName types state
  let mut hypD : Array (goalhypGenDataEntry IdxCollType) := Array.emptyWithCapacity gW.size
  let mut types := types
  for entry in next do
    let .mk hT hW hw types' ← cvb_goal_hyp_genHyps
      fold empty insert insertMulti intersect union difference
      empty? size contains l1 l2 genCondition freqCondition
      entry sampleName types
    types := types'
    hypD := hypD.push (.mk hT hW hw)
  return .mk types (.mk gT gW gw hypD)

--cvb_goal_hyp_genGoal

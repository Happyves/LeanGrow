


/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import LeanGrow.Src.SampleGenScore.Gen.GeneraliseMulti
import LeanGrow.Src.SampleGenScore.Gen.Conveyorbelts

import LeanGrow.Src.Caching.Formating.Process

open Lean Meta




def Lean.Level.getLevelTranlsation
  (e : Level) (sampleName : Name) (st : Prod3 Nat Nat (NameMap Name))
  : Prod3 Nat Nat (NameMap Name) :=
    e.onAllSubtermsFold st (fun l st@(.mk i lvlNum trans) =>
      match l with
      | .param n =>
        match trans.find? n with
        | .some .. => st
        | .none =>
          let trans := trans.insert n (.num sampleName i)
          let lvlNum := Nat.max lvlNum i
          let i := i+1
          .mk i lvlNum trans
      | _ => st
      )


def Lean.Expr.getLevelTranlsation (l1 : LocalContext) (l2 : LocalInstances)
  (e : Expr) (sampleName : Name) (lvlNum : Nat) (iniTr : NameMap Name) (iniSeen : NameSet)
  : MetaM (Prod5 Nat (NameMap Name) NameSet LocalContext LocalInstances) := do
  let .mk res l1 l2 ← e.onAllSubtermsFoldEnqueueM
    l1 l2 (Prod4.mk 0 lvlNum iniTr iniSeen) (fun e d w l1 l2 st@(.mk i lvlNum trans seen) => do
      match e with
      | .fvar fv@(.mk fvid) =>
        if seen.contains fvid || (w.contains e)
        then return .mk (.std st) l1 l2
        else
          let T ← fv.GetType l1 l2
          let seen := seen.insert fvid
          return .mk (.enq (.mk i lvlNum trans seen) d T) l1 l2
      | .sort u =>
        let .mk i lvlNum trans := u.getLevelTranlsation sampleName (.mk i lvlNum trans)
        return .mk (.std (.mk i lvlNum trans seen)) l1 l2
      | .const _ us =>
        let .mk i lvlNum trans := us.foldl (fun st u =>
          u.getLevelTranlsation sampleName st) (.mk i lvlNum trans)
        return .mk (.std (.mk i lvlNum trans seen)) l1 l2
      | _ =>
        return .mk (.std st) l1 l2
      )
  return .mk res.2 res.3 res.4 l1 l2


@[inline]
partial def Lean.Level.translateToLnodesMulti (e : Level)
  (trans : NameMap Name) : Level :=
    e.onAllSubtermsTR (fun
      | .param fid =>
        match trans.find? fid with
        | .some tr => .mvar (.mk tr)
        | .none => panic! s!"[translateToLnodesMulti] untranslated {fid}"
      | x => x)


partial def Lean.Expr.translateToLnodesMulti (l1 : LocalContext) (l2 : LocalInstances) (e : Expr)
  (sampleName : Name) (types : Array Expr) (dict : NameMap MVarId) (lvlTrans : NameMap Name)
  : MetaM (Prod4 Expr (Prod (Array Expr) (NameMap MVarId)) LocalContext LocalInstances) :=
  do
  mtracing
  mtrace on .one with s!"call on {← ppExpr e}"
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
                mtrace on .zero with s!" unknown {repr fid}  of type {← ppExpr T}"
                let .mk T (types, dict) l1 l2 ← T.translateToLnodesMulti l1 l2 sampleName types dict lvlTrans
                let rep : MVarId := ← mkMvarStdIndexNoCoI (.num sampleName types.size) T 0
                let types := types.push T
                let dict := dict.insert fid.name rep
                mtrace on .zero with s!" translate {repr fid} to {repr rep}  of type {← ppExpr T}"
                return .mk  (.ok (.mvar rep)) ⟨types,dict⟩ l1 l2
      | .sort u =>
          return .mk  (.ok (.sort (u.translateToLnodesMulti lvlTrans))) s l1 l2
      | .const n us =>
          return .mk  (.ok (.const n (us.mapTR (fun x => x.translateToLnodesMulti lvlTrans)))) s l1 l2
      | _ => return .mk  (.ok e) s l1 l2
      )


variable {IdxCollType : Type _}

/-- Expects raw samples with no lnode translation-/
@[specialize, inline]
partial def cvb_thmConj_sampleClassify
  [Repr IdxCollType]
  (emptyCol : IdxCollType) (singleton : Nat → IdxCollType) (insert : Nat → IdxCollType → IdxCollType)
  (l1 : LocalContext) (l2 : LocalInstances)
  (sampleThm : Name) (conjs : Array Expr) (goal : Expr) (hyps : List Expr) (sampleName : Name)
  (state : Prod3 Nat (Array Expr) (CTrie (Prod6 Nat Nat (ListProd Nat (List Nat)) (PaIn IdxCollType) (PaIn IdxCollType) (Array (Nat × PaIn IdxCollType)))))
  : MetaM (Prod3 Nat (Array Expr) (CTrie (Prod6 Nat Nat (ListProd Nat (List Nat)) (PaIn IdxCollType) (PaIn IdxCollType) (Array (Nat × PaIn IdxCollType))))) := do
    let .mk lvlNum types sorted := state
    let .mk goal (types, dict) l1 l2 ← goal.translateToLnodes l1 l2 sampleName types {}
    let .mk hyps (types, _) l1 l2 ← hyps.foldlM (fun (.mk L (types, dict) l1 l2) h => do
      let .mk h (types, dict) l1 l2 ← h.translateToLnodes l1 l2 sampleName types dict
      return .mk (h :: L) (types, dict) l1 l2
      ) (Prod4.mk [] (types, dict) l1 l2)
    let sampleThm := sampleThm.toString.toUTF8
    let .mk lN nm _ l1 l2 ← conjs.foldlM (fun (.mk lN nm seen l1 l2) e => do
      e.getLevelTranlsation l1 l2 sampleName lN nm seen
      ) (Prod5.mk lvlNum {} {} l1 l2)
    let .mk conjs (types, _) l1 l2 ← conjs.foldlM (fun (.mk cjs (types,dict) l1 l2) e => do
      let .mk here (types,dict) l1 l2 ← e.translateToLnodesMulti l1 l2
        sampleName types dict nm
      return .mk (cjs.push here) (types,dict) l1 l2
      ) (Prod4.mk (Array.emptyWithCapacity conjs.size) (types,{}) l1 l2)
    let new ← sorted.upsertM sampleThm (fun
      | .none => do
          let .mk ngT _ _ ← PaIn.dead.insert l1 l2 goal 0 emptyCol singleton insert
          let .mk nhi tshd nhT ← hyps.foldlM (fun (.mk nhi tshd nT) e => do
            let .mk iT _ _ ← nT.insert l1 l2 e nhi emptyCol singleton insert
            return .mk (nhi + 1) (nhi :: tshd) iT
            ) (.mk 0 [] PaIn.dead : Prod3 ..)
          let .mk cjs _ _ ← conjs.foldlM (fun (.mk A l1 l2) c => do
            let .mk cT l1 l2 ← PaIn.dead.insert l1 l2 c 0 emptyCol singleton insert
            return .mk (A.push (1,cT)) l1 l2
            ) (Prod3.mk (Array.emptyWithCapacity conjs.size) l1 l2)
          return .some <| .mk 1 nhi (.cons 0 tshd .nil) ngT nhT cjs
      | .some (Prod6.mk initSamIdx initHypIdx iD igT ihT cjs) => do
          let .mk ngT _ _ ← igT.insert l1 l2 goal initSamIdx emptyCol singleton insert
          let .mk nhi tshd nhT ← hyps.foldlM (fun (.mk nhi tshd nT) e => do
            let .mk iT _ _ ← nT.insert l1 l2 e nhi emptyCol singleton insert
            return .mk (nhi + 1) (nhi :: tshd) iT
            ) (.mk initHypIdx [] ihT : Prod3 ..)
          let .mk _ cjs _ _ ← conjs.foldlM (fun (.mk i A l1 l2) c => do
            let (idx,T) := A[i]!
            let .mk cT l1 l2 ← T.insert l1 l2 c idx emptyCol singleton insert
            return .mk (i+1) (A.set! i (idx+1, cT)) l1 l2
            ) (Prod4.mk 0 cjs l1 l2)
          return .some <| .mk (initSamIdx+1) nhi (.cons initSamIdx tshd iD) ngT nhT cjs
      )
    return .mk lN types new



#check 1

#check ThmFormat

/-- Bit akward cause we don't keep track of dependencies or enforce any invariant -/
partial def Lean.Expr.getLnodesToBind (l1 : LocalContext) (l2 : LocalInstances)
  (e : Expr) (bins : Array Expr) (seen : NameSet) : MetaM (Prod3 (Array Expr × NameSet) LocalContext LocalInstances) := do
  let .mk res l1 l2 ← e.onAllSubtermsFoldM
    l1 l2 (Prod.mk bins seen) (fun e _ _ l1 l2 st@(.mk bins seen) => do
      match e with
      | .mvar mv@(.mk mvid) =>
        if seen.contains mvid
        then return .mk st l1 l2
        else
          let T ← mv.getType
          let seen := seen.insert mvid
          let .mk (bins, seen) l1 l2 ← T.getLnodesToBind l1 l2 bins seen
          let bins := bins.push e
          return .mk (.mk bins seen) l1 l2
      | _ =>
        return .mk st l1 l2
      )
  return .mk res l1 l2


def Lean.Expr.bindLnodes_makeLevelPara (l1 : LocalContext) (l2 : LocalInstances)
  (e : Expr) : MetaM (Prod3 Expr LocalContext LocalInstances) := do
  let .mk (bins,_) l1 l2 ← e.getLnodesToBind l1 l2 #[] {}
  let e ← mkForallFVars bins e
  let e := e.onAllSubtermsTR (fun
    | .sort u => .sort <| u.onAllSubtermsTR (fun
        | .mvar m => .param m.name
        | x => x
        )
    | .const n l => .const n <| l.map (fun u =>
      u.onAllSubtermsTR (fun
        | .mvar m => .param m.name
        | x => x
        ))
    | x => x
      )
  return .mk e l1 l2



@[specialize, inline]
partial def cvb_thmConj_genConj [Repr IdxCollType]
  (fold : ∀ {β : Type _}, IdxCollType → (init : β) → (f : Nat → β → β) → β) (empty : IdxCollType)
  (insert : Nat → IdxCollType → IdxCollType)
  (insertMulti intersect union difference : IdxCollType → IdxCollType → IdxCollType) (empty? : IdxCollType → Bool)
  (size : IdxCollType → Nat) (contains : Nat → IdxCollType → Bool)
  (l1 : LocalContext) (l2 : LocalInstances)
  (genCondition : (occWeight : Nat) → (branchWeight : Nat) → (branchDistrib : Array Nat) → (commonType : Expr) → (branchDepth : Nat) → Bool)
  (freqCondition : (occWeight : Nat) → (branchWeight : Nat) → (branchDistrib : Array Nat) → (branchDepth : Nat) → Bool)
  (samIdx : Nat) (conjPain : PaIn IdxCollType)
  (sampleName : Name) (allTypes cleanTypes : Array Expr)
  : MetaM (Prod3 (ListProd ThmFormat Nat) (Array Expr) (Array Expr)) := do
    mtracing
    let weights := Array.replicate samIdx (1 : Nat)
    mtrace on .zero with s!" generalising"
    let .mk freqInd T allTypes l1 l2 ← generalizePaInCoreMulti
      fold empty insertMulti intersect union difference empty? l1 l2 genCondition freqCondition sampleName
      conjPain weights allTypes
    mtrace on .one with s!" generalised PaIn {← T.pp l1 l2 [] 0 intersect empty?}"
    mtrace on .zero with s!" found freqInd {repr freqInd}, deduplicating"
    let .mk T weights _ ← T.dedup insert union empty size contains fold weights freqInd
    mtrace on .zero with s!" running lnode garbadge collection"
    let (T,cleanTypes,_) := lnodeGarbageCollectionMulti T allTypes cleanTypes
    let build ← T.buildAllTop l1 l2 intersect empty?
    let (res,_) ← build.foldlM ((ListProd.nil : ListProd ThmFormat Nat),0) (fun e is (R,i) => do
      let w := getCPIweights fold weights is
      let r ← e.bindLnodes_makeLevelPara l1 l2
      let .mk _ f _ _ ← processForMainSpe l1 l2 (.num sampleName i) i (.inl <| (.num sampleName i)) #[] 0 r.1 .both
      -- ↑↓ make this more tailored
      let f :=
        match f with
        | .cons _ f _ => f
        | _ => panic! "[cvb_thmConj_genConj] failed process ??"
      return (ListProd.cons f w R,i+1)
      )
    return .mk res allTypes cleanTypes

#check 1


@[specialize, inline]
partial def cvb_thmConj_genMain [Repr IdxCollType]
  (fold : ∀ {β : Type _}, IdxCollType → (init : β) → (f : Nat → β → β) → β) (empty : IdxCollType)
  (insert : Nat → IdxCollType → IdxCollType)
  (insertMulti intersect union difference : IdxCollType → IdxCollType → IdxCollType) (empty? : IdxCollType → Bool)
  (size : IdxCollType → Nat) (contains : Nat → IdxCollType → Bool)
  (l1 : LocalContext) (l2 : LocalInstances)
  (genCondition : (occWeight : Nat) → (branchWeight : Nat) → (branchDistrib : Array Nat) → (commonType : Expr) → (branchDepth : Nat) → Bool)
  (freqCondition : (occWeight : Nat) → (branchWeight : Nat) → (branchDistrib : Array Nat) → (branchDepth : Nat) → Bool)
  (sampleName : Name) (allTypes cleanTypesGH cleanTypesC : Array Expr)
  (sorted : (CTrie (Prod6 Nat Nat (ListProd Nat (List Nat)) (PaIn IdxCollType) (PaIn IdxCollType) (Array (Nat × PaIn IdxCollType)))))
  : MetaM ((Prod3 (Array Expr) (Array Expr) (Array Expr)) × (CTrie (Prod3 (thmGenDataEntry IdxCollType) Nat (Array (ListProd ThmFormat Nat))))) := do
    sorted.foldMapM (.mk allTypes cleanTypesGH cleanTypesC ) (fun entry (.mk allTypes cleanTypesGH cleanTypesC ) => do
      let .mk gT gW gw _ allTypes cleanTypesGH ← cvb_thms_genGoal
        fold empty insert insertMulti intersect union difference
        empty? size contains l1 l2 genCondition freqCondition
        entry.1 entry.4 sampleName allTypes cleanTypesGH
      let .mk hT hw _ allTypes cleanTypesGH ← cvb_thms_genHyps
        fold empty insert insertMulti intersect union difference
        empty? size contains l1 l2 genCondition freqCondition
        entry.2 entry.5 entry.3 sampleName allTypes cleanTypesGH
      let .mk allTypes cleanTypesC total conjs ← entry.6.foldlM (fun (.mk allTypes cleanTypesC total A) (samIdx,T) => do
        let .mk res allTypes cleanTypesC ← cvb_thmConj_genConj
          fold empty insert insertMulti intersect union difference
          empty? size contains l1 l2 genCondition freqCondition
          samIdx T sampleName allTypes cleanTypesC
        return (Prod4.mk allTypes cleanTypesC total (A.push res) )
        ) (Prod4.mk allTypes cleanTypesC 0 (Array.emptyWithCapacity entry.6.size))
      return ((.mk allTypes cleanTypesGH cleanTypesC), .some (.mk (.mk gT gW gw hT hw) total conjs))
      )

#check 1

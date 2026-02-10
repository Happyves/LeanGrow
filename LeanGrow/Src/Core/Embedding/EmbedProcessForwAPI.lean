
/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/


import LeanGrow.Src.Core.Embedding.EmbedQueryForwInclude
import LeanGrow.Src.Search.IntroTree.Types
import LeanGrow.Src.Data.SetTrie.Specialize
import LeanGrow.Src.Data.PathIndexG.Operations


open Lean Meta

variable {IndexColType : Type}

structure embedForwData where
  thm : ThmFormat
  embedSofar :  Array Expr
  paramsSofar : Array Level
  unassignedNodes : List Nat
  unassignedParams : List Nat
deriving Inhabited


@[specialize, inline]
def embedPropaInclude [Repr IndexColType]
  (intersect : IndexColType → IndexColType → IndexColType) (empty? : IndexColType → Bool)
  (fold : ∀ {β : Type _}, IndexColType → (init : β) → (f : Nat → β → β) → β)
  (foldM : ∀ {β : Type _}, IndexColType → (init : β) → (f : Nat → β → MetaM β) → MetaM β)
  (stdForwSetTrie_idxToSinkIdx : Array Nat)
  (hypIndToThm : Nat → ThmFormat) (thmToInds : Name → IndexColType) (unode? : Nat → Bool)
  (l1 : LocalContext) (l2 : LocalInstances)
  (sofar : ListProd IndexColType embedForwData)
  (out : ListProd3 IndexColType IndexColType ((ListProd Nat Expr) × (ListProd Nat Level)))
  : MetaM (ListProd IndexColType embedForwData) :=
    do
    mtracing
    mtrace on .zero with s!"[embedPropaInclude] sofar: {← sofar.foldlM "" (fun is emb S => return S ++ s!"\n{repr is} {repr emb.thm.name} {← emb.embedSofar.mapM ppExpr}")}"
    out.foldlM sofar (fun guInds thmHypInds (propaE, propaL) R => do
      mtrace on .zero with s!"[embedPropaInclude] Looking at match guInds {repr guInds} thmHypInds {repr thmHypInds}"
      mtrace on .zero with s!"[embedPropaInclude] with propaE {← propaE.foldlM ListProd.nil (fun x y r => return .cons x (← ppExpr y) r)} and propaL {repr propaL}"
      mtrace on .zero with s!"[embedPropaInclude] R : {← R.foldlM "" (fun is emb S => return S ++ s!"\n{repr is} {repr emb.thm.name} {← emb.embedSofar.mapM ppExpr}")}"
      R.foldlMcps (.nil,false) (fun hI embedForwData (R, found?) q1 => do
        mtrace on .zero with s!"[embedPropaInclude] Looking at embed with hyp-ids signature {repr hI}"
        if empty? (intersect hI thmHypInds)
        then
          mtrace on .zero with s!"[embedPropaInclude] skiped"
          q1 (.cons hI embedForwData R, found?)
        else
          mtrace on .zero with s!"[embedPropaInclude] extending"
          let blue := embedForwData
          propaE.foldlMcps blue (fun p V blue q2 => do
            if blue.unassignedNodes.contains p
            then
              mtrace on .zero with s!"[embedPropaInclude] extended arg {p} with value {← ppExpr V}"
              q2 {blue with embedSofar := blue.embedSofar.set! p V, unassignedNodes := blue.unassignedNodes.erase p}
            else
              if (← defEqWiMv V blue.embedSofar[p]! l1 l2).isSome
              then
                mtrace on .zero with s!"[embedPropaInclude] positive coherence defeq"
                q2 blue
              else
                mtrace on .zero with s!"[embedPropaInclude] negative coherence defeq between →, aborting :\n V : {← ppExpr V} \n blue.embedSofar[p]! : {← ppExpr blue.embedSofar[p]!} "
                q1 (.cons hI embedForwData R, true)
                -- so we keep the embed so far, but don't extend it
            ) <| fun blue => do
              propaL.foldlMcps blue (fun p V blue q2 => do
                if blue.unassignedParams.contains p
                then
                  mtrace on .zero with s!"[embedPropaInclude] extended level {p} with value {repr V}"
                  q2 {blue with paramsSofar := blue.paramsSofar.set! p V, unassignedParams:= blue.unassignedParams.erase p}
                else
                  if ← (do let res ← isLevelDefEq V blue.paramsSofar[p]! ; clearMvarAssignments ; return res)
                  then
                    mtrace on .zero with s!"[embedPropaInclude] positive coherence defeq"
                    q2 blue
                  else
                    mtrace on .zero with s!"[embedPropaInclude] negative coherence defeq between →, aborting :\n V : {repr V} \n blue.paramsSofar[p]! : {repr blue.paramsSofar[p]!} "
                    q1 (.cons hI embedForwData R, true)
                ) <| fun blue => do
                  let opts : List Expr := fold guInds [] (fun i L =>
                    if unode? i
                    then (.fvar ⟨unode i⟩) :: L
                    else (.fvar ⟨gnode i⟩) :: L
                    )
                  mtrace on .zero with s!"[embedPropaInclude] sink opts {repr opts}"
                  let N := .cons hI embedForwData R -- we keep the embedding without extentions, so that it can be extended further in other branches of the intro tree ?
                  let N ← foldM thmHypInds N (fun hypIdx N => do
                    let thm := hypIndToThm hypIdx
                    let hI := thmToInds (match thm.name with | .inl n => n | .inr e => e.name)
                    let hypIdx := stdForwSetTrie_idxToSinkIdx[hypIdx]!
                    mtrace on .zero with s!"[embedPropaInclude] assigning sink {hypIdx}"
                    let mut Nm := N
                    for o in opts do
                      mtrace on .zero with s!"[embedPropaInclude] adding it withoption sink {o}"
                      let here :=  {blue with embedSofar := blue.embedSofar.set! hypIdx o, unassignedNodes := blue.unassignedNodes.erase hypIdx}
                      Nm := .cons hI here Nm
                    return Nm
                    )
                  q1 (N, true)
        ) <| fun (R, found?) => do
          if found?
          then
            mtrace on .zero with s!"[embedPropaInclude] theorem corresponding tothmHypInds {repr thmHypInds} is/was present, not adding it"
            return R
          else
            foldM thmHypInds R (fun hypIdx N => do
              let thm := hypIndToThm hypIdx
              let hI := thmToInds (match thm.name with | .inl n => n | .inr e => e.name)
              mtrace on .zero with s!"[embedPropaInclude] adding embed candidate for thm {repr thm.name}"
              let freshembedForwDataBlue : embedForwData :=
                {thm := thm
                 embedSofar := propaE.foldl (Array.replicate thm.hypsNum (failExpr "embedPropaInclude")) (fun p V A => A.set! p V)
                 paramsSofar := propaL.foldl (Array.replicate thm.lvlParamsNum (.zero)) (fun p V A => A.set! p V)
                 unassignedNodes := propaE.foldl (List.range thm.hypsNum) (fun p _ A => A.erase p)
                 unassignedParams := propaL.foldl (List.range thm.lvlParamsNum) (fun p _ A => A.erase p)
                }
              let opts : List Expr := fold guInds [] (fun i L =>
                if unode? i
                then (.fvar ⟨unode i⟩) :: L
                else (.fvar ⟨gnode i⟩) :: L
                )
              let hypIdx := stdForwSetTrie_idxToSinkIdx[hypIdx]!
              mtrace on .zero with s!"[embedPropaInclude] assigning sink {hypIdx}"
              let mut Nm := N
              for o in opts do
                mtrace on .zero with s!"[embedPropaInclude] adding it withoption sink {o}"
                let here :=  {freshembedForwDataBlue with embedSofar := freshembedForwDataBlue.embedSofar.set! hypIdx o, unassignedNodes := freshembedForwDataBlue.unassignedNodes.erase hypIdx}
                Nm := .cons hI here Nm
              return Nm
            )
          )


#check PaInG.pp


@[specialize, inline]
partial def embedForwIncludeMain
  (thmembedForwData : CTrie (Array ThmFormat)) [Repr IndexColType]
  (fold : ∀ {β : Type _}, IndexColType → (init : β) → (f : Nat → β → β) → β)
  (foldM : ∀ {β : Type _}, IndexColType → (init : β) → (f : Nat → β → MetaM β) → MetaM β)
  (insert : Nat → IndexColType → IndexColType)
  (intersect union difference : IndexColType → IndexColType → IndexColType)
  (empty? : IndexColType → Bool) (emptyCol : IndexColType)
  (stdForwSetTrie_idxToSinkIdx : Array Nat)
  (thm_data : Array ThmFormat) (stdForwSetTrie_idxToThmIdx : Array Nat)
  (thmNameToHypIdx : CTrie IndexColType) (uNodes : Array Nat)
  (l1 : LocalContext)
  (Q' : IntroTree IndexColType) (T : SetTrieP ThmFormat IndexColType PaInG)
  : MetaM <| ListProd4 LocalInstances IndexColType (PaInG IndexColType) embedForwData :=
  do
  mtracing
  let hypIndToThm : Nat → ThmFormat :=
    (fun i => let j := stdForwSetTrie_idxToThmIdx[i]! ; thm_data[j]!)
  let thmToInds : Name → IndexColType := (fun n =>
      match thmNameToHypIdx.find? n.toString.toUTF8 with
      | .none => emptyCol
      | .some ids => ids)
  let unode? : Nat → Bool :=
    (fun i => uNodes.binSearchContains i (· < · ))
  let rec @[specialize] findSplit
    (done : ListProd4 LocalInstances (List (IntroTree IndexColType)) (PaInG IndexColType) (ListProd IndexColType embedForwData))
    (t : PaInG IndexColType)
    : ListProd3 ((IntroTree IndexColType)) (PaInG IndexColType) (ListProd IndexColType embedForwData) →
        MetaM (ListProd4 LocalInstances (List (IntroTree IndexColType)) (PaInG IndexColType) (ListProd IndexColType embedForwData))
    | .nil => return done
    | .cons Q sf embs more => do
        match Q with
        | .leaf l2 _ _ _ q =>
            let msf := ((PaInG.merge union emptyCol) q sf)
            mtrace on .zero with s!"[findSplit] run embedForwIncludeCore on:\n msf : {← msf.pp l1 l2 [] 0 intersect empty?}\n t : {← t.pp l1 l2 [] 0 intersect empty?}"
            match ← PaInG.embedForwIncludeCore thmembedForwData intersect difference empty? l1 l2 msf t with
            | .nil =>
                mtrace on .zero with s!"[findSplit] nil"
                findSplit done t more
            | Ms =>
                mtrace on .zero with s!"[findSplit] propagate"
                let nembs ← embedPropaInclude intersect empty? fold foldM stdForwSetTrie_idxToSinkIdx hypIndToThm thmToInds unode? l1 l2 embs Ms
                match nembs with
                | .nil =>
                    mtrace on .zero with s!"[findSplit] nil after propa"
                    findSplit done t more
                | _ =>
                    mtrace on .zero with s!"[findSplit] proceed"
                    findSplit (.cons l2 [] msf nembs done) t more
        | .node l2 _ _ _ q kids =>
            let msf := ((PaInG.merge union emptyCol) q sf)
            mtrace on .zero with s!"[findSplit] run embedForwIncludeCore on:\n msf : {← msf.pp l1 l2 [] 0 intersect empty?}\n t : {← t.pp l1 l2 [] 0 intersect empty?}"
            match ← PaInG.embedForwIncludeCore thmembedForwData intersect difference empty? l1 l2 msf t with
            | .nil =>
                mtrace on .zero with s!"[findSplit] nil"
                findSplit done t (kids.foldl more (fun _ _ k R => .cons k msf embs R))
            | Ms =>
                mtrace on .zero with s!"[findSplit] propagate"
                let nembs ← embedPropaInclude intersect empty? fold foldM stdForwSetTrie_idxToSinkIdx  hypIndToThm thmToInds unode? l1 l2 embs Ms
                match nembs with
                | .nil =>
                    mtrace on .zero with s!"[findSplit] nil after propa"
                    findSplit done t (kids.foldl more (fun _ _ k R => .cons k msf embs R))
                | _ =>
                    mtrace on .zero with s!"[findSplit] proceed"
                    findSplit (.cons l2 (kids.foldl [] (fun _ _ y R => y :: R)) msf nembs done) t more
  let rec @[specialize] go (done : ListProd4 LocalInstances IndexColType (PaInG IndexColType) embedForwData) :
    ListProd5 (SetTrieP ThmFormat IndexColType PaInG) (Option (IntroTree IndexColType)) LocalInstances (PaInG IndexColType) (ListProd IndexColType embedForwData)
      → MetaM (ListProd4 LocalInstances IndexColType (PaInG IndexColType) embedForwData)
    | .nil => return done
    | .cons T (.some Q) l2 sf embs more => do
        match T with
        | .root t c =>
            mtrace on .zero with s!"[embedForwIncludeMain] run embedForwIncludeCore on:\n sf : {← sf.pp l1 l2 [] 0 intersect empty?}\n t : {← t.pp l1 l2 [] 0 intersect empty?}"
            match ← PaInG.embedForwInterCore thmembedForwData intersect difference empty? l1 l2 sf t with
            | .nil =>
                mtrace on .zero with s!"[embedForwIncludeMain] not found in prior, going forward with findSplit"
                let nxs ← findSplit .nil t (.cons Q sf embs .nil)
                let nxsf := nxs.foldl more (fun ll2 its sf emb R =>
                  match its with
                  | [] => c.foldl (fun R c => .cons c .none (l2 ++ ll2) sf emb R) R
                  | _ => c.foldl (fun R c => its.foldl (fun R it => .cons c (.some it) (l2 ++ ll2) sf emb R) R) R
                  )
                go done nxsf
            | Ms =>
                let nembs ← embedPropaInclude intersect empty? fold foldM stdForwSetTrie_idxToSinkIdx  hypIndToThm thmToInds unode? l1 l2 embs Ms
                match nembs with
                | .nil =>
                    mtrace on .zero with s!"[embedForwIncludeMain] found in prior, but inconcistent, going forward with findSplit"
                    let nxs ← findSplit .nil t (.cons Q sf embs .nil)
                    let nxsf := nxs.foldl more (fun ll2 its sf emb R =>
                      match its with
                      | [] => c.foldl (fun R c => .cons c .none (l2 ++ ll2) sf emb R) R
                      | _ => c.foldl (fun R c => its.foldl (fun R it => .cons c (.some it) (l2 ++ ll2) sf emb R) R) R
                      )
                    go done nxsf
                | _ =>
                    go done (c.foldl (fun R st => .cons st (.some Q) l2 sf nembs R) more)
        | .node _ t c =>
            mtrace on .zero with s!"[embedForwIncludeMain] run embedForwIncludeCore on:\n sf : {← sf.pp l1 l2 [] 0 intersect empty?}\n t : {← t.pp l1 l2 [] 0 intersect empty?}"
            match ← PaInG.embedForwIncludeCore thmembedForwData intersect difference empty? l1 l2 sf t with
            | .nil =>
                mtrace on .zero with s!"[embedForwIncludeMain] not found in prior, going forward with findSplit"
                let nxs ← findSplit .nil t (.cons Q sf embs .nil)
                let nxsf := nxs.foldl more (fun ll2 its sf emb R =>
                  match its with
                  | [] => c.foldl (fun R c => .cons c .none (l2 ++ ll2) sf emb R) R
                  | _ => c.foldl (fun R c => its.foldl (fun R it => .cons c (.some it) (l2 ++ ll2) sf emb R) R) R
                  )
                go done nxsf
            | Ms =>
                let nembs ← embedPropaInclude intersect empty? fold foldM stdForwSetTrie_idxToSinkIdx  hypIndToThm thmToInds unode? l1 l2 embs Ms
                match nembs with
                | .nil =>
                    mtrace on .zero with s!"[embedForwIncludeMain] found in prior, but inconcistent, going forward with findSplit"
                    let nxs ← findSplit .nil t (.cons Q sf embs .nil)
                    let nxsf := nxs.foldl more (fun ll2 its sf emb R =>
                      match its with
                      | [] => c.foldl (fun R c => .cons c .none (l2 ++ ll2) sf emb R) R
                      | _ => c.foldl (fun R c => its.foldl (fun R it => .cons c (.some it) (l2 ++ ll2) sf emb R) R) R
                      )
                    go done nxsf
                | _ =>
                    go done (c.foldl (fun R st => .cons st (.some Q) l2 sf nembs R) more)
        | .leaf thm =>
            let hI := thmToInds (match thm.name with | .inl n => n | .inr e => e.name)
            go (embs.foldl done (fun x y z =>
              if empty? (intersect hI x)
              then z
              else .cons l2 x sf y z)) more
    | .cons T .none l2 sf embs more => do
        match T with
        | .root t c =>
            mtrace on .zero with s!"[embedForwIncludeMain] run embedForwIncludeCore on:\n sf : {← sf.pp l1 l2 [] 0 intersect empty?}\n t : {← t.pp l1 l2 [] 0 intersect empty?}"
            match ← PaInG.embedForwInterCore thmembedForwData intersect difference empty? l1 l2 sf t with
            | .nil =>
                go done more
            | Ms =>
                let nembs ← embedPropaInclude intersect empty? fold foldM stdForwSetTrie_idxToSinkIdx  hypIndToThm thmToInds unode? l1 l2 embs Ms
                match nembs with
                | .nil =>
                    go done more
                | _ =>
                    go done (c.foldl (fun R st => .cons st .none  l2 sf nembs R) more)
        | .node _ t c =>
            mtrace on .zero with s!"[embedForwIncludeMain] run embedForwIncludeCore on:\n sf : {← sf.pp l1 l2 [] 0 intersect empty?}\n t : {← t.pp l1 l2 [] 0 intersect empty?}"
            match ← PaInG.embedForwInterCore thmembedForwData intersect difference empty? l1 l2 sf t with
            | .nil =>
                go done more
            | Ms =>
                let nembs ← embedPropaInclude intersect empty? fold foldM stdForwSetTrie_idxToSinkIdx  hypIndToThm thmToInds unode? l1 l2 embs Ms
                match nembs with
                | .nil =>
                    go done more
                | _ =>
                    go done (c.foldl (fun R st => .cons st .none  l2 sf nembs R) more)
        | .leaf thm =>
            let hI := thmToInds (match thm.name with | .inl n => n | .inr e => e.name)
            go (embs.foldl done (fun x y z =>
              if empty? (intersect hI x)
              then z
              else .cons l2 x sf y z)) more
  do
  clearMvarAssignments
  go .nil (.cons T Q' #[] .dead .nil .nil)


#check 1
#check PaInG.embedForwInterCore
#check PaInG.embedForwIncludeCore



/--
To add the term to the introtree, use the list of the sink-u-g-nodes:
use u-g-dirs to find sinks, stop when all are found : this is the spot

**New** check if term is instance, and if so, add it to instances of intro tree branch
-/
@[inline]
def embedForwIncludePostProcess' -- ' to remeber todo
  (l1 : LocalContext)
  (L : ListProd4 LocalInstances IndexColType (PaInG IndexColType) embedForwData )
  : MetaM <| ListProd3 Expr (PaInG IndexColType) (List Nat) :=
    do
    mtracing
    L.foldlM .nil (fun l2 _ ltxPaInG data R => do
      mtrace on .zero with s!"[embedForwIncludePostProcess] looking at data for thm {repr data.thm.name}"
      if !data.unassignedParams.isEmpty
      then
        mtrace on .zero with s!"[embedForwIncludePostProcess] unassigned level, dumping"
        return R
      else
        let mut asf := data.embedSofar
        for p in data.unassignedNodes do
          match data.thm.hyps[p]! with
          | .reg .. =>
            mtrace on .zero with s!"[embedForwIncludePostProcess] unassigned arg {p}, dumping"
            return R
          | .inst T =>
              let T := T.onAllSubtermsTR (fun
                | .mvar ⟨.num _ i⟩ => asf[i]!
                | .sort lv => .sort <| lv.onAllSubtermsTR (fun
                    | .mvar ⟨.num _ i ⟩ => data.paramsSofar[i]!
                    | x => x)
                | .const n lv => .const n <| lv.map <| fun lv => lv.onAllSubtermsTR (fun
                    | .mvar ⟨.num _ i ⟩ => data.paramsSofar[i]!
                    | x => x)
                | x => x )
              mtrace on .zero with s!"[embedForwIncludePostProcess] trying to synthesise instance for {← ppExpr T}"
              let .some val ← (SynthInstance T l1 l2) | return R
              -- *Note* bug potential : instance who's type contains a instance mvar can fail to be synthesised if data.unassignedNodes isn't oredered
              mtrace on .zero with s!"[embedForwIncludePostProcess] success"
              asf := asf.set! p val
        let term := mkAppN (match data.thm.name with | .inl n =>(.const n data.paramsSofar.toList) | .inr fv => .fvar fv) asf
        let mut sinkGUinds := []
        for p in data.thm.sinks do
          match data.thm.hyps[p]! with
          | .inst .. => continue
          | .reg .. =>
            let A := asf[p]!
            match A with
            | .fvar ⟨.num _ i⟩ => sinkGUinds := i :: sinkGUinds
            | _ => throwError s!"[embedForwIncludePostProcess] we expect sinks to have u-g-nodes as args only, instead we have {← ppExpr A}"
        mtrace on .zero with s!"[embedForwIncludePostProcess] term {← ppExpr term} of type {← ppExpr (← inferType term)}"
        mtrace on .zero with s!"[embedForwIncludePostProcess] sinkGUinds {sinkGUinds}"
        return .cons term ltxPaInG sinkGUinds R
      )


#check PaInG.merge

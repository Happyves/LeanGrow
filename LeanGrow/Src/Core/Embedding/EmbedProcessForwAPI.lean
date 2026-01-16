
/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/


import LeanGrowBeta.Core.Embedding.EmbedQueryForwInclude
import LeanGrowBeta.Search.IntroTree.Types
import LeanGrowBeta.Data.SetTrie.Operations
import LeanGrowBeta.Data.PathIndex.Operations


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
def akwardFindSinkPosFromHypIdx
  (toList : IndexColType → List Nat)
  (thm : ThmFormat) (thmHypInds : IndexColType) (foundHypInd : Nat) : Nat :=
  let thmHypInds := toList thmHypInds
  match thmHypInds.findIdx? (· == foundHypInd) with
  | .none => panic s!"[akwardFindSinkPosFromHypIdx] foundHypInd {foundHypInd} not found in hyp indices {thmHypInds}"
  | .some pp =>
    let sinkPos := thm.sinks.reverse -- sinks where added to hyp-counting in reverse !
    match sinkPos[pp]? with
    | .none => panic s!"[akwardFindSinkPosFromHypIdx] searched for {pp} among sinkPos {sinkPos}"
    | .some pos => pos



@[specialize, inline]
def embedPropaInclude [Repr IndexColType]
  (intersect : IndexColType → IndexColType → IndexColType) (empty? : IndexColType → Bool)
  (toList : IndexColType → List Nat)
  (hypIndToThm : Nat → ThmFormat) (thmToInds : Name → IndexColType) (unode? : Nat → Bool)
  (l1 : LocalContext) (l2 : LocalInstances)
  (sofar : ListProd IndexColType embedForwData)
  (out : ListProd3 IndexColType IndexColType ((ListProd Nat Expr) × (ListProd Nat Level)))
  : MetaM (ListProd IndexColType embedForwData) :=
  do --trace set Tracing.Flags.none in  do
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
                  let opts : List Expr := (toList guInds).mapTRR (fun i =>
                    if unode? i
                    then .fvar ⟨unode i⟩
                    else .fvar ⟨gnode i⟩
                    )
                  mtrace on .zero with s!"[embedPropaInclude] sink opts {repr opts}"
                  let mut N := .cons hI embedForwData R -- we keep the embedding without extentions, so that it can be extended further in other branches of the intro tree ?
                  let explHypInds := (toList thmHypInds)
                  for hypIdx in explHypInds do
                    let thm := hypIndToThm hypIdx
                    let hI := thmToInds (match thm.name with | .inl n => n | .inr e => e.name)
                    mtrace on .zero with s!"[embedPropaInclude] found {repr hI} as hyp-inds-signature for thm"
                    let hypIdx := akwardFindSinkPosFromHypIdx toList thm hI hypIdx
                    mtrace on .zero with s!"[embedPropaInclude] assigning sink {hypIdx}"
                    for o in opts do
                      mtrace on .zero with s!"[embedPropaInclude] adding it withoption sink {o}"
                      let here :=  {blue with embedSofar := blue.embedSofar.set! hypIdx o, unassignedNodes := blue.unassignedNodes.erase hypIdx}
                      N := .cons hI here N
                  q1 (N, true)
        ) <| fun (R, found?) => do
          if found?
          then
            mtrace on .zero with s!"[embedPropaInclude] theorem corresponding tothmHypInds {repr thmHypInds} is/was present, not adding it"
            return R
          else
            let explHypInds := (toList thmHypInds)
            let mut N := R
            for hypIdx in explHypInds do
              let thm := hypIndToThm hypIdx
              mtrace on .zero with s!"[embedPropaInclude] adding embed candidate for thm {repr thm.name}"
              let freshembedForwDataBlue : embedForwData :=
                {thm := thm
                 embedSofar := propaE.foldl (Array.replicate thm.hypsNum (failExpr "embedPropaInclude")) (fun p V A => A.set! p V)
                 paramsSofar := propaL.foldl (Array.replicate thm.lvlParamsNum (.zero)) (fun p V A => A.set! p V)
                 unassignedNodes := propaE.foldl (List.range thm.hypsNum) (fun p _ A => A.erase p)
                 unassignedParams := propaL.foldl (List.range thm.lvlParamsNum) (fun p _ A => A.erase p)
                }
              let opts : List Expr := (toList guInds).mapTRR (fun i =>
                if unode? i
                then .fvar ⟨unode i⟩
                else .fvar ⟨gnode i⟩
                )
              mtrace on .zero with s!"[embedPropaInclude] sink opts {repr opts}"
              let hI := thmToInds (match thm.name with | .inl n => n | .inr e => e.name)
              mtrace on .zero with s!"[embedPropaInclude] found {repr hI} as hyp-inds-signature for thm"
              let hypIdx := akwardFindSinkPosFromHypIdx toList thm hI hypIdx
              mtrace on .zero with s!"[embedPropaInclude] assigning sink {hypIdx}"
              for o in opts do
                mtrace on .zero with s!"[embedPropaInclude] adding it withoption sink {o}"
                let here :=  {freshembedForwDataBlue with embedSofar := freshembedForwDataBlue.embedSofar.set! hypIdx o, unassignedNodes := freshembedForwDataBlue.unassignedNodes.erase hypIdx}
                N := .cons hI here N
            return N
          )


#check PaIn.pp

@[specialize, inline]
partial def embedForwIncludeMain
  (thmembedForwData : CTrie (Array ThmFormat)) [Repr IndexColType]
  (toList : IndexColType → List Nat)
  (hypIndToThm : Nat → ThmFormat) (thmToInds : Name → IndexColType) (unode? : Nat → Bool)
  (intersect union difference : IndexColType → IndexColType → IndexColType) (empty? : IndexColType → Bool) (emptyCol : IndexColType)
  (l1 : LocalContext) (l2 : LocalInstances)
  (Q' : IntroTree IndexColType) (T : SetTrie ThmFormat (PaIn IndexColType))
  : MetaM <| ListProd3 IndexColType (PaIn IndexColType) embedForwData :=
  do --trace set Tracing.Flags.none in
  let rec @[specialize] findSplit
    (done : ListProd3 (List (IntroTree IndexColType)) (PaIn IndexColType) (ListProd IndexColType embedForwData))
    (t : PaIn IndexColType)
    : ListProd3 ((IntroTree IndexColType)) (PaIn IndexColType) (ListProd IndexColType embedForwData) →
        MetaM (ListProd3 (List (IntroTree IndexColType)) (PaIn IndexColType) (ListProd IndexColType embedForwData))
    | .nil => return done
    | .cons Q sf embs more => do
        match Q with
        | .leaf _ _ _ q =>
            let msf := ((PaIn.merge union emptyCol) q sf)
            mtrace on .zero with s!"[findSplit] run embedForwIncludeCore on:\n msf : {← msf.pp l1 l2 [] 0 intersect empty?}\n t : {← t.pp l1 l2 [] 0 intersect empty?}"
            match ← PaIn.embedForwIncludeCore thmembedForwData intersect difference empty? l1 l2 msf t with
            | .nil =>
                mtrace on .zero with s!"[findSplit] nil"
                findSplit done t more
            | Ms =>
                mtrace on .zero with s!"[findSplit] propagate"
                let nembs ← embedPropaInclude intersect empty? toList hypIndToThm thmToInds unode? l1 l2 embs Ms
                match nembs with
                | .nil =>
                    mtrace on .zero with s!"[findSplit] nil after propa"
                    findSplit done t more
                | _ =>
                    mtrace on .zero with s!"[findSplit] proceed"
                    findSplit (.cons [] msf nembs done) t more
        | .node _ _ _ q kids =>
            let msf := ((PaIn.merge union emptyCol) q sf)
            mtrace on .zero with s!"[findSplit] run embedForwIncludeCore on:\n msf : {← msf.pp l1 l2 [] 0 intersect empty?}\n t : {← t.pp l1 l2 [] 0 intersect empty?}"
            match ← PaIn.embedForwIncludeCore thmembedForwData intersect difference empty? l1 l2 msf t with
            | .nil =>
                mtrace on .zero with s!"[findSplit] nil"
                findSplit done t (kids.foldl more (fun _ _ k R => .cons k msf embs R))
            | Ms =>
                mtrace on .zero with s!"[findSplit] propagate"
                let nembs ← embedPropaInclude intersect empty? toList hypIndToThm thmToInds unode? l1 l2 embs Ms
                match nembs with
                | .nil =>
                    mtrace on .zero with s!"[findSplit] nil after propa"
                    findSplit done t (kids.foldl more (fun _ _ k R => .cons k msf embs R))
                | _ =>
                    mtrace on .zero with s!"[findSplit] proceed"
                    findSplit (.cons (kids.foldl [] (fun _ _ y R => y :: R)) msf nembs done) t more
  let rec @[specialize] go (done : ListProd3 IndexColType (PaIn IndexColType) embedForwData) :
    ListProd4 (SetTrie ThmFormat (PaIn IndexColType)) (Option (IntroTree IndexColType)) (PaIn IndexColType) (ListProd IndexColType embedForwData)
      → MetaM (ListProd3 IndexColType (PaIn IndexColType) embedForwData)
    | .nil => return done
    | .cons T (.some Q) sf embs more => do
        match T with
        | .root c =>
            go done (c.foldl (fun R st => .cons st (.some Q) sf embs R) more)
        | .node t c =>
            mtrace on .zero with s!"[embedForwIncludeMain] run embedForwIncludeCore on:\n sf : {← sf.pp l1 l2 [] 0 intersect empty?}\n t : {← t.pp l1 l2 [] 0 intersect empty?}"
            match ← PaIn.embedForwIncludeCore thmembedForwData intersect difference empty? l1 l2 sf t with
            | .nil =>
                mtrace on .zero with s!"[embedForwIncludeMain] not found in prior, going forward with findSplit"
                let nxs ← findSplit .nil t (.cons Q sf embs .nil)
                let nxsf := nxs.foldl more (fun its sf emb R =>
                  match its with
                  | [] => c.foldl (fun R c => .cons c .none sf emb R) R
                  | _ => c.foldl (fun R c => its.foldl (fun R it => .cons c (.some it) sf emb R) R) R
                  )
                go done nxsf
            | Ms =>
                let nembs ← embedPropaInclude intersect empty? toList hypIndToThm thmToInds unode? l1 l2 embs Ms
                match nembs with
                | .nil =>
                    mtrace on .zero with s!"[embedForwIncludeMain] found in prior, but inconcistent, going forward with findSplit"
                    let nxs ← findSplit .nil t (.cons Q sf embs .nil)
                    let nxsf := nxs.foldl more (fun its sf emb R =>
                      match its with
                      | [] => c.foldl (fun R c => .cons c .none sf emb R) R
                      | _ => c.foldl (fun R c => its.foldl (fun R it => .cons c (.some it) sf emb R) R) R
                      )
                    go done nxsf
                | _ =>
                    go done (c.foldl (fun R st => .cons st (.some Q) sf nembs R) more)
        | .leaf thm =>
            let hI := thmToInds (match thm.name with | .inl n => n | .inr e => e.name)
            go (embs.foldl done (fun x y z =>
              if empty? (intersect hI x)
              then z
              else .cons x sf y z)) more
    | .cons T .none sf embs more => do
        match T with
        | .root c =>
            go done (c.foldl (fun R st => .cons st .none sf embs R) more)
        | .node t c =>
            mtrace on .zero with s!"[embedForwIncludeMain] run embedForwIncludeCore on:\n sf : {← sf.pp l1 l2 [] 0 intersect empty?}\n t : {← t.pp l1 l2 [] 0 intersect empty?}"
            match ← PaIn.embedForwIncludeCore thmembedForwData intersect difference empty? l1 l2 sf t with
            | .nil =>
                go done more
            | Ms =>
                let nembs ← embedPropaInclude intersect empty? toList hypIndToThm thmToInds unode? l1 l2 embs Ms
                match nembs with
                | .nil =>
                    go done more
                | _ =>
                    go done (c.foldl (fun R st => .cons st .none sf nembs R) more)
        | .leaf thm =>
            let hI := thmToInds (match thm.name with | .inl n => n | .inr e => e.name)
            go (embs.foldl done (fun x y z =>
              if empty? (intersect hI x)
              then z
              else .cons x sf y z)) more
  do
  clearMvarAssignments
  go .nil (.cons T Q' .dead .nil .nil)


#check 1



/--
To add the term to the introtree, use the list of the sink-u-g-nodes:
use u-g-dirs to find sinks, stop when all are found : this is the spot
-/
@[inline]
def embedForwIncludePostProcess
  (l1 : LocalContext) (l2 : LocalInstances)
  (L : ListProd3 IndexColType (PaIn IndexColType) embedForwData )
  : MetaM <| ListProd3 Expr (PaIn IndexColType) (List Nat) :=
    do --trace set Tracing.Flags.none in
    L.foldlM .nil (fun _ ltxPaIn data R => do
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
        return .cons term ltxPaIn sinkGUinds R
      )


#check PaIn.merge

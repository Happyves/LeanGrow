

/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/
import LeanGrow.Src.Search.Search
import LeanGrow.Src.Caching.Query.Load
import LeanGrow.Src.Caching.NonStrucIndunction

open Lean System IO FS Process Elab Parser Meta


#check introMain
#check integratePropaedGoalStd

#check PaInG.insertS

#check  registerEnvExtension

#check Lean.Meta.Ext.extExtension
#check Lean.EnvExtension.getState
#check Lean.EnvExtension.setState
#check Lean.EnvExtension.modifyState


#check 1

structure GrowExtCore where
  cfg : SearchConfig UInt32Array
  levelNums : Array (Name × Nat)
  types : Array (Name × (Array Expr))
  thm_data : Array ThmFormat
  thmData : CTrie (Array ThmFormat)
  stdBackPaInG : PaInG UInt32Array
  stdForwSetTrie : SetTrieP ThmFormat UInt32Array PaInG
  stdForwSetTrie_idxToThmIdx : Array Nat
  stdForwSetTrie_idxToSinkIdx : Array Nat
  rwBackPaInG : PaInG UInt32Array
  rwForwPaInG : PaInG UInt32Array
  thmNameToThmIdx : CTrie UInt32Array
  thmNameToHypIdx : CTrie UInt32Array
  -- mainModuleThm : CTrie Unit
  dataCacheRegions : Array CompactedRegion
  scoreCacheRegions : Array CompactedRegion
deriving Inhabited

inductive GrowExt where
| none
| basic (main : GrowExtCore)
deriving Inhabited



initialize GrowExtImpl : EnvExtension GrowExt ← registerEnvExtension (pure .none)

#check 1
#check ModuleCacheState.mergeMain
#check UInt32Array.shiftAdd


def  ModuleCacheState.mergeMainS :=
  ModuleCacheState.mergeMain
    UInt32Array.union UInt32Array.empty
    (fun x y => y.shiftAdd x.toUInt32)

#check 1



-- # TODO: Port




#check 1

unsafe def mkGrowExtCore (cfg : SearchConfig UInt32Array) : MetaM Unit :=
  do
  mtracing
  let commandref ← getRef
  let mut msg := "[mkGrowExtCore] Diagnostics:\n"
  let env ← getEnv
  let imports := env.allImportedModuleNames
  let cachePath ← findLeanGrowCacheDir
  let mut regs : Array CompactedRegion := #[]
  -- Adding standard theorems
  let mut data : ListProd Name (ModuleCacheState UInt32Array) := .nil
  msg := msg ++ "[mkGrowExtCore] The following modules have no pre-process-caches : `grow` will not be able to use their declaratiions.\nModules:\n"
  for module in imports do
    mtrace on .zero with s!"[mkGrowExtCore] (std) looking at {module}"
    let path := FilePath.join cachePath ⟨LeanGrow.mkCacheName module⟩
    if ← path.pathExists
    then
      let (x, region) ← unpickle (ModuleCacheState UInt32Array) path
      regs := regs.push region
      data := .cons module x data
    else
      msg := msg ++ s!"   {module}"
  let mergeData ← ModuleCacheState.mergeMainS data
  let thm_data : Array ThmFormat := mergeData.data.thm_data
  let thmData : CTrie (Array ThmFormat) := mergeData.thmData
  let stdBackPaIn : PaInG UInt32Array := mergeData.data.stdBackPaIn
  let stdForwSetTrie : SetTrieP ThmFormat UInt32Array PaInG := mergeData.data.stdForwSetTrie
  let stdForwSetTrie_idxToThmIdx : Array Nat := mergeData.data.stdForwSetTrie_idxToThmIdx
  let stdForwSetTrie_idxToSinkIdx : Array Nat := mergeData.data.stdForwSetTrie_idxToSinkIdx
  let rwBackPaIn : PaInG UInt32Array := mergeData.data.rwBackPaIn
  let rwForwPaIn : PaInG UInt32Array := mergeData.data.rwForwPaIn
  let thmNameToIdx : CTrie UInt32Array := mergeData.data.thmNameToIdx
  let thmNameToHypIdx : CTrie UInt32Array := mergeData.data.thmNameToHypIdx
  -- Adding functional induction and eliminators
  let mut funrecus : CTrie FunRecursorCache := CTrie.empty
  let mut elimrecus : CTrie (List RecursorCache) := CTrie.empty
  msg := msg ++ "[mkGrowExtCore] The following modules have no pre-process-caches for functional induction and eliminators : `grow` will not be able to use these principles from these files.\nModules:\n"
  for module in imports do
    mtrace on .zero with s!"[mkGrowExtCore] (recu) looking at {module}"
    let path := FilePath.join cachePath ⟨LeanGrow.mkRecuCacheName module⟩
    if ← path.pathExists
    then
      let (x, region) ← unpickle RecursorCachePickle path
      regs := regs.push region
      funrecus := funrecus.merge (fun x _ => x) x.funrecu
      elimrecus := elimrecus.merge (fun x _ => x) x.elimrecu
    else
      msg := msg ++ s!"   {module}"
  logInfoAt commandref msg
  let cfg := {cfg with funrecus := funrecus, elimrecus := elimrecus}
  let D : GrowExtCore := ⟨cfg, #[], #[], thm_data, thmData, stdBackPaIn, stdForwSetTrie, stdForwSetTrie_idxToThmIdx, stdForwSetTrie_idxToSinkIdx, rwBackPaIn, rwForwPaIn, thmNameToIdx, thmNameToHypIdx , regs, #[]⟩
  let nenv := GrowExtImpl.setState env (.basic D)
  setEnv nenv


#check SearchConfig

elab "grow_load_data" cfg:term : command => unsafe do
  Command.liftTermElabM do
    let cfg ← Term.evalTerm (SearchConfig UInt32Array) ((Expr.const `SearchConfig []).app (.const `UInt32Array [])) cfg
    mkGrowExtCore cfg

#check Term.evalTerm
#check Array
#check FilePath





def LeanGrow_ErrorMsg_loadScoreWithoutCore :=
  "[Grow] Please load the pre-process-data caches before executing this operation, via X (implemented by `mkGrowExtCore`)"



unsafe def mkGrowExtScore (freeOld? : Bool) (scoreCachePaths : Array FilePath) : MetaM Unit :=
  do
  mtracing
  let commandref ← getRef
  let mut msg := "[mkGrowExtScore] Diagnostics:\n"
  let env ← getEnv
  let imports := env.allImportedModuleNames
  let importsTrie := CTrie.ofListKeys imports.toList
  match GrowExtImpl.getState env with
  | .none => throwError LeanGrow_ErrorMsg_loadScoreWithoutCore
  | .basic D =>
      if freeOld?
      then
        for r in D.scoreCacheRegions do
          r.free
      msg := msg ++ "[mkGrowExtCore] The following score-caches are invalid, as they require imports that aren't present, and will not be loaded.\nCache filepaths and missing imports:\n"
      let mut levelNums : Array (Name × Nat) := #[]
      let mut types : Array (Name × (Array Expr)) := #[]
      let mut regularBack : CTrie (thmGenDataEntry UInt32Array) := {}
      let mut regularForw : CTrie (thmGenDataEntry UInt32Array)  := {}
      let mut subpat : CTrie (Prod3 (PaIn UInt32Array ) (Array Nat) Nat)  := {}
      let mut conj : CTrie (Prod3 (thmGenDataEntry UInt32Array ) Nat (Array (ListProd ThmFormat Nat))) := {}
      let mut regs : Array CompactedRegion := #[]
      for scoreCacheP in scoreCachePaths do
        let (x, region) ← unpickle (scoreThmKey UInt32Array) scoreCacheP
        -- **Todo** restore tracking required imports and throwing error here
        -- let missed := CTrie.clean <| CTrie.difference x.requiredImportModuleNames importsTrie
        -- if missed == .empty
        -- then
        --   msg := msg ++ s!"   {scoreCacheP}\n   {missed.keys}\n"
        regs := regs.push region
        levelNums := levelNums.push (x.sampleName, x.levelNum)
        types := types.push (x.sampleName, x.types)
        -- **Todo** merge data
        -- regularBack := ← regularBack.mergeM
      logInfoAt commandref msg
      -- let nenv := GrowExtImpl.setState env (.basic {D with cfg := {D.cfg with subpat := subpat, thmPatternScores := thmPatternScores}, scoreCacheRegions := if freeOld? then regs else D.scoreCacheRegions ++ regs})
      -- setEnv nenv

#check CTrie.mapM
#check Lean.EnvExtension.modifyState


-- #exit


elab "grow_load_score" freeOld?:term scoreCachePaths:term : command => unsafe do
  Command.liftTermElabM do
    let freeOld? ← Term.evalTerm Bool ((.const `Bool [])) freeOld?
    let scoreCachePaths ← Term.evalTerm (Array FilePath) (.app (.const `Array [0]) (.const `System.FilePath [])) scoreCachePaths
    mkGrowExtScore freeOld? scoreCachePaths



#check Environment.declsInModuleIdx
#check Environment.mainModule
#check Environment.getModuleIdx?


#exit

-- **Todo** model after buildCachDataForCore, or refactor the latter since it's also used at intro ...

@[specialize]
def helpBuildLocal (env : Environment) (module : Name) (cinfoNs : List Name) (sofarBack : PaInG UInt32Array) (formatsCumul formatsHere : Array ThmFormat)
    (sofarBackRW : PaInG UInt32Array) (countThm : Nat) (sofarFwd : SetTrie ThmFormat (PaInG UInt32Array))
    (hyptothm : Array Nat) (sofarFwdRW : PaInG UInt32Array) (countHyps : Nat) (thmNameToHypIdx : CTrie UInt32Array)
    {α : Sort _} (k : PaInG UInt32Array → Array ThmFormat → Array ThmFormat → PaInG UInt32Array → Nat → SetTrie ThmFormat (PaInG UInt32Array) → Array Nat → PaInG UInt32Array → Nat → CTrie UInt32Array → MetaM α)
    : MetaM α :=
    do
    mtracing
    match cinfoNs with
    | [] =>
        k sofarBack formatsCumul formatsHere sofarBackRW countThm sofarFwd hyptothm sofarFwdRW countHyps thmNameToHypIdx
    | cinfoN :: moreNs =>
      match thmNameToHypIdx.find? cinfoN.toString.toUTF8 with
      | .some .. =>
        -- *Note* this is a hack (is it?) to not rebuild and duplicate the data for the declarations
        -- of the main module, when the command to do so is run multiple times in the file
        helpBuildLocal env module moreNs sofarBack formatsCumul formatsHere sofarBackRW countThm sofarFwd hyptothm sofarFwdRW countHyps thmNameToHypIdx k
      | .none =>
        match env.find? cinfoN with
        | .none =>
          throwError s!"[helpBuildLocal] {cinfoN} is not in the current environement"
        | .some cinfo =>
            mtrace on .zero with s!"[helpBuildLocal] on decl {cinfo.name} with idx {countThm}"
            if cinfo.name.blackListCaching env
            then
              mtrace on .zero with s!"[helpBuildLocal] blacklisted !"
              helpBuildLocal env module moreNs sofarBack formatsCumul formatsHere sofarBackRW countThm sofarFwd hyptothm sofarFwdRW countHyps thmNameToHypIdx k
            else
              let .mk rwWithSinkNotInGoal data _ _ ← processForCache module countThm cinfo
              mtrace on .zero with s!"[helpBuildLocal] passed processForCache"
              match data with
              | d@(.std _ _ _ hyps mctx _ goal sinks) :: [] =>
                  mtrace on .zero with s!"[helpBuildLocal] std case"
                  mtrace on .one with s!"[helpBuildLocal] sinks {sinks}"
                  let formatsCumul := formatsCumul.push d
                  let formatsHere := formatsHere.push d
                  mctx.load -- paranoina ?
                  sofarBack.insertS goal countThm <| fun sofarBack => do
                    mtrace on .zero with s!"[helpBuildLocal] add goal to back"
                    let HforFwdPaInG := sinks.foldl (fun S s => match hyps[s]! with | .inst .. => S | .reg type => (type) :: S) []
                    HforFwdPaIn.foldlMcps (PaIn.dead, countHyps)  (fun e (T,i) q =>
                      T.insertS e i <| fun res => do
                        mtrace on .zero with s!"[helpBuildLocal] for forw, added hyp {← ppExpr e}"
                        q (res, i+1))
                        <| fun (FwdPaIn,_) => do
                          let sofarFwd := sofarFwd.easyInsert FwdPaInG d
                          let hyptothm := (hyptothm.pushN countThm) HforFwdPaIn.length
                          let ciN := cinfo.name.toString.toUTF8
                          let countThm := countThm + 1
                          let thmNameToHypIdx := thmNameToHypIdx.insert ciN (List.Ico countHyps (countHyps + HforFwdPaIn.length))
                          let countHyps := countHyps + HforFwdPaIn.length
                          helpBuildLocal env module moreNs sofarBack formatsCumul formatsHere sofarBackRW countThm sofarFwd hyptothm sofarFwdRW countHyps thmNameToHypIdx k
              | fst@(.rw _ _ _ goal replacement _ mctx _ _) :: snd :: [] => do
                  mtrace on .zero with s!"[helpBuildLocal] rw case"
                  let formatsCumul := (formatsCumul.push fst).push snd
                  let formatsHere := (formatsHere.push fst).push snd
                  mctx.load -- paranoina ?
                  mtrace on .zero with s!"[helpBuildLocal] rwWithSinkNotInGoal {rwWithSinkNotInGoal} "
                  if !rwWithSinkNotInGoal
                  then -- handle forward rws in LeanGrow.Src
                    sofarBackRW.insertS goal countThm <| fun sofarBackRW => do
                      mtrace on .zero with s!"[helpBuildLocal] added left to back"
                      sofarFwdRW.insertS goal countThm <| fun sofarFwdRW => do
                        mtrace on .zero with s!"[helpBuildLocal] added left to forw"
                        let countThm := countThm + 1
                        sofarBackRW.insertS replacement countThm <| fun sofarBackRW => do
                          mtrace on .zero with s!"[helpBuildLocal] added right to back"
                          sofarFwdRW.insertS replacement countThm <| fun sofarFwdRW => do
                            mtrace on .zero with s!"[helpBuildLocal] added rigth to forw"
                            let countThm := countThm + 1
                            helpBuildLocal env module moreNs sofarBack formatsCumul formatsHere sofarBackRW countThm sofarFwd hyptothm sofarFwdRW countHyps thmNameToHypIdx k
                  else
                    sofarBackRW.insertS goal countThm <| fun sofarBackRW => do
                      mtrace on .zero with s!"[helpBuildLocal] added left to back"
                      let countThm := countThm + 1
                      sofarBackRW.insertS replacement countThm <| fun sofarBackRW => do
                        mtrace on .zero with s!"[helpBuildLocal] added right to back"
                        let countThm := countThm + 1
                        helpBuildLocal env module moreNs sofarBack formatsCumul formatsHere sofarBackRW countThm sofarFwd hyptothm sofarFwdRW countHyps thmNameToHypIdx k
              | _ => throwError s!"[helpBuildLocal] unsupported format ?!?"


#check CTrie.difference

#print SearchConfig
#check SetTrie.easyInsert
#exit


unsafe def mkGrowExtLocal : MetaM Unit :=
  trace set Tracing.Flags.none in do
  let commandref ← getRef
  let env ← getEnv
  let module := env.mainModule
  match GrowExtImpl.getState env with
  | .none => throwError LeanGrow_ErrorMsg_loadScoreWithoutCore
  | .basic D =>
      let .some midx := env.getModuleIdx? module | throwError s!"[mkGrowExtLocal] module {module} has no index"
      let consts := (env.header.moduleData[midx]!).constants
      let mut elimrecu : CTrie (List RecursorCache) := D.cfg.elimrecus
      let ee ← getElabElims' env midx
      for n in ee do
        let (key,val) ← deriveElabElimKeyVal n
        elimrecu := elimrecu.upsert key (fun
          | .none => .some [val]
          | .some V => .some <| V.insert val -- *Note* duplicates (customelim & elabelim) may exist, such as `Nat.recAux` (in 4.18), so we avoid them
          )
      let ce ← getCustomElims' env midx
      for d in ce do
        let data ← deriveCustomElimKeyVal d
        for (key,val) in data do
          elimrecu := elimrecu.upsert key (fun
            | .none => .some [val]
            | .some V => .some <| V.insert val
            )
      let mut funrecu : CTrie FunRecursorCache := D.cfg.funrecus
      for con in consts do
        if con.isDefinition
        then
          if con.name.blackListCaching
          then
            continue
          else
            match ← deriveFunIndKeyVal' con.name with
            | .none => continue
            | .some (_,key,recu) =>
                funrecu := funrecu.insert  key recu
        else continue
      let decls := env.declsInModuleIdx midx
      helpBuildLocal
        env module decls
        D.stdBackPaInG D.thm_data #[] D.rwBackPaInG D.thm_data.size D.stdForwSetTrie D.stdForwSetTrie_idxToThmIdx D.rwForwPaInG D.stdForwSetTrie_idxToThmIdx.size D.thmNameToHypIdx
        <| fun stdBackPaInG thm_data toThmData rwBackPaInG _ stdForwSetTrie stdForwSetTrie_idxToThmIdx rwForwPaInG _ thmNameToHypIdx => do
            let thmData := D.thmData.insert module.toString.toUTF8 toThmData
            let ncfg := {D.cfg with elimrecus := elimrecu, funrecus := funrecu}
            let nenv := GrowExtImpl.setState env (.basic {D with cfg := ncfg, stdBackPaInG := stdBackPaIn, thm_data := thm_data, thmData := thmData, rwBackPaInG := rwBackPaIn, stdForwSetTrie := stdForwSetTrie, stdForwSetTrie_idxToThmIdx := stdForwSetTrie_idxToThmIdx, rwForwPaInG := rwForwPaIn, thmNameToHypIdx := thmNameToHypIdx})
            logInfoAt commandref "[mkGrowExtLocal] built and added cache data for the declaration of the main module."
            setEnv nenv



#check SetTrieP.ofList

elab "grow_load_local" : command => unsafe do
  Command.liftTermElabM mkGrowExtLocal

#check 1

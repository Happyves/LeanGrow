
/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import Batteries.Util.Pickle
import Lean.Attributes
import Lean.Elab.App
import LeanGrow.Src.Data.Amalgames

import Lean

open Lean System IO FS Process Elab Parser Meta

/-
Sections

- API
- Tests
- With environement to work on
- Unpickle safety
-  Elab info
-/



-- # API

def Lean.ScopedEnvExtension.Entry.get {α : Type} (e : ScopedEnvExtension.Entry α) : α :=
  match e with
  | .global x => x
  | .scoped _ x => x


-- # Tests

namespace ImportExport

/-- noConfusion theorems are in constants -/
def test0 : CoreM Unit := do
  let cs := (← getEnv).constants
  let has? := cs.contains `List.noConfusion
  if !has?
    then throwError "will need fixing"

#eval test0

/-- Injectivity theorems are in constants -/
def test1 : CoreM Unit := do
  let cs := (← getEnv).constants
  let has? := cs.contains `List.cons.inj
  if !has?
    then throwError "will need fixing"

#eval test1


/-- Ext theorems are among env constants, and in the
ext-extention, and require type inference to get the constant info.
Intended use can be studied in `Lean.Elab.Tactic.Ext.applyExtTheoremAt`
-/
def test2 : MetaM Unit := do
  let cs := (← getEnv).constants
  let has? := cs.contains `Prod.ext
  if !has?
    then throwError "will need fixing"
  let env ← getEnv
  let .some midx := env.getModuleIdxFor? `Prod.ext | throwError "bizare"
  let extEntries := (Lean.Meta.Ext.extExtension.ext.getModuleEntries env midx).map (fun x => x.get.declName)
  if !(extEntries.contains `Prod.ext)
    then throwError "will need fixing"
  let c ← mkConstWithFreshMVarLevels `Prod.ext
  let ct ← inferType c
  IO.println (← ppExpr ct)


#eval test2

#check Lean.Elab.Tactic.Ext.applyExtTheoremAt

/-- Instances are among constants-/
def test3 : CoreM Unit := do
  let cs := (← getEnv).constants
  let has? := cs.contains `instInhabitedNat
  if !has?
    then throwError "will need fixing"

#synth Inhabited Nat

#eval test3

/-- Recursors aren't among constants-/
def test4 : CoreM Unit := do
  let cs := (← getEnv).constants
  let has? := cs.contains `Nat.rec
  if !has?
    then throwError "will need fixing"
  let has? := cs.contains `Nat.recOn
  if !has?
    then throwError "will need fixing"

#eval test4


/-- Eq-theorems are among the constants of the environement.
The extentions only contain the names of delcaration for which eq-thms
ere generated. To get the names, use `Lean.Elab.Structural.getEqnsFor?`
and `Lean.Elab.WF.getEqnsFor?`.
-/
def test5 : MetaM Unit := do
  let cs := (← getEnv).constants
  let has? := cs.contains `Nat.add.eq_def
  if has?
    then throwError "will need fixing 1"
  let has? := cs.contains `Nat.gcd.eq_def
  if has?
    then throwError "will need fixing 2"
  let env ← getEnv
  let .some midx := env.getModuleIdxFor? `Nat.add | throwError "bizare"
  let entries := (Structural.eqnInfoExt.getModuleEntries env midx).map (fun (x,y) => s!"{x} : {y.declNames}")
  IO.println (entries)
  let .some midx := env.getModuleIdxFor? `Nat.gcd | throwError "bizare"
  let entries := (WF.eqnInfoExt.getModuleEntries env midx).map (fun (x,y) => s!"{x} : {y.declNames}")
  IO.println (entries)

#eval test5

#check Nat.add.eq_def
#check Nat.gcd.eq_def


/-- ElabAsElims are among the environement constants and
they are also among the entries of the elabelim extention
Custom eliminators are also amon env constants.-/
def test6 : MetaM Unit := do
  let cs := (← getEnv).constants
  let has? := cs.contains `Nat.strongRecOn
  if !has?
    then throwError "will need fixing 1"
  let env ← getEnv
  let .some midx := env.getModuleIdxFor? `Nat.strongRecOn | throwError "bizare"
  let entries := (TagAttribute.ext Lean.Elab.Term.elabAsElim).getModuleEntries env midx
  if !(entries.contains `Nat.strongRecOn)
    then throwError "will need fixing 1"
  let has? := cs.contains `Nat.recAux
  if !has?
    then throwError "will need fixing 2"
  let res := customEliminatorExt.getState env |>.map.find? (true, #[`Nat])
  if res != .some `Nat.recAux
    then throwError "will need fixing 2"

#eval test6

#check Nat.strongRecOn
#check Nat.recAux



/-- Functional induction isn't among constants, but they are
after running `getFunInduct?`. `match`es are among constants. -/
def test7 : CoreM Unit := do
  let cs := (← getEnv).constants
  let has? := cs.contains `Nat.add.induct
  if has?
    then throwError "will need fixing 1"
  let .some real ← getFunInduct? false false `Nat.add | throwError "will need big fixing"
  let has? := (← getEnv).constants.contains real
  if !has?
    then throwError "will need fixing 2"
  let has? := cs.contains `Nat.add.match_1
  if !has?
    then throwError "will need fixing 3"

#eval test7

#check Nat.add.induct
#check Nat.add.match_1



def bar : Fin 42 := ⟨37, by decide⟩

#print bar

#check bar._proof_1

/-- Abstracted proofs are among the env constants.
They are made in `Lean.Meta.abstractNestedProofs` and added to
the envionemt via `Lean.Meta.mkAuxTheorem` -/
def test8 : CoreM Unit := do
  let cs := (← getEnv).constants
  let has? := cs.contains `ImportExport.bar._proof_1
  if !has?
    then throwError "will need fixing"

#eval test8

#check Lean.Meta.abstractNestedProofs
#check Lean.Meta.mkAuxTheorem


#check Fin.isLt
#print StructureInfo

/-- Projection functions are in the env constants and in
a private env extention-/
def test9 : CoreM Unit := do
  let cs := (← getEnv).constants
  let has? := cs.contains `Fin.isLt
  if !has?
    then throwError "will need fixing"
  let .some res := getStructureInfo? (← getEnv) `Fin | throwError "hmm"
  IO.println s!"{res.fieldNames}"

#eval test9


end ImportExport



-- # With environement to work on


#eval do return FilePath.join (← getCurrentDir) (FilePath.toString "LeanGrow/Src/Caches")

def findLeanGrowCacheDir : IO FilePath := do
  let here ← getCurrentDir
  let res := FilePath.join here (FilePath.toString "LeanGrow/Src/Caches")
  if ← res.pathExists
  then return res
  else throw (IO.userError "[findLeanGrowCacheDir] The location of caches seems to have failed")

/-- With exts loaded-/
unsafe def WithImportModules (imports : Array Import) (opts : Options)
    (act : Environment → IO Unit) (trustLevel : UInt32 := 0) : IO Unit := do
  -- initSearchPath (← findSysroot)
  -- enableInitializersExecution
  let env ← importModules (loadExts := true) imports opts trustLevel
  try {act env ; return()} finally pure ()-- env.freeRegions --



unsafe def withImportModulesTracing
  (imports : Array Name) (opts : Options)
  (act : Environment → IO String) : IO Unit := do
  let cachePath ← findLeanGrowCacheDir
  let finalPath := FilePath.join cachePath (FilePath.toString "withImportModulesTracing.txt")
  let imports := imports.map (fun n => Import.mk n true true false)
  WithImportModules imports opts <| fun env => do
    let traces ← act env
    writeFile finalPath traces
  let res ← readFile finalPath
  IO.println res

unsafe def withImportModulesTracingPass
  {m} [Monad m] [MonadLiftT IO m]
  (imports : Array Name) (opts : Options)
  (act : Environment → IO String) : m String := do
  let cachePath ← findLeanGrowCacheDir
  let finalPath := FilePath.join cachePath (FilePath.toString "withImportModulesTracing.txt")
  let imports := imports.map (fun n => Import.mk n true true false)
  WithImportModules imports opts <| fun env => do
    let traces ← act env
    writeFile finalPath traces
  readFile finalPath

@[specialize, inline]
def Core.withResetRecDepth {α : Sort _} (k : CoreM α) : CoreM α :=
  withReader (fun ctx => { ctx with currRecDepth := 0 }) k

@[specialize, inline]
def Meta.withResetRecDepth  {α : Sort _} (k : MetaM α) : MetaM α :=
  withTheReader Core.Context (fun ctx => { ctx with currRecDepth := 0 }) k

@[specialize, inline]
def Core.withUnlimitedHeartbeats {α : Sort _} (k : CoreM α) : CoreM α :=
  withReader (fun ctx => { ctx with maxHeartbeats := 0 }) k

@[specialize, inline]
def Meta.withUnlimitedHeartbeats  {α : Sort _} (k : MetaM α) : MetaM α :=
  withTheReader Core.Context (fun ctx => { ctx with maxHeartbeats := 0 }) k

@[specialize, inline]
def stdMetaRun {α : Sort _} (env : Environment) (k : MetaM α) : IO α := do
  let cc : Core.Context := { fileName := "stdMetaRunDummy", fileMap := FileMap.ofString ""}
  let cs : Core.State := {env := env}
  let fst := MetaM.run (Meta.withUnlimitedHeartbeats k)
  let snd := Core.CoreM.toIO fst cc cs
  let ((res,_), _) ← snd
  return res

@[specialize, inline]
def stdMetaRunWithMeta
  (ctx : Meta.Context) (st : Meta.State)
  {α : Sort _} (env : Environment) (k : MetaM α) : IO α := do
  let cc : Core.Context := { fileName := "stdMetaRunDummy", fileMap := FileMap.ofString ""}
  let cs : Core.State := {env := env}
  let fst := MetaM.run (Meta.withUnlimitedHeartbeats k) ctx st
  let snd := Core.CoreM.toIO fst cc cs
  let ((res,_), _) ← snd
  return res

@[specialize, inline]
unsafe def stdImportTracePickle
  (imports : Array Name) (opts : Options) (cacheName : String)
  {α : Sort _} (act : MetaM (α × String)) : IO Unit :=
  withImportModulesTracing imports opts <| fun env => do
    let (res,traces) ← stdMetaRun env act
    let cachePath ← findLeanGrowCacheDir
    let finalPath := FilePath.join cachePath (FilePath.toString cacheName)
    pickle finalPath res
    return traces

@[specialize, inline]
unsafe def stdImportTracePicklePerImport
  (imports : Array Name) (opts : Options) (cacheName : Name → String)
  {α : Sort _} (act : Name → MetaM (α × String)) : IO Unit :=
  withImportModulesTracing imports opts <| fun env => do
    let mut totalTraces := ""
    for module in imports do
      let (res,traces) ← stdMetaRun env (act module)
      let cachePath ← findLeanGrowCacheDir
      let finalPath := FilePath.join cachePath (FilePath.toString (cacheName module))
      pickle finalPath res
      totalTraces := totalTraces ++ traces
    return totalTraces




-- # Unpickle safety


/-- *Note* It seems that unpickleing doesn't require to set imports.
In order to unpickle to a type, we must already have that type in the environement
we're running in.-/
@[specialize, inline]
unsafe def withUnpickleTracing {m} [Monad m] [MonadLiftT IO m] (α : Sort _)
  (path : FilePath) (act : α → m String) : m Unit := do
  let cachePath ← findLeanGrowCacheDir
  let finalPath := FilePath.join cachePath (FilePath.toString "withUnpickleTracing.txt")
  let (x, region) ← unpickle α path
  let traces ← act x
  writeFile finalPath traces
  region.free
  let res ← readFile finalPath
  IO.println res

@[specialize, inline]
unsafe def stdWithUnpickleTracing {m} [Monad m] [MonadLiftT IO m] (α : Sort _)
  (cacheName : String) (act : α → m String) : m Unit := do
  let cachePath ← findLeanGrowCacheDir
  let finalPath := FilePath.join cachePath (FilePath.toString "withUnpickleTracing.txt")
  let path := FilePath.join cachePath ⟨cacheName⟩
  let (x, region) ← unpickle α path
  let traces ← act x
  writeFile finalPath traces
  region.free
  let res ← readFile finalPath
  IO.println res

@[specialize, inline]
unsafe def stdWithUnpickleTracingMulti {m} [Monad m] [MonadLiftT IO m] (α : Sort _) [Inhabited α]
  (cacheNames : Array String) (act : Array α → m String) : m Unit := do
  let cachePath ← findLeanGrowCacheDir
  let finalPath := FilePath.join cachePath (FilePath.toString "withUnpickleTracing.txt")
  let mut regs : Array CompactedRegion := Array.replicate cacheNames.size (0 : USize)
  let mut i := 0
  let mut data : Array α := Array.replicate cacheNames.size default
  for cacheName in cacheNames do
    let path := FilePath.join cachePath ⟨cacheName⟩
    let (x, region) ← unpickle α path
    regs := regs.set! i region
    data := data.set! i x
    i := i+1
  let traces ← act data
  writeFile finalPath traces
  for reg in regs do
    reg.free
  let res ← readFile finalPath
  IO.println res


@[specialize, inline]
unsafe def stdWithUnpickleTracingMulti' {m} [Monad m] [MonadLiftT IO m] (α : Sort _) [Inhabited α]
  (moduleNames : Array Name) (toCacheName : Name → String) (act : ListProd Name α → m String) : m Unit := do
  let cachePath ← findLeanGrowCacheDir
  let finalPath := FilePath.join cachePath (FilePath.toString "withUnpickleTracing.txt")
  -- used to be for loop and caused overflow at Caching.Query.Test.BuildLoad ; codegen error ??
  let rec main (regs : Array CompactedRegion) (i : Nat) (data : ListProd Name α) : m ((Array CompactedRegion) × (ListProd Name α)) := do
    if i < moduleNames.size
    then
      let module := moduleNames[i]!
      let path := FilePath.join cachePath ⟨toCacheName module⟩
      let (x, region) ← unpickle α path
      let regs := regs.set! i region
      let data := .cons module x data
      let i := i+1
      main regs i data
    else
      return .mk regs data
  let .mk regs data ← main (Array.replicate moduleNames.size (0 : USize)) 0 .nil
  let traces ← act data
  writeFile finalPath traces
  let rec free (i : Nat) : IO Unit := do
    if h : i < regs.size
    then
      let _ ← regs[i].free
      free (i+1)
    else
      return ()
  let res ← readFile finalPath
  IO.println res



@[specialize, inline]
unsafe def stdWithUnpickle {m} [Monad m] [MonadLiftT IO m] (α : Sort _)
  (cacheName : String) (act : α → m Unit) : m Unit := do
  let cachePath ← findLeanGrowCacheDir
  let path := FilePath.join cachePath ⟨cacheName⟩
  let (x, region) ← unpickle α path
  let _ ← act x
  region.free
  pure ()



-- # Elab info

/--Thanks to Kim Morrissons REPL-/
unsafe def getInfoTrees (module : Name) : IO (Environment × FileMap × List InfoTree) := do
  Lean.initSearchPath (← Lean.findSysroot) -- from repl...
  enableInitializersExecution
  let path ← findLean (← searchPathRef.get) module -- ex.: `Mathlib.Combinatorics.Pigeonhole
  let raw ← readFile (FilePath.join (← IO.currentDir) path)
  -- let raw ← readFile path
  let fm := String.toFileMap raw
  let fileName   := "<input>"
  let inputCtx   := Parser.mkInputContext raw fileName
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let (env, messages) ← processHeader header {} messages inputCtx (leakEnv:= true)
  let headerOnlyState := Command.mkState env messages {}
  let commandState := {headerOnlyState with infoState.enabled := true}
  let s ← IO.processCommands inputCtx parserState commandState <&> Frontend.State.commandState
  pure (s.env, fm, s.infoState.trees.toList)

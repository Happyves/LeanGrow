
import Lean
import Lake

open Lean Elab Meta Command Tactic
open Lake


def simpleImportModules (imp : Array Name) : IO Environment :=
  Lean.importModules (imp.map (fun n => ⟨n,false⟩)) {}

#check simpleImportModules

#check importModules
#check importModulesCore
#check finalizeImport
#check_failure setImportedEntries

#check Environment.header
#check EnvironmentHeader.imports

#check writeModule
#check readModuleData
#check findOLean


#check Environment.addDeclCore

#check runFrontend


#check EnvExtension
#check registerEnvExtension

#check registerTraceClass

#check registerOption

#check Lean.addTrace

--#synth MonadTrace Option
#synth MonadTrace CoreM
#check Core.instMonadTraceCoreM


#check buildLeanO
#check buildO
#check buildImportsAndDeps
#check Module.recBuildLean


def dummyFile :=
"import Lean

#check 1+1

def myConst : Nat := 42

"

#eval IO.Process.getCurrentDir

#check System.FilePath.join

elab "buildOlean?" : command => do
  let (elabed,pass?) ← runFrontend dummyFile {} "dumdum1" `dumdum2
  dbg_trace "test1"
  if pass? then
    let rootish ← IO.Process.getCurrentDir
    let hmm := "LeanGrow/F/EnvironmentManagement/Imports"
    let next := rootish.join ⟨hmm⟩
    if ← next.pathExists
    then
      let name := "dumdum3.olean"
      let final := next.join ⟨name⟩
      writeModule elabed final
      dbg_trace "test2"
      IO.FS.writeFile (next.join ⟨"hmmm.txt"⟩) "seems to work"
    else
      IO.println "Error a file path build"
  else
    IO.println "Elaboration raised errors"



-- buildOlean?
-- works ; prints the check message ; VScode is to blame for not dsiplaying the olean ...

-- privat in lean environment
private def equivInfo (cinfo₁ cinfo₂ : ConstantInfo) : Bool := Id.run do
  let .thmInfo tval₁ := cinfo₁ | false
  let .thmInfo tval₂ := cinfo₂ | false
  return tval₁.name == tval₂.name
    && tval₁.type == tval₂.type
    && tval₁.levelParams == tval₂.levelParams
    && tval₁.all == tval₂.all



-- no idea if this works ; our caches will only contains defs and theorems anyway ??
def Lean.ConstantInfo.toDeclaration : ConstantInfo → Option Declaration
  | .defnInfo v => .some (.defnDecl v)
  --| .axiomInfo v => .some (.axiomDecl v)
  | .thmInfo v => .some (.thmDecl v)
  --| .opaqueInfo v => .some (.opaqueDecl v)
  --| quotDecl -- ??
  --| mutualDefnDecl  (defns : List DefinitionVal) -- All definitions must be marked as `unsafe` or `partial` -- not needed ??
  --| induct => .inductDecl (lparams : List Name) (nparams : Nat) (types : List InductiveType) (isUnsafe : Bool)
  | _ => .none

--#exit

elab "readOlean?" : command => do
  let rootish ← IO.Process.getCurrentDir
  let hmm := "LeanGrow/F/EnvironmentManagement/Imports"
  let next := rootish.join ⟨hmm⟩
  let name := "dumdum3.olean"
  let final := next.join ⟨name⟩
  if ← final.pathExists
    then
    let (data,_) ← readModuleData final
    let env ← getEnv
    let modIdx := env.header.imports.size + 1
    -- ↑ I assume the module indices of constants correspond to te index in the imports?
    -- adapted from finalizeImport
    -- Actually, we can't, because the Environment construcot is private
    -- let mut const2ModIdx : HashMap Name ModuleIdx := env.const2ModIdx
    -- let mut constantMap : HashMap Name ConstantInfo := env.constants.map₁ -- I assume this is the right projection ?
    -- for cname in data.constNames, cinfo in data.constants do
    --   match constantMap.insertIfNew cname cinfo with
    --   | (constantMap', cinfoPrev?) =>
    --     constantMap := constantMap'
    --     if let some cinfoPrev := cinfoPrev? then
    --       unless equivInfo cinfoPrev cinfo do
    --         throwError "Constant name mismatch"
    --   const2ModIdx := const2ModIdx.insert cname modIdx
    -- for cname in data.extraConstNames do
    --   const2ModIdx := const2ModIdx.insert cname modIdx
    -- let nenv : Environment := { env with
    --     const2ModIdx    := const2ModIdx
    --     constants       := constants
    --     extraConstNames := {}
    --     extensions      := exts
    --     header          := {
    --       quotInit     := !imports.isEmpty -- We assume `core.lean` initializes quotient module
    --       trustLevel   := trustLevel
    --       imports      := imports
    --       regions      := s.regions
    --       moduleNames  := s.moduleNames
    --       moduleData   := s.moduleData
    --     }
    --   }
    let env2 := data.constants.foldl (fun e i =>
      match i.toDeclaration with
      | .some I =>
        match e.addDeclWithoutChecking I with
        | .ok E => E
        | _ => e
      | _ => e) env
    setEnv env2 -- conside note below


#check_failure Environment.mk --is private :<
-- potential hack might be to add a fake import and modify the environement via
#check finalizeImport

readOlean?

#check myConst
--#eval myConst --fail
#reduce myConst


#eval (do let res := (← getEnv).header.imports.map Import.module ; IO.println res : CoreM Unit)
-- Indeed, when we set the environement to the new one
-- we didin't add imports !!!

--#exit

#check Environment.extensions
#check EnvExtensionState

#check ConstantInfo.rec

elab "studyExtraNames" n:name : command => do
  let mFile ← findOLean n.getName
  let (data,_) ← readModuleData mFile
  IO.println data.extraConstNames

studyExtraNames `Mathlib.Data.Nat.Defs

studyExtraNames `Init.Prelude

#check_failure Nat.decLt._boxed
-- in Init, so module is imported

#check persistentEnvExtensionsRef.get
#check PersistentEnvExtension.name


#eval (do let res ← persistentEnvExtensionsRef.get ; IO.println (res.map PersistentEnvExtension.name) : IO Unit)

#check addDecl

#check Environment.addDecl


elab "com" : command => do
  let exts ← persistentEnvExtensionsRef.get
  let names := String.intercalate "\n"
    (exts.map (fun x => (PersistentEnvExtension.name x).toString)).toList
  let loc := "/home/yves/Desktop/CodeWorkspace/Lean4_General/LeanGrow/LeanGrow/F/EnvironmentManagement/Imports/testin.txt"
  IO.FS.writeFile ⟨loc⟩ names

--com

elab "com2" : command => do
  let env ← getEnv
  let exts ← persistentEnvExtensionsRef.get
  let names := String.intercalate "\n"
    (exts.map (fun x => (PersistentEnvExtension.name x).toString)).toList
  let dec := Declaration.defnDecl (mkDefinitionValEx `LG.extract [] (.const `String []) (Expr.lit (Literal.strVal names)) .opaque .safe [])
  let nenv := env.addDecl {} dec
  match nenv with
  | .ok yes => setEnv yes
  | _ => pure ()

#check Expr.lit
#check Literal.strVal
#check mkDefinitionValEx
#check String.intercalate

def fakeInstructions :=
"
import Lean

open Lean

elab \"com\" : command => do
  let exts ← persistentEnvExtensionsRef.get
  let names := String.intercalate \"\\n\"
    (exts.map (fun x => (PersistentEnvExtension.name x).toString)).toList
  let loc := \"/home/yves/Desktop/CodeWorkspace/Lean4_General/LeanGrow/LeanGrow/F/EnvironmentManagement/Imports/testin.txt\"
  IO.FS.writeFile ⟨loc⟩ names

com
"




elab "studyPersEnvExt" n:name : command => do
  let fakeFile := "import " ++ n.getName.toString ++ fakeInstructions
  let (_,_) ← runFrontend fakeFile {} "nope" `nope

-- studyPersEnvExt `Mathlib.Data.Nat.Defs
-- studyPersEnvExt `Init.Prelude
-- work, and carry out IO, but strangely also adds the Lake stuff, which doesn't happen
-- if we remove the lake import in this file, so it seems that environements aren't loaded
-- the way I imagined them ?


#check expandInitialize


#check importModules
#check importModulesCore
#check finalizeImport

#check 1

/-
The way imports seem to work is by starting wih a list of `Import`s, which are just names.
`importModules` is just the top function: it sets flags, and calls `importModulesCore` and `finalizeImport`.
`importModulesCore` adds the name of the import to the list of import names, uses `findOLean` to find the
corresponding olean filepath, uses `readModuleData` to get the module data, and first makes a recursive call
on the imports of that imported module. When the call returns, the module data of the current module is
pushed onto stack of the ImportState.
`finalizeImport` will turn these stacks of data into an `Environment`. Most notably, it builds the constant
hashmaps by folding over the module datas, checking if names clash.

-/



inductive Tree where
| leaf (_ : Name)  | node (_ : Name) (kist : Array Tree)
deriving Inhabited, Repr, BEq

/-
Compare with:
- mathlib > shake > main
- importGraphs > ImportGraphs > Import
-/

-- hopefully no cycles
partial def goImp (i : Import) : IO Tree := do
  let mFile ← findOLean i.module
  let (data,_) ← readModuleData mFile
  let is := data.imports
  if is.isEmpty
  then
    return .leaf i.module
  else
    let Ts ← is.mapM goImp
    return .node i.module Ts


elab "getImportTree" n:name : command => do
  let mFile ← findOLean n.getName
  let (data,_) ← readModuleData mFile
  let is := data.imports
  let Ts ← (is.mapM goImp : IO _)
  let res := Tree.node n.getName Ts
  IO.println (repr res)


-- getImportTree `Mathlib.Data.Nat.Defs
-- caused massive freeze ...

-- adapted from importGraph

def MyImportsOf (env : Environment) (n : Name) : Array Name :=
  if n = env.header.mainModule then
    env.header.imports.map Import.module
  else match env.getModuleIdx? n with
    | .some idx => env.header.moduleData[idx.toNat]!.imports.map Import.module |>.erase `Init
    | .none => #[]

partial def importGraph (env : Environment) : Tree :=
  let main := env.header.mainModule
  let imports := env.header.imports.map Import.module
  let reses := imports.map (process env)
  .node main reses
  -- imports.foldl (fun m i => process env i m) (({} : NameMap _).insert main imports)
  --   |>.erase Name.anonymous
where
  process (env) (i) : Tree :=
    let imports := MyImportsOf env i
    if imports.isEmpty
    then
      .leaf i
    else
      let reses := imports.map (process env)
      .node i reses
      --imports.foldr (fun i m => process env i m) (m.insert i imports)

elab "getImportTree2" n:name : command => do
  let mFile ← findOLean n.getName
  let (data,_) ← readModuleData mFile
  IO.println (repr res)

-- getImportTree2 `Mathlib.Data.Nat.Defs

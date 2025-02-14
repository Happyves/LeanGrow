
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
    setEnv env2


#check_failure Environment.mk --is private :<


readOlean?

#check myConst
--#eval myConst --fail
#reduce myConst

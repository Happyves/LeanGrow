
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


import Lean

open Lean Elab Meta Command Tactic


def simpleImportModules (imp : Array Name) : IO Environment :=
  Lean.importModules (imp.map (fun n => ⟨n,false⟩)) {}

#check simpleImportModules

#check importModules

#check elabImport

#check findOLean

#check runFrontend

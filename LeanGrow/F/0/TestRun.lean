import Lean
import Batteries.Lean.IO.Process
import Batteries.Lean.System.IO

open Lean

def main : IO Unit := do
  IO.println "Hey"

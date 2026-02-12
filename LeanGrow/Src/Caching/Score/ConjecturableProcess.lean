
/-
Copyright (c) 2026 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import Lean.Meta.Basic
import LeanGrow.Src.Utils.Lean.Expr.Basic
import LeanGrow.Src.Utils.Lean.Blacklisting
import LeanGrow.Src.Utils.Lean.ImportExport
import LeanGrow.Src.Utils.Std.Name
import LeanGrow.Src.Data.CTrie.Operations


open Lean Meta


partial def getConjecturablePos (type : Expr) : MetaM (List Nat) := do
  let rec process (i : Nat) (hyps : Array Expr) (insts : List Nat) (T : Expr) : MetaM (Prod3 Expr (Array Expr) (List Nat)) := do
    match T with
    | .forallE _ t b bi =>
      let t ← withTransparency .reducible <| reduce (skipTypes := false) t
      let t := t.cleanupAnnotations
      let mv ← mkMvarStdNoCoE (.num `dummy i) t
      let b := Expr.instantiate1 b mv
      match bi with
      | .instImplicit =>
        process (i+1) hyps (i :: insts) b
      | _ =>
        process (i+1) (hyps.push t) insts b
    | .letE _ _ v b _ =>
      process i hyps insts (Expr.instantiate1 b v)
    | _ => return .mk T hyps insts
  let .mk goal hyps insts ← process 0 #[] [] type
  let gdeps := goal.onAllSubtermsFold insts (fun e l =>
    match e with
    | .mvar (.mk (.num _ pos)) => l.insert pos
    | _ => l
    )
  let mut res := []
  let mut i := 0
  for T in hyps do
    if gdeps.contains i
    then
      i := i+1
    else
      if !(← isProp T)
      then
        let tdeps := T.onAllSubtermsFold [] (fun e l =>
          match e with
          | .mvar (.mk (.num _ pos)) => l.insert pos
          | _ => l
          )
        res := i :: (res.filter (fun x => !(tdeps.contains x)))
      i := i+1
  return res.mergeSort (· ≤ ·) -- important that sorted !


#check 1

def LeanGrow.mkConjTreeName (module : Name) := "LeanGrow_ConjTree_" ++ module.toUnderscoreString


#check 1



open System
unsafe def buildConjPosTree (modules : Array Name) : IO Unit :=
  WithImportModules (modules.map (fun x => {module := x})) {} <| fun env => do
    stdMetaRun env do
      mtracing
      for module in modules do
        let .some midx := env.getModuleIdx? module | panic s!"[buildCachData] unknonw module {module}"
        let cinfos := (env.header.moduleData[midx]!).constants
        let mut res : CTrie (List Nat) := .leaf
        for cinfo in cinfos do
          match cinfo with
          | .thmInfo .. | .axiomInfo .. =>
            if cinfo.name.blackListCaching env
            then
              mtrace on .zero with s!" blacklisted !"
              continue
            else
              let here ← getConjecturablePos cinfo.type
              match here with
              | [] => continue
              | _ =>
                res := res.insert cinfo.name.toString.toUTF8 here
          | .ctorInfo .. =>
            if cinfo.name.blackListCaching (← getEnv)
            then
              mtrace on .zero with s!" blacklisted !"
              continue
            else
              if ← isProp cinfo.type
              then
                let here ← getConjecturablePos cinfo.type
                match here with
                | [] => continue
                | _ =>
                  res := res.insert cinfo.name.toString.toUTF8 here
              else
                mtrace on .zero with s!" non prop ctor !"
                continue
          | _ =>
            mtrace on .zero with s!" skip !"
            continue
        let cachePath ← findLeanGrowCacheDir
        let finalPath := FilePath.join cachePath (FilePath.toString (LeanGrow.mkConjTreeName module))
        pickle finalPath res


#check 1

unsafe def loadConjPosTree_forTest (moduleName : Name) : MetaM Unit := do
    stdWithUnpickleTracingMulti' (CTrie (List Nat)) #[moduleName] LeanGrow.mkConjTreeName
      <| fun data => do
        match data with
        | .nil => return "fail"
        | .cons _ data _ =>
          return s!"{data.toList}"


#check 1
#check readModuleData
#print ModuleData
#check findOLean


unsafe def buildConjPosTree_forEnvImportsofModule (mod : Name) : IO Unit :=
  WithImportModules (#[mod].map (fun x => {module := x})) {} <| fun env => do
    stdMetaRun env do
      mtracing
      let env ← getEnv
      let modpath ← findOLean mod
      let (data, _) ← readModuleData modpath
      let modules := data.imports
      for module in modules do
        let .some midx := env.getModuleIdx? module.module | panic s!"[buildCachData] unknonw module {module}"
        let cinfos := (env.header.moduleData[midx]!).constants
        let mut res : CTrie (List Nat) := .leaf
        for cinfo in cinfos do
          match cinfo with
          | .thmInfo .. | .axiomInfo .. =>
            if cinfo.name.blackListCaching env
            then
              mtrace on .zero with s!" blacklisted !"
              continue
            else
              let here ← getConjecturablePos cinfo.type
              match here with
              | [] => continue
              | _ =>
                res := res.insert cinfo.name.toString.toUTF8 here
          | .ctorInfo .. =>
            if cinfo.name.blackListCaching (← getEnv)
            then
              mtrace on .zero with s!" blacklisted !"
              continue
            else
              if ← isProp cinfo.type
              then
                let here ← getConjecturablePos cinfo.type
                match here with
                | [] => continue
                | _ =>
                  res := res.insert cinfo.name.toString.toUTF8 here
              else
                mtrace on .zero with s!" non prop ctor !"
                continue
          | _ =>
            mtrace on .zero with s!" skip !"
            continue
        let cachePath ← findLeanGrowCacheDir
        let finalPath := FilePath.join cachePath (FilePath.toString (LeanGrow.mkConjTreeName module.module))
        pickle finalPath res

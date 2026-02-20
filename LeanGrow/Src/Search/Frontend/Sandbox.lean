
/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import LeanGrow.Src.Search.Frontend.Frontend
import LeanGrow.Src.Caching.Query.Sandbox


open Lean Meta System IO FS Process Elab

def sandboxConfig : SearchConfig UInt32Array where
  sandboxMode := true
  revCountMax := 3
  sinkRevCutOff := 10
  addBatchSize := 8
  splitBatches := true
  backBatchSize := 4
  forwBatchSize := 4
  induBatchSize := 2
  regulariser_fH := (fun x y => stdRegulariser2 x 64 y)
  regulariser_bH := (fun x y => stdRegulariser2 x 64 y)
  regulariser_fD := (fun x y => stdRegulariser1 x 6 64 y)
  regulariser_bD := (fun x y => stdRegulariser1 x 6 64 y)
  baseLocalThmScore := 30
  sandboxModThmScore := 10
  cachelessThmScore := 15
  regularBack := CTrie.empty
  regularForw := CTrie.empty
  funrecus := CTrie.empty
  elimrecus := CTrie.empty
  subpat := CTrie.empty
  conj := .empty
  default_relevance_timer := 3
  stdForwPeriod := 3
  tacticSupport := false
  tacticSupportData := ⟨5,5⟩
  customRegulariser_back := (fun s time data st => regBackBreadth 5 s time data st)
  customRegulariser_forw := (fun s _ _ _ => s)
  customRegulariser_indu := (fun s _ _ _ => s)




unsafe def mkGrowExtSandbox
  (sandboxStd : Array Name) (sandboxElims : Array Name) (sandboxFunInds : Array Name) : MetaM Unit := do
  let commandref ← getRef
  let env ← getEnv
  -- Adding functional induction and eliminators
  let mut funrecu : CTrie FunRecursorCache := CTrie.empty
  let mut elimrecu : CTrie (List RecursorCache) := CTrie.empty
  for n in sandboxElims do
    let (key,val) ← deriveElabElimKeyVal n
    elimrecu := elimrecu.upsert key (fun
      | .none => .some [val]
      | .some V => .some <| V.insert val -- *Note* duplicates (customelim & elabelim) may exist, such as `Nat.recAux` (in 4.18), so we avoid them
      )
  for con in sandboxFunInds do
    match ← deriveFunIndKeyVal' con with
    | .none => continue
    | .some (_,key,recu) =>
        funrecu := funrecu.insert key recu
  -- Adding standard theorems
  inSandboxS sandboxStd <| fun _ data => do
    let mergeData ← ModuleCacheState.mergeMainS (.cons `Sandbox data .nil)
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
    logInfoAt commandref "Done"
    let cfg := {sandboxConfig with funrecus := funrecu, elimrecus := elimrecu}
    let D : GrowExtCore := ⟨cfg, #[], #[], thm_data, thmData, stdBackPaIn, stdForwSetTrie, stdForwSetTrie_idxToThmIdx, stdForwSetTrie_idxToSinkIdx, rwBackPaIn, rwForwPaIn,thmNameToIdx,thmNameToHypIdx , #[], #[]⟩
    let nenv := GrowExtImpl.setState env (.basic D)
    setEnv nenv


#check SearchConfig

elab "grow_load_sandbox" std:term ";" eli:term ";" funi:term : command => unsafe do
  Command.liftTermElabM do
    let sandboxStd ← Term.evalTerm (Array Name) (.app (.const `Array [0]) (.const `Lean.Name [])) std
    let sandboxElims ← Term.evalTerm (Array Name) (.app (.const `Array [0]) (.const `Lean.Name [])) eli
    let sandboxFunInds ← Term.evalTerm (Array Name) (.app (.const `Array [0]) (.const `Lean.Name []))  funi
    mkGrowExtSandbox sandboxStd sandboxElims sandboxFunInds

#check 2

elab "grows" : tactic => do
  let msgRef ← getRef
  let data := GrowExtImpl.getState (← getEnv)
  match data with
  | .none => throwError "[Grow] seems no sandbox was loaded"
  | .basic D =>
      growImpl msgRef 16 D.cfg D.thm_data D.thmData D.stdBackPaInG D.stdForwSetTrie D.stdForwSetTrie_idxToThmIdx D.rwBackPaInG D.rwForwPaInG D.thmNameToHypIdx D.stdForwSetTrie_idxToSinkIdx D.thmNameToThmIdx

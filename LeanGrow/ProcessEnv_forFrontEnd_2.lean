
import LeanGrow.NameListCompare
import LeanGrow.DAGembed
import LeanGrow.ProcessDecl
import LeanGrow.Blacklisting
import Mathlib

open Lean Data


structure pdata where
  cst_name : Name
  dag : SizedDAG CExpr Nat
  sink_cst_names : Trie Unit
deriving Inhabited

def pdata.toString : pdata → String :=
  --dbg_trace "comp pdata"
  fun ⟨n,d,st⟩ => s!"⟨`{n},{SizedDAG.toString CExpr.toGoodString d},{print_trie st}⟩"


--#exit

elab "cache_data" n:name : command =>
  match (Lean.Syntax.isNameLit? n.raw) with
  | none => throwError s!"Error : please enter the correct name of a module to search theorems in."
  | some N => do
        let env ← getEnv
        let modules := env.header.moduleNames.map (N.isPrefixOf ·)
        env.constants.map₁.forM (fun decName decInfo => do
            let na ← Loogle.isBlackListed decName
            if modules[env.const2ModIdx[decName].get! (α := Nat)]! && (! na)
            then match decInfo with
                  | .thmInfo v | .defnInfo v | .axiomInfo v | .ctorInfo v | .quotInfo v | .recInfo v => do
                      --dbg_trace s!"Looking at {v.name}"
                      let hyps := naiveGetHyps v.type
                      let thm_dag := SizeDAG.sinks_fst (orderHyps_wBvar hyps)
                      let sink_names := (((DAG.find_sinks thm_dag).map DAGnode.data).map CExpr.getConstNames).join.map Name.toString
                      let psn := SortedTrieFormList' sink_names
                      let maindata : pdata := ⟨decName, thm_dag, psn⟩
                      let source := Parser.runParserCategory env `term (pdata.toString  maindata) s!"ficticiousFile {decName}"
                      --dbg_trace (pdata.toString  maindata)
                      match source with
                      | .error e => throwError s!"Syntax error durring process at cache_data: {e}"
                      | .ok stx => do
                          let res ← Lean.Elab.Command.liftTermElabM  (Lean.Elab.Term.elabTermAndSynthesize stx (.some (.const `pdata [])))
                          let my_decl := Declaration.defnDecl
                            {name := Name.append `PDATA decName
                             levelParams := []
                             type := .const `pdata []
                             value := res
                             hints := .regular 0
                             safety := .safe
                            }
                          let _ ← Lean.Elab.Command.liftTermElabM  (addDecl my_decl)
                  | _ => pure ()
              else return ())
        let new_env ← getEnv
        writeModule new_env ⟨"/./home/yves/Desktop/CodeWorkspace/Lean4_General/LeanGrow/LeanGrow/Caches/mark2cache"⟩


--run_cmd cache_data `Mathlib.Data.List.Basic

#check ( ⟨`List.map₂Left.eq_1,⟨5,⟨4,CExpr.app (CExpr.const `List [Level.param `u_2]) (CExpr.node 1 (OriginalData.ofBvar 2)),[1]⟩ :: ⟨3,CExpr.forallE `a._hyg.324 (CExpr.node 0 (OriginalData.ofBvar 2)) (CExpr.forallE `a (CExpr.app (CExpr.const `Option [Level.param `u_2]) (CExpr.node 1 (OriginalData.ofBvar 2))) (CExpr.node 2 (OriginalData.ofBvar 2)) Lean.BinderInfo.default) Lean.BinderInfo.default,[0, 1, 2]⟩ :: ⟨2,CExpr.sort (Lean.Level.succ (Lean.Level.param `u_3)) ,[]⟩ :: ⟨1,CExpr.sort (Lean.Level.succ (Lean.Level.param `u_2)) ,[]⟩ :: ⟨0,CExpr.sort (Lean.Level.succ (Lean.Level.param `u_1)) ,[]⟩ :: []⟩,Lean.Data.Trie.node (none) ⟨#[76,79]⟩ #[Lean.Data.Trie.node1 (none) 105 (Lean.Data.Trie.node1 (none) 115 (Lean.Data.Trie.node1 (none) 116 (Lean.Data.Trie.leaf ((some ()))))),Lean.Data.Trie.node1 (none) 112 (Lean.Data.Trie.node1 (none) 116 (Lean.Data.Trie.node1 (none) 105 (Lean.Data.Trie.node1 (none) 111 (Lean.Data.Trie.node1 (none) 110 (Lean.Data.Trie.leaf ((some ())))))))]⟩
  : pdata)

#check Name

def mo_playin : CoreM Unit := do
  let (md, _) ← readModuleData ⟨"/./home/yves/Desktop/CodeWorkspace/Lean4_General/LeanGrow/LeanGrow/Caches/mark2cache"⟩
  for info in md.constants do
    if info.name = `PDATA.List.takeI_length then IO.print info.value!

#eval mo_playin


import LeanGrow.NameListCompare
import LeanGrow.DAGembed
import LeanGrow.ProcessDecl
import LeanGrow.Blacklisting
import Mathlib

open Lean Data


structure pdata where
  cst_info : ConstantInfo
  dag : SizedDAG CExpr Nat
  sink_cst_names : Trie Unit


elab "cache_data" n:name : tactic =>
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
                      dbg_trace s!"Looking at {v.name}"
                      let hyps := naiveGetHyps v.type
                      let thm_dag := SizeDAG.sinks_fst (orderHyps_wBvar hyps)
                      let sink_names := (((DAG.find_sinks thm_dag).map DAGnode.data).map CExpr.getConstNames).join.map Name.toString
                      let psn := SortedTrieFormList' sink_names
                      let maindata : pdata := ⟨decInfo, thm_dag, psn⟩
                      -- Parser.runParserCategory env `term raw
                      --let res ← Lean.Elab.Term.elabTermAndSynthesize
                      let my_decl := Declaration.defnDecl
                        {name := Name.append `PDATA decName
                         levelParams := []
                         type := .const `pdata []
                         value := -- fuck
                         hints := .regular 0
                         safety := .safe
                        }
                      let _ ← addDecl my_decl
                  | _ => pure ()
              else return ())

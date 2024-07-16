
import LeanGrow.NameListCompare
import LeanGrow.DAGembed
import LeanGrow.ProcessDecl
import LeanGrow.Blacklisting
import Mathlib

open Lean Data


structure pdata where
  cst_name : Name
  cst_level_params : List Name
  dag : SizedDAG CExpr Nat
  sink_cst_names : Trie Unit
deriving Inhabited

def pdata.toString : pdata → String :=
  --dbg_trace "comp pdata"
  fun ⟨n,l,d,st⟩ => s!"⟨`{n},[{String.intercalate "," (l.map (fun x => s!"`{x}"))}],{SizedDAG.toString CExpr.toGoodString d},{print_trie st}⟩"


--#exit

elab "cachData" n:name : command =>
  match (Lean.Syntax.isNameLit? n.raw) with
  | none => throwError s!"Error : please enter the correct name of a module to search theorems in."
  | some N => do
        let env ← getEnv
        let modules := env.header.moduleNames.map (N.isPrefixOf ·)
        let res ← env.constants.map₁.foldM (fun hmm decName decInfo => do
                    let na ← Loogle.isBlackListed decName
                    if modules[env.const2ModIdx[decName].get! (α := Nat)]! && (! na)
                    then match decInfo with
                          | .thmInfo v | .defnInfo v | .axiomInfo v | .ctorInfo v | .quotInfo v | .recInfo v => do
                              --dbg_trace s!"Looking at {v.name}"
                              let hyps := naiveGetHyps v.type
                              let thm_dag := SizeDAG.sinks_fst (orderHyps_wBvar hyps)
                              let sink_names := (((DAG.find_sinks thm_dag false).map DAGnode.data).map CExpr.getConstNames).join.map Name.toString
                              let psn := SortedTrieFormList' sink_names
                              let maindata : pdata := ⟨decName, decInfo.levelParams, thm_dag, psn⟩
                              let package := "def PDATA." ++  decName.toString ++ " : pdata := " ++ (pdata.toString  maindata) ++ "\n"
                              return ((package) :: hmm.1, ("PDATA." ++  decName.toString) :: hmm.2)

                              -- let source := Parser.runParserCategory env `term (pdata.toString  maindata) s!"ficticiousFile {decName}"
                              -- --dbg_trace (pdata.toString  maindata)
                              -- match source with
                              -- | .error e => throwError s!"Syntax error durring process at cache_data: {e}"
                              -- | .ok stx => do
                              --     let res ← Lean.Elab.Command.liftTermElabM  (Lean.Elab.Term.elabTermAndSynthesize stx (.some (.const `pdata [])))
                              --     let my_decl := Declaration.defnDecl
                              --       {name := Name.append `PDATA decName
                              --        levelParams := []
                              --        type := .const `pdata []
                              --        value := res
                              --        hints := .regular 0
                              --        safety := .safe
                              --       }
                              --     let _ ← Lean.Elab.Command.liftTermElabM  (addDecl my_decl)
                          | _ => return hmm
                      else return hmm) (["import LeanGrow.ProcessEnv_forFrontEnd_2\n"], [])
        -- let new_env ← getEnv
        -- writeModule new_env ⟨"/./home/yves/Desktop/CodeWorkspace/Lean4_General/LeanGrow/LeanGrow/Caches/mark2cache"⟩
        let source := String.join res.1.reverse
        let l := "def cluster_list : List pdata := [" ++ (String.intercalate ", " res.2.reverse) ++ "]"
        IO.FS.writeFile ⟨"/./home/yves/Desktop/CodeWorkspace/Lean4_General/LeanGrow/LeanGrow/Caches/mark2cache_v2.lean"⟩ (source ++ l)
        return ()


--cachData `Mathlib.Data.List.Basic



#exit

elab "test" n:name : command =>
  match (Lean.Syntax.isNameLit? n.raw) with
  | none => throwError s!"Error : please enter the correct name of a module to search theorems in."
  | some N => do logInfo "hey"

#check 1

test `lol

--def PDATA.List.nthLe_tail

#print List.nthLe_tail

#check outParam

#exit


#check Name

def mo_playin : CoreM Unit := do
  let (md, _) ← readModuleData ⟨"/./home/yves/Desktop/CodeWorkspace/Lean4_General/LeanGrow/LeanGrow/Caches/mark2cache"⟩
  for info in md.constants do
    if info.name = `PDATA.List.takeI_length then IO.print info.value!

#eval mo_playin
-- uses sorryAx ...

open Lean Meta Elab Term

#check mkConst

#check mkListLit

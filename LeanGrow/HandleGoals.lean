
import LeanGrow.CExpr
import LeanGrow.NameListCompare
import LeanGrow.Blacklisting


open Lean Data

#check Expr.getForallBody

def process_goal (depth : Nat) : Expr → CExpr
| .app (.app (.const `optParam _) e) _ => process_goal depth e
| .app (.app (.const `outParam _) e) _ => process_goal depth e
| .bvar i => if i ≥ depth then .node (i - depth) (.ofBvar i) else .bvar i
| .app l r => .app (process_goal depth l) (process_goal depth r)
| .lam n l r B => .lam n (process_goal depth l) (process_goal (depth+1) r) B -- shouldn't occur ?
| .forallE n l r B => .forallE n (process_goal depth l) (process_goal (depth+1) r) B -- shouldn't occur ?
| .mdata _ e => process_goal depth e
| .proj n i e => .proj n i (process_goal depth e)
| x => x.toCExpr



structure gdata where
  cst_name : Name
  cst_level_params : List Name
  exp : CExpr
  name_list : Trie Unit
deriving Inhabited

def gdata.toString : gdata → String :=
  --dbg_trace "comp gdata"
  fun ⟨n,l,d,st⟩ => s!"⟨`{n},[{String.intercalate "," (l.map (fun x => s!"`{x}"))}],{CExpr.toGoodString d},{print_trie st}⟩"


--#exit

elab "cachDataGoal" n:name : command =>
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
                              let goal := process_goal 0 (Expr.getForallBody v.type)
                              let names := goal.getConstNames.map Name.toString
                              let psn := SortedTrieFormList' names
                              let maindata : gdata := ⟨decName, decInfo.levelParams, goal, psn⟩
                              let package := "def GDATA." ++  decName.toString ++ " : gdata := " ++ (gdata.toString  maindata) ++ "\n"
                              return ((package) :: hmm.1, ("GDATA." ++  decName.toString) :: hmm.2)

                              -- let source := Parser.runParserCategory env `term (gdata.toString  maindata) s!"ficticiousFile {decName}"
                              -- --dbg_trace (gdata.toString  maindata)
                              -- match source with
                              -- | .error e => throwError s!"Syntax error durring process at cache_data: {e}"
                              -- | .ok stx => do
                              --     let res ← Lean.Elab.Command.liftTermElabM  (Lean.Elab.Term.elabTermAndSynthesize stx (.some (.const `gdata [])))
                              --     let my_decl := Declaration.defnDecl
                              --       {name := Name.append `gdata decName
                              --        levelParams := []
                              --        type := .const `gdata []
                              --        value := res
                              --        hints := .regular 0
                              --        safety := .safe
                              --       }
                              --     let _ ← Lean.Elab.Command.liftTermElabM  (addDecl my_decl)
                          | _ => return hmm
                      else return hmm) (["import LeanGrow.HandleGoals\n"], [])
        -- let new_env ← getEnv
        -- writeModule new_env ⟨"/./home/yves/Desktop/CodeWorkspace/Lean4_General/LeanGrow/LeanGrow/Caches/mark2cache"⟩
        let source := String.join res.1.reverse
        let l := "def goal_cluster_list : List gdata := [" ++ (String.intercalate ", " res.2.reverse) ++ "]"
        IO.FS.writeFile ⟨"/./home/yves/Desktop/CodeWorkspace/Lean4_General/LeanGrow/LeanGrow/Caches/mark1goalCache.lean"⟩ (source ++ l)
        return ()


--cachDataGoal `Mathlib.Data.List.Basic

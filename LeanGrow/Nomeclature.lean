
import Mathlib

open Lean Elab Data


def Name.getStringList : Name → List String
| .anonymous => []
| .str p s => s :: (Name.getStringList p)
| .num p _ => Name.getStringList p




def thm_parse' (cache : List Char) : List Char → List String
| [] => [String.mk cache]
| c :: next =>
    if c.isUpper
    then if (String.mk cache ≠ "")
         then (String.mk cache) :: (thm_parse' [c.toLower] next)
         else (thm_parse' [c.toLower] next)
    else if c = '_' || c = ' '
         then (String.mk cache) :: (thm_parse' [] next)
         else thm_parse' (c :: cache) next

def String.reverse (s : String) := String.mk (s.data.reverse)

def thm_parse (s : String ) : List String := (thm_parse' [] s.data).map String.reverse

#eval thm_parse "add_oddEven_le"

#eval Name.getStringList `List.countP_le_length
#eval (Name.getStringList `List.countP_le_length).map thm_parse

--#exit

-- rememeber to get names lowerd first, but not for output
#check String.toLower

#check Trie

#check Lean.RBMap

#check RBMap.ofList

/-- Inputs in lower cases only !!!-/
def what_I_meant := [["not", "ne", "neg", "neq"],["sub","tsub"],["eq","congr"], ["join", "concat"]]

def build_my_trie : List (List String) →  Trie (List String)
| [] => .leaf .none
| l :: L =>
    Id.run do
      let mut t := build_my_trie L
      for s in l do
        t := Trie.upsert t s (fun _ => l)
      return t

def what_I_meant_compiled := build_my_trie what_I_meant

def merge (inp : List String) (ref : Trie (List String)) : List String :=
  List.join ((inp.map ((fun x => match Trie.find? ref x with | .some l => l | .none => [x]))))

#eval merge ["neq", "tsub", "Nat"] what_I_meant_compiled



--#exit

elab "nomenclature" e:num n:num h:name "with" s:ident+ : command => do
  let akward : Syntax → Command.CommandElabM String :=
    fun x : Syntax => match x with
                      | Syntax.ident _ rawVal _ _   => return rawVal.toString
                      | _ => throwError "Something went wrong when elaborating the keywords"
  let S ← s.mapM (akward ∘ TSyntax.raw)
  let Sm := if e.getNat = 0 then S.toList else merge S.toList what_I_meant_compiled
  let env ← getEnv
  let modules := env.header.moduleNames.map (h.getName.isPrefixOf ·)
  env.constants.map₁.forM (fun declName declInfo => do
    if modules[env.const2ModIdx[declName].get! (α := Nat)]!
    then  if declInfo.isThm
          then
            let data :=  (List.join ((Name.getStringList declName).map thm_parse)) -- List.dedup makes Lean lose it...
            dbg_trace s!"Data: {data}"
            let mut count := n.getNat
            dbg_trace s!"Count init: {count}"
            for d in data do
              if d ∈ Sm
              then
                if count ≠ 0
                then
                  dbg_trace s!"Count decreased to {count-1}"
                  count := count - 1
                else
                  dbg_trace s!"Printing"
                  logInfo m!"{declName} :\n{← Command.liftTermElabM (Meta.ppExpr declInfo.type)}\n"
                  break
            if count = 0
            then logInfo m!"{declName} :\n{← Command.liftTermElabM (Meta.ppExpr declInfo.type)}\n"
            else return ()
          else return ()
    else return ())


#exit

nomenclature 0 2 `Batteries.Data.List with pairwise append

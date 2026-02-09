
/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/


import LeanGrow.Src.Core.Induction.Format
import LeanGrow.Src.Data.CTrie.Basic
import LeanGrow.Src.Utils.Lean.ImportExport
import LeanGrow.Src.Utils.Std.Name
import LeanGrow.Src.Utils.Lean.Blacklisting


open Lean Meta


-- # Build

/-- Expects `module` to be in environement-/
@[inline]
def getElabElims (module : Name) : CoreM (Array Name) := do
  let env ← getEnv
  let .some midx := env.getModuleIdx? module | throwError s!"[getElabElims] was queried with odule {module}, but env doesn't have it in header"
  return (TagAttribute.ext Lean.Elab.Term.elabAsElim).getModuleEntries env midx

@[inline]
def getElabElims' (env : Environment) (midx : Nat) : CoreM (Array Name) := do
  return (TagAttribute.ext Lean.Elab.Term.elabAsElim).getModuleEntries env midx


/--
As key for the eliminator `elim`, we use the name of the head of the last arguement.
This makes for most eliminators, such as `List.Perm.recOnSwap'` or `Fin.succRecOn`, but
can lead to false positives, like `Fin.reverseInduction` when the fvar is of form
`Fin m` and not `Fin (m+1)`. We could remedy this by using a path-index instead of a trie.
Also, it is possible to declare eliminators for which our induction will not work:
eliminators that have two or more independent "motArgMv", for example. We could handle
them by searching for multiple inducible fvars in the target, but this is a lot of work
for cases no one uses so far ...
-/
@[inline]
def deriveElabElimKeyVal (elim : Name) : MetaM (ByteArray × RecursorCache) := do
  let val ← processRecursorCache elim
  let .some lastArg := val.motArgMv[val.motArgMv.size -1]? | throwError s!"[deriveElimKeyVal] eliminator {elim} has no arguemts ?!?"
  let T ← inferType lastArg -- still in context
  let .const TH  _ := (← whnfAtMostI T).getAppFn | throwError s!"[deriveElimKeyVal] eliminator {elim} has last arguement who's types head isn't a constant"
  let key := TH.toString.toUTF8
  return (key,val)



/-- Expects `module` to be in environement-/
@[inline]
def getCustomElims (module : Name) : CoreM (Array (Array Name × Name)) := do
  let env ← getEnv
  let .some midx := env.getModuleIdx? module | throwError s!"[getCustomElims] was queried with odule {module}, but env doesn't have it in header"
  let elims := customEliminatorExt.getState env |>.map
  let res ← elims.foldM (fun A (rec?, key) val => do
    if rec?
    then
      let .some didx := env.getModuleIdxFor? val | throwError s!"[getCustomElims] {val} has no module index in this env"
      if didx == midx
      then
        return A.push (key,val)
      else
        return A
    else
      return A
    ) #[]
  return res



@[inline]
def getCustomElims' (env : Environment) (midx : Nat) : CoreM (Array (Array Name × Name)) := do
  let elims := customEliminatorExt.getState env |>.map
  let res ← elims.foldM (fun A (rec?, key) val => do
    if rec?
    then
      let .some didx := env.getModuleIdxFor? val | throwError s!"[getCustomElims] {val} has no module index in this env"
      if didx == midx
      then
        return A.push (key,val)
      else
        return A
    else
      return A
    ) #[]
  return res



@[inline]
def deriveCustomElimKeyVal (elimData : Array Name × Name) : MetaM (Array (ByteArray × RecursorCache)) := do
  let val ← processRecursorCache elimData.2
  let res := elimData.1.map (fun x => (x.toString.toUTF8, val))
  return res



partial def getNewDeclarations (done : List Declaration) (prior now : Environment) : List ConstantInfo → MetaM (List Declaration)
  | [] => return done
  | info :: infos =>
      match info.value? with
      | .none => getNewDeclarations done prior now infos
      | .some V => do
          let newCs := V.getUsedConstants.filter (fun x => !(prior.contains x))
          let newIs := newCs.map (now.find?) |>.reduceOption.foldl (fun L i => i :: L) infos
          match info with
          | .thmInfo I => getNewDeclarations (.thmDecl I :: done) prior now newIs
          | .defnInfo I => getNewDeclarations (.defnDecl I :: done) prior now newIs
          | .opaqueInfo I => getNewDeclarations (.opaqueDecl I :: done) prior now newIs
          | _ => getNewDeclarations done prior now newIs


def processFunIndParamInfo (info : Array FunIndParamKind) : List Nat :=
  Id.run do
    let mut i := 0
    let mut L := []
    for I in info do
      match I with
      | .target =>
          L := i :: L
          i := i+1
      | _ =>
          i := i+1
    return L



/-- Given the name of a function (or any def), return the module name its in,
the declaration corresponding to the functional induction principle, the
function name as bytearray, and the `RecursorCache` corresponding to the functional
induction. The plan will be to add the declarations with `Lean.addAndCompile`
at query load time, and simply pickle them at cache time, so that we can assume
the functional induction principles are in the environement at query time.
-/
@[inline]
def deriveFunIndKeyVal (funName : Name) : MetaM (Option (Name × List Declaration × ByteArray × FunRecursorCache)) := do
  let env ← getEnv
  let modules := env.header.moduleNames
  let .some midx := env.getModuleIdxFor? funName | throwError "[deriveFunIndKeyVal] bizare case of {funName} not having a module index in the current evironment"
  let mod := modules[midx]!
  let funInd? ← getFunIndInfo? false true funName
  match funInd? with
  | .none => return .none
  | .some funInd =>
      let now ← getEnv
      match now.find? funInd.funIndName with
      | .some I@(.thmInfo _) =>
          let key := funName.toString.toUTF8
          let val ← processRecursorCache funInd.funIndName
          let fa := processFunIndParamInfo funInd.params
          let decs ← getNewDeclarations [] env now [I]
          return .some (mod,decs,key,⟨val, fa, funInd.params.size⟩)
      | _ => throwError "[deriveFunIndKeyVal] {funInd.funIndName} not found or not a theorem"


#check List.append.induct
#check List.append.induct_unfolding





@[inline]
def deriveFunIndKeyVal' (funName : Name) : MetaM (Option (List Declaration × ByteArray × FunRecursorCache)) := do
  let env ← getEnv
  let funInd? ← getFunIndInfo? false false funName
  match funInd? with
  | .none =>
    return .none
  | .some funInd =>
      let now ← getEnv
      match now.find? funInd.funIndName with
      | .some I@(.thmInfo _) =>
          let key := funName.toString.toUTF8
          let val ← processRecursorCache funInd.funIndName
          let fa := processFunIndParamInfo funInd.params
          let decs ← getNewDeclarations [] env now [I]
          return .some (decs,key,⟨val, fa, funInd.params.size⟩)
      | _ => throwError "[deriveFunIndKeyVal] {funInd.funIndName} not found or not a theorem"



structure RecursorCachePickle where
  module : Name
  funinducts : Array Declaration
  funrecu : CTrie FunRecursorCache
  elimrecu : CTrie (List RecursorCache)
deriving Inhabited

def RecursorCachePickle.emptyNamed (modu : Name) : RecursorCachePickle where
  module := modu
  funinducts := #[]
  funrecu := .empty
  elimrecu := .empty

def LeanGrow.mkRecuCacheName := fun module : Name => s!"RecursorCache_{module.toUnderscoreString}"



def buildRecursorCache_core (module : Name) : MetaM RecursorCachePickle := do
  let env ← getEnv
  let .some midx := env.getModuleIdx? module | throwError s!"[buildRecursorCache] module {module} has no index"
  let consts := (env.header.moduleData[midx]!).constants
  let mut elimrecu : CTrie (List RecursorCache) := .leaf
  let ee ← getElabElims' env midx
  for n in ee do
    let (key,val) ← deriveElabElimKeyVal n
    elimrecu := elimrecu.upsert key (fun
      | .none => .some [val]
      | .some V => .some <| V.insert val -- *Note* duplicates (customelim & elabelim) may exist, such as `Nat.recAux` (in 4.18), so we avoid them
      )
  let ce ← getCustomElims' env midx
  for d in ce do
    let data ← deriveCustomElimKeyVal d
    for (key,val) in data do
      elimrecu := elimrecu.upsert key (fun
        | .none => .some [val]
        | .some V => .some <| V.insert val
        )
  -- *Note* do ↑ before ↓ since the latter will modify env, and this order makes for linear use (?)
  let mut funrecu : CTrie FunRecursorCache := .leaf
  let mut funinducts := #[]
  for con in consts do
    if con.isDefinition
    then
      if con.name.blackListCaching env
      then
        continue
      else
        match ← deriveFunIndKeyVal' con.name with
        | .none =>
            continue
        | .some (decs,key,recu) =>
            funrecu := funrecu.insert  key recu
            for dec in decs do
              funinducts := funinducts.push dec
    else continue
  let res : RecursorCachePickle := ⟨module,funinducts, funrecu, elimrecu⟩
  return res


/--
**Warning ?** : set traces to Flag.none if using with `#eval` as `stdImportTracePickle` frees momery
that traces may refer to (didn't test this...)
-/
unsafe def buildRecursorCache (module : Name) : IO Unit :=
  stdImportTracePickle #[module] {} (LeanGrow.mkRecuCacheName module) do
    let res ← buildRecursorCache_core module
    return (res, "Ready to recurse")


-- # Explore


unsafe def withRecursorCache (module : Name) (act : RecursorCachePickle → MetaM String) : IO Unit := do
  let cN := s!"RecursorCache_{module.toUnderscoreString}"
  stdWithUnpickleTracing RecursorCachePickle cN <| fun unpick => do
    withImportModulesTracingPass #[module] {} <| fun env => do
      stdMetaRun env do
        for dec in unpick.funinducts do
          addAndCompile dec
        act unpick

unsafe def withRecursorCacheWith
  (ctx : Meta.Context) (st : Meta.State)
  (module : Name) (act : RecursorCachePickle → MetaM String) : IO Unit := do
  let cN := s!"RecursorCache_{module.toUnderscoreString}"
  stdWithUnpickleTracing RecursorCachePickle cN <| fun unpick => do
    withImportModulesTracingPass #[module] {} <| fun env => do
      stdMetaRunWithMeta ctx st env do
        for dec in unpick.funinducts do
          addAndCompile dec
        act unpick

unsafe def withRecursorCacheWithMulti
  (ctx : Meta.Context) (st : Meta.State)
  (modules : Array Name) (act : Array RecursorCachePickle → MetaM String) : IO Unit := do
  let cNs := modules.map (fun module => s!"RecursorCache_{module.toUnderscoreString}")
  stdWithUnpickleTracingMulti RecursorCachePickle cNs <| fun unpicks => do
    withImportModulesTracingPass modules {} <| fun env => do
      stdMetaRunWithMeta ctx st env do
        for unpick in unpicks do
          for dec in unpick.funinducts do
            addAndCompile dec
        act unpicks


unsafe def RecursorCache_printFunIndNames (module : Name) : MetaM Unit := do
  withRecursorCache module <| fun cache => do
    let allNames := cache.funrecu.toList.foldl [] (fun _ r  L => r.name.toString :: L)
    let res := String.intercalate "\n" allNames
    return res

unsafe def RecursorCache_printFunIndNamesWithKeys (module : Name) : MetaM Unit := do
  withRecursorCache module <| fun cache => do
    let allNames := cache.funrecu.toList.toListOfProd.foldl (fun L (s,r) => s!"{r.name.toString} with keys {s}" :: L) []
    let res := String.intercalate "\n" allNames
    return res


unsafe def RecursorCache_printElimNames (module : Name) : MetaM Unit := do
  withRecursorCache module <| fun cache => do
    let allNames := cache.elimrecu.toList.foldl [] (fun _ x L => x.foldl (fun L r => r.name.toString :: L) L)
    let res := String.intercalate "\n" allNames
    return res

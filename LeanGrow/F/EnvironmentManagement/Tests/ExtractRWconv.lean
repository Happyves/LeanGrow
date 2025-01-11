
import Mathlib.Tactic

open Lean Meta


-- convert requires import Mathlib.Tactic which clashes with my stuff, for some reason


inductive rwPartType where
| ofThm (subproof : Expr) (name : Name) (rel_args : List Expr)
| ofLocal (subproof : Expr)
| none
deriving Inhabited, Repr, BEq

def getRelevantArgsOTypes (as : Array Expr) : MetaM (List Expr) := do
    let mut Ts := []
    for e in as do
      let T ← inferType e
      let TT ← inferType T
      if TT.isProp
      then
        Ts := e :: Ts
    return (Ts)


def extractRW_main (proof : Expr) : MetaM rwPartType := -- subproof, thm name and args
  match proof with
  | .app _ _ =>
      let (h,as) := proof.getAppFnArgs
      if h == `Eq.mp || h == `Eq.mpr
      then
        let rwPart := as.get! 2
        let subproof := as.get! 3
        match rwPart with
        | .app (.app (.const ID _) _) (.app _ core) => -- id and congrArd, assuming no reduction
            if ID == `id -- to avoid false positive when its actually a `convert`
            then
              match core with
              | .app _ _ | .const _ _ => -- are there equalities that require not arguements ??
                let (H,AS) := core.getAppFnArgs
                if H == `Eq.symm
                then
                  let final := AS.get! 3
                  match final with
                  | .app _ _ | .const _ _ => -- are there equalities that require not arguements ??
                    let (n,args) := final.getAppFnArgs
                    do
                      let relArgs ← getRelevantArgsOTypes args
                      return .ofThm subproof n relArgs
                  | _ => pure (.ofLocal subproof)
                else
                  do
                    let relArgs ← getRelevantArgsOTypes AS
                    return .ofThm subproof H relArgs
              | _ => pure (.ofLocal subproof)
            else pure .none
        | _ => pure .none
      else pure .none
  | _ => pure .none



/-
rw, simp_rw, nth_rewrite

All produce terms of the form `Eq.mpr (id (congrArg _ thm-appli-for-rw) subproof)`
-/

#check Eq.mp
#check Eq.mpr
#check Eq.symm


/-- Requires terms to *not* be fully beta reduced -/
partial def extractConvert_main (proof : Expr) : MetaM (List rwPartType) :=
  let rec getEqPos (pos : Nat) (cache : List Nat) : Expr → List Nat
    | .lam _ t b _ =>
        match t.getAppFn' with
        | .const n _ =>
            if n == `Eq
            then getEqPos pos.succ ( pos :: cache) b
            else getEqPos pos.succ cache b
        | _ => getEqPos pos.succ cache b
    | _ => cache

  let rec core (subproof : Expr) (ta : Array Expr) : MetaM (List rwPartType) :=
      let Main := ta.get! 3
      let H := Main.getAppFn
      match H with
      | .lam _ _ _ _ =>
          let eq_pos := getEqPos 0 [] H -- perhaps too naive ? infer and reduce on args to check for equality ?
          let AS := Main.getAppArgs
          let rw_args := eq_pos.foldl (fun L i => (AS.get! i) :: L) []
          let cleaned := rw_args.map (fun x =>
            let (H,AS) := x.getAppFnArgs
            if H == `Eq.symm
            then AS.get! 3
            else x
            )
          do
            let res ← cleaned.mapM (fun final =>
              match final with
              | .app _ _ | .const _ _ => -- are there equalities that require not arguements ??
                let (n,args) := final.getAppFnArgs
                if n == `eq_of_heq
                then
                  core subproof args
                else
                  do
                    let relArgs ← getRelevantArgsOTypes args
                    return [.ofThm subproof n relArgs]
              | _ => pure ([.ofLocal subproof])
              )
            return (res.join.filter (fun x => x != .none))
      | _ => pure []

  match proof with
  | .app _ _ =>
      let (h,as) := proof.getAppFnArgs
      if h == `Eq.mp || h == `Eq.mpr
      then
        let rwPart := as.get! 2
        let subproof := as.get! 3
        let (n,ta) := rwPart.getAppFnArgs
        if n == `eq_of_heq
        then core subproof ta
        else pure []
    else pure []
  | _ => pure []

#check Eq.ndrec
#check Eq.rec
#check Eq.recOn
#check Eq.casesOn

partial def extractCongrRaw_main (proof : Expr) : MetaM rwPartType := do
  let cproof ← whnf proof -- required by congr
  match cproof with
  | .app _ _ =>
      --let (h,as) := proof.getAppFnArgs -- gets Nmae.anonymous instead of Eq.rec 0_0 ; check if fixed in future versions
      let h := cproof.getAppFn'.constName!
      let as := cproof.getAppArgs
      if h == `Eq.rec || h == `Eq.ndrec
      then
        let rwPart := as.get! 5
        let subproof := as.get! 3
        match rwPart with
        | .app _ _ | .const _ _ =>
          let (H,AS) := rwPart.getAppFnArgs
          if H == `Eq.symm
          then
            let final := AS.get! 3
            match final with
            | .app _ _ | .const _ _ => -- are there equalities that require not arguements ??
              let (n,args) := final.getAppFnArgs
              let relArgs ← getRelevantArgsOTypes args
              return .ofThm subproof n relArgs
            | _ => pure (.ofLocal subproof)
          else
            let relArgs ← getRelevantArgsOTypes AS
            return .ofThm subproof H relArgs
        | _ => pure (.ofLocal subproof)
      else
        if h == `Eq.recOn || h == `Eq.casesOn
        then
          let rwPart := as.get! 4
          let subproof := as.get! 5
          match rwPart with
          | .app _ _ | .const _ _ =>
            let (H,AS) := rwPart.getAppFnArgs
            if H == `Eq.symm
            then
              let final := AS.get! 3
              match final with
              | .app _ _ | .const _ _ => -- are there equalities that require not arguements ??
                let (n,args) := final.getAppFnArgs
                let relArgs ← getRelevantArgsOTypes args
                return .ofThm subproof n relArgs
              | _ => pure (.ofLocal subproof)
            else
              let relArgs ← getRelevantArgsOTypes AS
              return .ofThm subproof H relArgs
          | _ => pure (.ofLocal subproof)
        else pure (.none)
  | _ => pure (.none)

def a := 42


def extractRWall_main (proof : Expr) : MetaM (List rwPartType) := do
  let rw ← extractRW_main proof
  match rw with
  | .none =>
      let conv ← extractConvert_main proof
      match conv with
      | [] =>
        let congrRaw ← extractCongrRaw_main proof
        match congrRaw with
        | .none => return []
        | _ => return [congrRaw]
      | _ => return conv
  | _ => return [rw]




theorem test3 (n m p k: Nat) (hnm : n = m) (hpk : p = k) (hn : n + p = 42)
  : m + k = 42 := by
  convert hn
  exact hnm.symm
  exact hpk.symm

#print test3

theorem test4 (n m p k: Nat) (hnm : n = m) (hpk : p = k) (hn : n  = p)
  : m = k := by
  convert hn
  exact hnm.symm
  exact hpk.symm

#print test4


theorem test5 (n m p k r s: Nat) (hnm : n = m) (hpk : p = k) (hrs : r = s) (hn : n +p +r  = 42)
  : m + k + s = 42 := by
  convert hn
  exact hnm.symm
  exact hpk.symm
  exact hrs.symm


#print test5



elab "runTest" n:name : command => do
  let .some thm := (← getEnv).find?  n.getName | pure ()
  let .some proof := thm.value? | pure ()
  let res ← Elab.Command.liftTermElabM (lambdaLetTelescope proof (fun _ head => extractConvert_main head ) (cleanupAnnotations := true))
  IO.println (repr res)

elab "runTestAll" n:name : command => do
  let .some thm := (← getEnv).find?  n.getName | pure ()
  let .some proof := thm.value? | pure ()
  let res ← Elab.Command.liftTermElabM (lambdaLetTelescope proof (fun _ head => extractRWall_main head ) (cleanupAnnotations := true))
  IO.println (repr res)


runTest `test3
runTestAll `test3
runTest `test4
runTestAll `test4
runTest `test5
runTestAll `test5


theorem test6 (n m p k: Nat) (hnm : n = m)  (hn : p + k + n  = 42)
  : k + p + m = 42 := by
  convert hn using 2
  apply Nat.add_comm
  exact hnm.symm


#print test6

runTest `test6
runTestAll `test6

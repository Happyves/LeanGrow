
import LeanGrow.F.EnvironmentManagement.SampleRegular.API

open Lean Meta


inductive rwPartType where
| ofThm (subproof : Expr) (name : Name) (rel_args : List Expr)
| ofLocal (subproof : Expr)
| none
deriving Inhabited, Repr, BEq

def extractRW_main (proof : Expr) : MetaM rwPartType := -- subproof, thm name and args
  match proof with
  | .app _ _ =>
      let (h,as) := proof.getAppFnArgs
      if h == `Eq.mp || h == `Eq.mpr
      then
        let rwPart := as.get! 2
        let subproof := as.get! 3
        match rwPart with
        | .app _ (.app _ core) => -- id and congrArd, assuming no reduction
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

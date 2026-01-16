
/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/


import LeanGrowBeta.Utils.Lean.Expr.Basic
import LeanGrowBeta.Utils.Lean.Generalize
import LeanGrowBeta.Utils.Lean.Revert

import LeanGrowBeta.Core.Rewriting.Dependencies


open Lean Meta




/-- Note: on 4.23 with new tracing system,
uncommeting mtrace leads to massive compile time-/
@[specialize]
def topBackRW
  (revert : MVarId → Array FVarId → LocalContext → LocalInstances → Array (FVarId × (List LocalDecl)) → MetaM (Array FVarId × MVarId)) -- should handle woker fvars
  (l1 : LocalContext) (l2 : LocalInstances)
  (dirs : rwDirs) (backIdx pos : Nat) (within pat eqProof : Expr)
  : MetaM (Prod3 Expr LocalContext LocalInstances) := do
  -- trace set TracingFlags.none in do
  let ⟨depFvs,l1,l2⟩ ←  getDeps l1 l2 dirs within pat 0
  --mtrace on .zero with s!"[topBackRW] depFvs {repr depFvs}"
  let tmp ← generalizeTnodesSafeIgnoring l1 l2 within
    (fun x _ _ => return x == pat )
    (fun x l1 l2 => do
      let xT ← InferType x l1 l2
      return Expr.hasPatternTR pat xT
      -- *Note* we don't look for transitive dependecies ...
      )
    (fun _ _ _ => return true)
  match tmp with
  | .none =>
      (throwError s!"[topBackRW] generalisation  of tnodes failed in 'within' {← ppExpr within}")
  | .some within tnodes => do
      withReader (fun ctx => {ctx with lctx := l1, localInstances := l2}) do
        --mtrace on .zero with s!"[topBackRW] within {← ppExpr within}"
        --mtrace on .zero with s!"[topBackRW] tnodes {← tnodes.mapM ppExpr}"
        let dummy ← mkFreshExprMVar (.some within)
        let (allRev, revMv) ← revert dummy.mvarId! depFvs.toArray l1 l2 #[]
        --mtrace on .zero with s!"[topBackRW] allRev {repr allRev}"
        let within ← revMv.getType
        --mtrace on .zero with s!"[topBackRW] within {← ppExpr within}"
        let (within, proofs) ← generalizeProofsIgnoring l1 l2 within
          (fun x _ _ => return x == pat)
          (fun x l1 l2 => do
            let T ← InferType x l1 l2
            return Expr.hasPatternTR pat T)
        --mtrace on .zero with s!"[topBackRW] within {← ppExpr within}"
        --mtrace on .zero with s!"[topBackRW] proofs {← proofs.mapM ppExpr}"
        let patType ← inferType pat
        --mtrace on .zero with s!"[topBackRW] patType {← ppExpr patType}"
        let patTypeLevel ← getLevel patType
        let motive := Expr.abstractPatBind pat patType within
        --mtrace on .zero with s!"[topBackRW] motive {← ppExpr motive}"
        let motT ← inferType motive
        --mtrace on .zero with s!"[topBackRW] motT {← ppExpr motT}"
        let .sort motL := ← whnf motT.getForallBody | throwError "[topBackRW] motive's type isn't sort headed, it's {← ppExpr motT}"
        let .some (_,_,rep) := (← inferType eqProof).eq? | throwError "[topBackRW] eq proof insn't ... it's {← ppExpr eqProof}"
        --mtrace on .zero with s!"[topBackRW] rep {← ppExpr rep}"
        --mtrace on .zero with s!"[topBackRW] eqProof {eqProof}, of type {← ppExpr (← inferType eqProof)},\nok ? {← isTypeCorrect eqProof}"
        let eqProof ← mkAppM `Eq.symm #[eqProof]
        --mtrace on .zero with s!"[topBackRW] eqProof {← ppExpr eqProof}, of type {← ppExpr (← inferType eqProof)}"
        let newGoal := (Expr.app motive rep).headBeta
        --mtrace on .zero with s!"[topBackRW] newGoal {← ppExpr newGoal}"
        let tn := tnode backIdx pos
        let ⟨_,l1,l2⟩ ← WithLocalDecl tn newGoal l1 l2
        let mainProof := mkAppN (.const `Eq.ndrec [motL,patTypeLevel]) #[patType, rep, motive, .fvar ⟨tn⟩ , pat, eqProof]
        --mtrace on .zero with s!"[topBackRW] mainProof {← ppExpr mainProof}, of type {← ppExpr (← inferType mainProof)}"
        let allRev := allRev.foldl (fun R x =>
          match x.name with
          | .num (.str _ k) _ => if k == "u" then R else R.push (Expr.fvar x)
          | _ => R
          ) #[]
        --mtrace on .zero with s!"[topBackRW] allRev {repr allRev}"
        let withRevs := mkAppN mainProof (proofs ++ allRev ++ tnodes)
        --mtrace on .zero with s!"[topBackRW] withRevs {← ppExpr withRevs}, of type {← ppExpr (← inferType withRevs)}"
        return ⟨withRevs,l1,l2⟩



@[inline]
def castProofForRW
  (pat rep patType eqProof x : Expr) (patTypeLevel : Level) : MetaM Expr := do
  -- trace set Tracing.Flags.none in do
  let xT ← inferType x
  --mtrace on .zero with s!"[castProofForRW] xT {← ppExpr xT}"
  let eqMot := Expr.abstractPat pat xT
  let rT := (Expr.app (.lam `castProofForRW patType eqMot .default) rep).headBeta
  --mtrace on .zero with s!"[castProofForRW] rT {← ppExpr rT}"
  let eqMot := .lam `castProofForRW patType (mkAppN (.const `Eq [1]) #[.sort 0, xT,eqMot]) .default
  --mtrace on .zero with s!"[castProofForRW] eqMot {← ppExpr eqMot}, of type {← ppExpr (← inferType eqMot)}"
  let eqRfl := mkAppN (.const `Eq.refl [1]) #[.sort 0, xT]
  --mtrace on .zero with s!"[castProofForRW] eqRfl {← ppExpr eqRfl}, of type {← ppExpr (← inferType eqRfl)}"
  let eqP := mkAppN (.const `Eq.ndrec [0,patTypeLevel]) #[patType,pat,eqMot,eqRfl,rep,eqProof]
  --mtrace on .zero with s!"[castProofForRW] eqP {← ppExpr eqP}, of type {← ppExpr (← inferType eqP)}"
  let castMain := mkAppN (.const `cast [0]) #[xT,rT,eqP,x]
  --mtrace on .zero with s!"[castProofForRW] castMain {← ppExpr castMain}, of type {← ppExpr (← inferType castMain)}"
  return castMain
  -- assumes `pat` has no abstracted dependecies in the reverted types



#check cast
#check Eq.refl
#check Eq.ndrec

@[specialize]
def topForwRW
  (revert : MVarId → Array FVarId → LocalContext → LocalInstances → Array (FVarId × (List LocalDecl)) → MetaM (Array FVarId × MVarId)) -- should handle woker fvars
  (l1 : LocalContext) (l2 : LocalInstances)
  (dirs : rwDirs) (rwableFvar : Expr) (within pat eqProof : Expr)
  : MetaM (Prod3 Expr LocalContext LocalInstances) := do
  -- trace set Tracing.Flags.none in do
  let ⟨depFvs,l1,l2⟩ ←  getDeps l1 l2 dirs within pat 0
  --mtrace on .zero with s!"[topBackRW] depFvs {repr depFvs}"
  withReader (fun ctx => {ctx with lctx := l1, localInstances := l2}) do
    let dummy ← mkFreshExprMVar (.some within)
    let (allRev, revMv) ← revert dummy.mvarId! depFvs.toArray l1 l2 #[]
    --mtrace on .zero with s!"[topForwRW] allRev {repr allRev}"
    -- if ← allRev.anyM (fun x => return !(← isProp (← x.getType)))
    -- then
    --   throwError s!"[topForwRW] 'within' contains dependent non-prop fvars: {← ppExpr within}"
    -- else
    let within ← revMv.getType
    --mtrace on .zero with s!"[topForwRW] within {← ppExpr within}"
    let (within, proofs) ← generalizeProofsIgnoring l1 l2 within
        (fun x _ _ => return x == pat)
        (fun x l1 l2 => do
          let T ← InferType x l1 l2
          return Expr.hasPatternTR pat T)
    --mtrace on .zero with s!"[topForwRW] within {← ppExpr within}"
    --mtrace on .zero with s!"[topForwRW] proofs {← proofs.mapM ppExpr}"
    let patType ← inferType pat
    --mtrace on .zero with s!"[topForwRW] patType {← ppExpr patType}"
    let patTypeLevel ← getLevel patType
    let motive := Expr.abstractPatBind pat patType within
    --mtrace on .zero with s!"[topForwRW] motive {← ppExpr motive}"
    let motT ← inferType motive
    --mtrace on .zero with s!"[topForwRW] motT {← ppExpr motT}"
    let .sort motL := ← whnf motT.getForallBody | throwError "[topForwRW] motive's type isn't sort headed, it's {← ppExpr motT}"
    let .some (_,_,rep) := (← inferType eqProof).eq? | throwError "[topForwRW] eq proof insn't ... it's {← ppExpr eqProof}"
    --mtrace on .zero with s!"[topForwRW] rep {← ppExpr rep}"
    let mainProof := mkAppN (.const `Eq.ndrec [motL,patTypeLevel]) #[patType, pat, motive, rwableFvar , rep, eqProof]
    --mtrace on .zero with s!"[topForwRW] mainProof {← ppExpr mainProof}, of type {← ppExpr (← inferType mainProof)}"
    let allRev := allRev.foldl (fun R x =>
      match x.name with
      | .num (.str _ k) _ => if k == "u" then R else R.push (Expr.fvar x)
      | _ => R
      ) #[]
    --mtrace on .zero with s!"[topForwRW] allRev {repr allRev}"
    let castedArgs ← (proofs ++ allRev).mapM
      (fun x => castProofForRW pat rep patType eqProof x patTypeLevel)
    let withRevs := mkAppN mainProof castedArgs
    --mtrace on .zero with s!"[topForwRW] withRevs {← ppExpr withRevs}, of type {← ppExpr (← inferType withRevs)}"
    return ⟨withRevs,l1,l2⟩


#check funext

#check mkFunExt
/-- We prefer this over `mkFunExt` because the defeq with standard config that i relies on
doesn't have the properties we want. For example in the context of `(n : Nat) (h : ∀ x, n+x = x+n)`,
regular `mkFunExt` will infer `f` to be `HAdd`, instead f making a new fun, as we desire
-/
@[inline]
def mkFunExt! (extHyp : Expr) : MetaM Expr := do
  -- trace set Tracing.Flags.none in do
  let T ← inferType extHyp
  forallTelescope T <| fun extArgs head => do
    let extArg := extArgs[0]! --should be only one
    let .some (eqT,L,R) := head.eq? | throwError s!"[mkFunExt!] expected eq, got {← ppExpr head}"
    --mtrace on .zero with s!"[mkFunExt!] eqT {← ppExpr eqT}, L {← ppExpr L}, R {← ppExpr R}"
    let α ← inferType extArg
    let u ← getLevel α
    --mtrace on .zero with s!"[mkFunExt!] α {← ppExpr α}, u {u}"
    let β := Expr.abstractPatBind extArg α eqT
    --mtrace on .zero with s!"[mkFunExt!] β {← ppExpr β}"
    let bT ← inferType β
    let .sort v := bT.getForallBody | throwError s!"[mkFunExt!] expected ∀ with sort head, got {← ppExpr β}"
    --mtrace on .zero with s!"[mkFunExt!] v {v}"
    let f := Expr.abstractPatBind extArg α L
    let g := Expr.abstractPatBind extArg α R
    --mtrace on .zero with s!"[mkFunExt!] f {← ppExpr f}, g {← ppExpr g}"
    return mkAppN (.const `funext [u,v]) #[α,β,f,g,extHyp]

#check pi_congr

@[inline]
def mkPiCongr! (extHyp : Expr) : MetaM Expr := do
  let T ← inferType extHyp
  forallTelescope T <| fun extArgs head => do
    let extArg := extArgs[0]! --should be only one
    let .some (_,L,R) := head.eq? | throwError s!"[mkPiCongr!] expected eq, got {← ppExpr head}"
    let α ← inferType extArg
    let u ← getLevel α
    let β := Expr.abstractPatBind extArg α L
    let β' := Expr.abstractPatBind extArg α R
    let bT ← inferType β
    let .sort v := bT.getForallBody | throwError s!"[mkPiCongr!] expected ∀ with sort head, got {← ppExpr β}"
    return mkAppN (.const `pi_congr [u,v]) #[α,β,β',extHyp]

#check let_body_congr

@[inline]
def mkLetBodyCongr!
  (l1 : LocalContext) (l2 : LocalInstances)
  (extHyp : Expr) (letVal : Expr) : MetaM (Prod3 Expr LocalContext LocalInstances) := do
  let T ← inferType extHyp
  let ⟨head, extArgs, l1,l2⟩ ← forallLetTelescope l1 l2 T #[]
  let extArg := extArgs[0]! --should be only one
  let .some (eqT,L,R) := head.eq? | throwError s!"[mkLetBodyCongr!] expected eq, got {← ppExpr head}"
  let α ← inferType extArg
  let u ← getLevel α
  let β := Expr.abstractPatBind extArg α eqT
  let bT ← inferType β
  let .sort v := bT.getForallBody | throwError s!"[mkLetBodyCongr!] expected ∀ with sort head, got {← ppExpr β}"
  let b := Expr.abstractPatBind extArg α L
  let b' := Expr.abstractPatBind extArg α R
  let res := mkAppN (.const `let_body_congr [u,v]) #[α,β,b,b',letVal,extHyp]
  return ⟨res,l1,l2⟩


@[inline]
def adaptWorkers (workerDeps : Array (FVarId × (List LocalDecl))) (term : Expr) : Expr :=
  term.onAllSubtermsTR (fun
    | y@(.fvar ⟨.num (.str _ k) i⟩) =>
        if k == "w"
        then
          match workerDeps.find? (fun (⟨z⟩,_) => match z with | .num _ j => i == j | _ => false) with
          | .none => y
          | .some (rep,_) => .fvar rep
        else y
    | y => y
    )



@[specialize]
partial def handleBinders (back? : Bool)
  (revert : MVarId → Array FVarId → LocalContext → LocalInstances → Array (FVarId × (List LocalDecl)) → MetaM (Array FVarId × MVarId)) -- should handle woker fvars
  (l1 : LocalContext) (l2 : LocalInstances)
  (currentDepth : Nat) (nextDepths : List Nat) (workerDeps : Array (FVarId × (List LocalDecl)))
  (dirs : rwDirs) (within pat eqProof : Expr)
  : MetaM (Prod3 Expr LocalContext LocalInstances) := do
  -- trace set Tracing.Flags.none in do
  let rec @[inline] mainAct (k : rwDirs → Expr → Expr → Expr → Expr → Expr → LocalContext → LocalInstances → MetaM (Prod3 Expr LocalContext LocalInstances)) : MetaM (Prod3 Expr LocalContext LocalInstances) := do
    match nextDepths with
    | nextDepth :: furtherDepths =>
        --mtrace on .zero with s!"[handleBinders] call on within {← ppExpr within}, pat {← ppExpr pat}, dirs {repr dirs}"
        --mtrace on .zero with s!"[handleBinders] currentDepth {currentDepth}, nextDepth { nextDepth}"
        let ⟨boundedTermDirs, boundedTerm, l1,l2⟩ ← getNextBoundedTerm l1 l2 currentDepth nextDepth dirs within
        --mtrace on .zero with s!"[handleBinders] boundedTerm {← ppExpr boundedTerm}"
        let ⟨introTerm, introTermDirs, passWorker, workerDeps,l1,l2⟩ ← lambdaLetAllBoundedTelescopeWorkerDirsDeps l1 l2 boundedTerm #[] workerDeps nextDepth (nextDepth+1) boundedTermDirs
        --mtrace on .zero with s!"[handleBinders] introTerm {← ppExpr introTerm}, passWorker {← passWorker.mapM ppExpr}"
        --mtrace on .one with s!"[handleBinders] workerDeps {repr <| workerDeps.map (fun x => (x.1, x.2.map LocalDecl.fvarId))}"
        let ⟨res,l1,l2⟩ ← handleBinders back? revert l1 l2 (nextDepth+1) furtherDepths workerDeps introTermDirs introTerm pat eqProof
        --mtrace on .zero with s!"[handleBinders] local return {← ppExpr res}"
        withReader (fun ctx => {ctx with lctx := l1, localInstances := l2}) do
          let extHyp ← mkLambdaFVars passWorker res false false false false .default
          --mtrace on .zero with s!"[handleBinders] abstracted worker to {← ppExpr extHyp}"
          let ⟨extProof,l1,l2⟩ : (Prod3 Expr LocalContext LocalInstances) := ← do
            match boundedTermDirs with
            | .la .. => return ⟨← mkFunExt! extHyp,l1,l2⟩
            | .al .. => return ⟨← mkPiCongr! extHyp,l1,l2⟩
            | .le .. =>
                match boundedTerm with
                | .letE _ _ V _ _ => mkLetBodyCongr! l1 l2 extHyp V
                | _ => throwError s!"[handleBinders] expected letE, got {← ppExpr boundedTerm}"
            | _ => throwError s!"[handleBinders] expected binder, got {repr boundedTermDirs}"
          withReader (fun ctx => {ctx with lctx := l1, localInstances := l2}) do
            if currentDepth == 0
            then
              return ⟨extProof,l1,l2⟩
            else
              let .some (boundedType,_,boundedRep) := (← inferType extProof).eq? | throwError s!"[handleBinders] expected eq, got {← ppExpr (← inferType extProof)}"
              --mtrace on .zero with s!"[handleBinders] boundedType {← ppExpr boundedType}"
              --mtrace on .zero with s!"[handleBinders] boundedRep {← ppExpr boundedRep}"
              let supTermDirs := replaceDirsAtSupPattern dirs within boundedTerm
              --mtrace on .zero with s!"[handleBinders] supTermDirs {repr supTermDirs}"
              k supTermDirs within boundedTerm boundedType boundedRep extProof l1 l2
      | [] =>
        if currentDepth == 0
        then
          return ⟨eqProof,l1,l2⟩
        else
          --mtrace on .zero with s!"[handleBinders] base case reached"
          --mtrace on .one with s!"[handleBinders] within before {← ppExpr within}"
          let within := adaptWorkers workerDeps within
          --mtrace on .one with s!"[handleBinders] within after {← ppExpr within}"
          --mtrace on .one with s!"[handleBinders] pat before {← ppExpr pat}"
          let pat := adaptWorkers workerDeps pat
          --mtrace on .one with s!"[handleBinders] pat after {← ppExpr pat}"
          --mtrace on .one with s!"[handleBinders] eqProof before {← ppExpr eqProof}"
          let eqProof := adaptWorkers workerDeps eqProof
          --mtrace on .one with s!"[handleBinders] eqProof after {← ppExpr eqProof}"
          withReader (fun ctx => {ctx with lctx := l1, localInstances := l2}) do
            let .some (patType,_,rep) := (← inferType eqProof).eq? | throwError s!"[handleBinders] expected eq, got {← ppExpr (← inferType eqProof)}"
            k dirs within pat patType rep eqProof l1 l2
  mainAct <| fun supTermDirs within boundedTerm boundedType boundedRep extProof l1 l2 => do
    --mtrace on .two with s!"[handleBinders] in the context of boundedTerm {← ppExpr boundedTerm} and within {← ppExpr within}, supTermDirs {repr supTermDirs}, dirs {repr dirs}"
    withReader (fun ctx => {ctx with lctx := l1, localInstances := l2}) do
      let insta := within
      let instaT ← inferType insta
      --mtrace on .zero with s!"[handleBinders] instaT {← ppExpr instaT}"
      let instaL ← getLevel instaT
      let ⟨depFvs,l1,l2⟩ ← getDeps l1 l2 supTermDirs within boundedTerm currentDepth
      withReader (fun ctx => {ctx with lctx := l1, localInstances := l2}) do
        --mtrace on .zero with s!"[handleBinders] depFvs {repr depFvs}"
        if ← depFvs.anyM (fun fv => return !(← isProp (← fv.getType)))
        then
          throwError s!"[handleBinders] we reject non-prop fvars ; there is one in 'within': {← ppExpr within}"
        else
          --mtrace on .zero with s!"[handleBinders] depFvs {repr depFvs}"
          let rec @[inline] act (k : Expr → Array Expr → MetaM (Prod3 Expr LocalContext LocalInstances)) : MetaM (Prod3 Expr LocalContext LocalInstances) := do
            if back?
            then
              let tmp ← generalizeTnodesSafeIgnoring l1 l2 within
                (fun x _ _ => return x == boundedTerm )
                (fun x l1 l2 => do
                  let xT ← InferType x l1 l2
                  return Expr.hasPatternTR boundedTerm xT
                  -- *Note* we don't look for transitive dependecies ...
                  )
                (fun _ _ _ => return true)
              match tmp with
              | .none =>
                  (throwError s!"[handleBinders] failed to generalize tnodes (non-prop one ?) in within {← ppExpr within}")
              | .some x y => k x y
            else
              k within #[]
          act <| fun within tnodes => do
            --mtrace on .zero with s!"[handleBinders]  within {← ppExpr within}"
            --mtrace on .zero when back? with s!"[handleBinders] tnodes {← tnodes.mapM ppExpr}"
            let dummy ← mkFreshExprMVar (.some within)
            let (allRev, revMv) ← revert dummy.mvarId! depFvs.toArray l1 l2 workerDeps
            --mtrace on .zero with s!"[handleBinders] allRev {repr allRev}"
            if ← allRev.anyM (fun x => return !(← isProp (← x.getType)))
            then
              throwError s!"[handleBinders] 'within' contains dependent non-prop fvars: {← ppExpr within}"
            else
              let within ← revMv.getType
              --mtrace on .zero with s!"[handleBinders] within {← ppExpr within}"
              let (within, proofs) ← generalizeProofsIgnoring l1 l2 within
                (fun x _ _ => return x == boundedTerm)
                (fun x l1 l2 => do
                  let T ← InferType x l1 l2
                  return Expr.hasPatternTR boundedTerm T)
              --mtrace on .zero with s!"[handleBinders] within {← ppExpr within}"
              --mtrace on .zero with s!"[handleBinders] proofs {← proofs.mapM ppExpr}"
              let boundedTypeLevel ← getLevel boundedType
              let bnd := (tnodes.size + allRev.size + proofs.size)
              let eqMot := Expr.abstractPat boundedTerm within
              let eqMot ← eqMot.surgeryBoundedForallWD (fun head _ => do
                return mkAppN (.const `Eq [instaL]) #[instaT,insta,head]
                ) 0 bnd
              let eqRfl ← eqMot.lambdifyBoundedWD (fun _ _ => do
                return mkAppN (.const `Eq.refl [instaL]) #[instaT,insta]
                -- will hold by kernel proof irrelevance
                ) 0 bnd
              let eqMot := Expr.lam `handleBinders boundedType eqMot .default
              --mtrace on .zero with s!"[handleBinders] eqMot {← ppExpr eqMot}, of type {← ppExpr (← inferType eqMot)}"
              let eqRfl := Expr.app (.lam `handleBinders boundedType eqRfl .default) boundedTerm
              --mtrace on .zero with s!"[handleBinders] eqRfl {← ppExpr eqRfl}, of type {← ppExpr (← inferType eqRfl)}"
              let eqP := mkAppN (.const `Eq.ndrec [0,boundedTypeLevel]) #[boundedType,boundedTerm,eqMot,eqRfl,boundedRep,extProof]
              --mtrace on .zero with s!"[handleBinders] eqP {← ppExpr eqP}, of type {← ppExpr (← inferType eqP)}"
              -- *Note* we don't filter out unodes since we assume all unodes to be non-prop typed,
              -- so if they were dependecies, we'd have failed already
              let castedArgs ← (proofs ++ (allRev.map Expr.fvar) ++ tnodes).mapM
                (fun x => castProofForRW boundedTerm boundedRep boundedType extProof x boundedTypeLevel)
              let finalProof := mkAppN eqP castedArgs
              --mtrace on .zero with s!"[handleBinders] finalProof {← ppExpr finalProof}, of type {← ppExpr (← inferType finalProof)}"
              return ⟨finalProof,l1,l2⟩


#check Eq.refl
#check Eq.ndrec
#check Expr.abstractPat



@[specialize, inline]
def mainBackRW
  (revert : MVarId → Array FVarId → LocalContext → LocalInstances → Array (FVarId × (List LocalDecl)) → MetaM (Array FVarId × MVarId)) -- should handle woker fvars
  (l1 : LocalContext) (l2 : LocalInstances)
  (dirs : rwDirs) (backIdx pos : Nat) (within pat eqProof : Expr)
  : MetaM (Prod3 Expr LocalContext LocalInstances) := do
  -- trace set Tracing.Flags.none in do
  withReader (fun ctx => {ctx with lctx := l1, localInstances := l2}) do
    mtrace on .zero with s!"[mainBackRW] within {← PpExpr within l1 l2}"
    mtrace on .zero with s!"[mainBackRW] eqProof {← PpExpr eqProof l1 l2}"
    mtrace on .zero with s!"[mainBackRW] pat {← PpExpr pat l1 l2}"
    let ws := List.orderedUnion (← eqProof.getWorkerIndsTrans l1 l2) (← pat.getWorkerIndsTrans l1 l2)
    mtrace on .zero with s!"[mainBackRW] ws {ws}"
    -- let eqType ← inferType eqProof
      match ws with
      | _ :: _ =>
        let ⟨extProof,l1,l2⟩ ← handleBinders true revert l1 l2 0 ws #[] dirs within pat eqProof
        withReader (fun ctx => {ctx with lctx := l1, localInstances := l2}) do
          mtrace on .zero with s!"[mainBackRW] extProof {← PpExpr extProof l1 l2}"
          let .some (_,boundedTerm,_) := (← inferType extProof).eq? | throwError s!"[mainBackRW] expected eq, got {← ppExpr (← inferType extProof)}"
          mtrace on .zero with s!"[mainBackRW] boundedTerm {← PpExpr boundedTerm l1 l2}"
          let supTermDirs := replaceDirsAtSupPattern dirs within boundedTerm
          mtrace on .zero with s!"[mainBackRW] supTermDirs {repr supTermDirs}"
          let ⟨term,l1,l2⟩ ← topBackRW revert l1 l2 supTermDirs backIdx pos within boundedTerm extProof
            mtrace on .zero with s!"[mainBackRW] term {← PpExpr term l1 l2}"
            -- and indeed, it was a bug ; **Idea** use Expr.mdata ??
            -- let term := .lam `SampleHelper eqType (Expr.abstractPat eqProof term) .default
            -- -- we do this for sampling, to avoid the rw-construction
            -- -- **Bug for sure** eqProof has workers, term has bvars !!! Also, tnodes ...
            -- return ⟨.app term eqProof,l1,l2⟩
            return ⟨term,l1,l2⟩
      | _ => do
        let ⟨term,l1,l2⟩ ← topBackRW revert l1 l2 dirs backIdx pos within pat eqProof
        mtrace on .zero with s!"[mainBackRW] term {← PpExpr term l1 l2}"
        -- let term := .lam `SampleHelper eqType (Expr.abstractPat eqProof term) .default
        -- -- we do this for sampling, to avoid the rw-construction
        -- return ⟨.app term eqProof,l1,l2⟩
        return ⟨term,l1,l2⟩



@[specialize revert, inline]
def mainForwRW
  (revert : MVarId → Array FVarId → LocalContext → LocalInstances → Array (FVarId × (List LocalDecl)) → MetaM (Array FVarId × MVarId)) -- should handle woker fvars
  (l1 : LocalContext) (l2 : LocalInstances)
  (dirs : rwDirs) (rwableFvar : Expr) (within pat eqProof : Expr)
  : MetaM (Prod3 Expr LocalContext LocalInstances) := do
  -- trace set Tracing.Flags.none in do
  withReader (fun ctx => {ctx with lctx := l1, localInstances := l2}) do
    let ws := List.orderedUnion (← eqProof.getWorkerIndsTrans l1 l2) (← pat.getWorkerIndsTrans l1 l2)
    mtrace on .zero with s!"[mainForwRW] eqProof {← ppExpr eqProof}"
    mtrace on .zero with s!"[mainForwRW] pat {← ppExpr pat}"
    mtrace on .zero with s!"[mainForwRW] ws {repr ws}"
    -- let eqType ← inferType eqProof
    match ws with
    | _ :: _ =>
      let ⟨extProof,l1,l2⟩ ← handleBinders false revert l1 l2 0 ws #[] dirs within pat eqProof
      withReader (fun ctx => {ctx with lctx := l1, localInstances := l2}) do
        let .some (_,boundedTerm,_) := (← inferType extProof).eq? | throwError s!"[mainForwRW] expected eq, got {← ppExpr (← inferType extProof)}"
        let supTermDirs := replaceDirsAtSupPattern dirs within boundedTerm
        let ⟨term,l1,l2⟩ ← topForwRW revert l1 l2 supTermDirs rwableFvar within boundedTerm extProof
        -- let term := .lam `SampleHelper eqType (Expr.abstractPat eqProof term) .default
        -- -- we do this for sampling, to avoid the rw-construction
        -- -- **Bug for sure** eqProof has workers, term has bvars !!! Also, tnodes ...
        -- return ⟨.app term eqProof,l1,l2⟩
        return ⟨term,l1,l2⟩
    | _ =>
      let ⟨term,l1,l2⟩ ← topForwRW revert l1 l2 dirs rwableFvar within pat eqProof
      -- let term := .lam `SampleHelper eqType (Expr.abstractPat eqProof term) .default
      -- -- we do this for sampling, to avoid the rw-construction
      -- return ⟨.app term eqProof,l1,l2⟩
      return ⟨term,l1,l2⟩

-- #exit
@[specialize introAdmissible?]
def mainBackRWData
  (introAdmissible? : Nat → Bool) (depsCache : Array (List LocalDecl))
  (l1 : LocalContext) (l2 : LocalInstances)
  (dirs : rwDirs) (backIdx pos : Nat) (within pat eqProof : Expr)
  : MetaM (Prod3 Expr LocalContext LocalInstances) := do
  mainBackRW (fun x y l1 l2 z => MVarId.revert_NoTn_wDepsCache introAdmissible? l1 l2 x y depsCache z)
    l1 l2 dirs backIdx pos within pat eqProof

@[specialize, inline]
def mainForwRWData
  (introAdmissible? : Nat → Bool) (depsCache : Array (List LocalDecl))
  (l1 : LocalContext) (l2 : LocalInstances)
  (dirs : rwDirs) (rwableFvar : Expr) (within pat eqProof : Expr)
  : MetaM (Prod3 Expr LocalContext LocalInstances) := do
  mainForwRW (fun x y l1 l2 z => MVarId.revert_NoTn_wDepsCache introAdmissible? l1 l2 x y depsCache z)
    l1 l2 dirs rwableFvar within pat eqProof

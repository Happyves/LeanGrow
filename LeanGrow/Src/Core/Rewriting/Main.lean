
/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/


import LeanGrow.Src.Utils.Lean.Expr.Basic
import LeanGrow.Src.Utils.Lean.Generalize
import LeanGrow.Src.Utils.Lean.Revert

import LeanGrow.Src.Core.Rewriting.Dependencies


open Lean Meta




/-- Note: on 4.25 with new tracing system,
uncommeting --mtrace leads to massive compile time-/
@[specialize]
def topBackRW
  (introAdmissible? : Nat → Bool)
  (depsCache : Array DepCache)
  (RevCutOff : Nat)
  (l1 : LocalContext) (l2 : LocalInstances)
  (dirs : rwDirs) (backIdx pos : Nat) (within pat eqProof : Expr)
  : MetaM (Prod3 Expr LocalContext LocalInstances) := do
  mtracing
  let ⟨depFvs,l1,l2⟩ ← getDeps l1 l2 dirs within pat 0
  dbg_trace s!"[topBackRW] depFvs {repr depFvs}"
  let .mk tmp tnodes l1 l2 ← generalizeTnodesSafeIgnoring l1 l2 within #[]
    (fun x _ _ => return x == pat )
  match tmp with
  | .none =>
      (throwError s!"[topBackRW] generalisation  of tnodes failed in 'within' {← ppExpr within}")
  | .some within => do
      dbg_trace s!"[topBackRW] within {← ppExpr within}"
      dbg_trace s!"[topBackRW] tnodes {← tnodes.mapM ppExpr}"
      let .mk within _ allRev l1 l2 ← revert_NoTn_cutOff_wDepsCache
        introAdmissible? l1 l2 within depFvs.toArray
        depsCache #[] RevCutOff
      dbg_trace s!"[topBackRW] allRev {repr allRev}"
      dbg_trace s!"[topBackRW] within {← ppExpr within}"
      let .mk within proofs l1 l2 ← generalizeProofsIgnoring l1 l2 within #[]
        (fun x _ _ => return x == pat)
        (fun x l1 l2 => do
          let T ← InferType x l1 l2
          return Expr.hasPatternTR pat T)
      dbg_trace s!"[topBackRW] within {← ppExpr within}"
      dbg_trace s!"[topBackRW] proofs {← proofs.mapM ppExpr}"
      let patType ← InferType pat l1 l2
      dbg_trace s!"[topBackRW] patType {← ppExpr patType}"
      let patTypeLevel ← withLCtx l1 l2 <| do getLevel patType
      let motive := Expr.abstractPatBind pat patType within .default
      dbg_trace s!"[topBackRW] motive {← ppExpr motive}"
      let motT ← InferType motive l1 l2
      dbg_trace s!"[topBackRW] motT {← ppExpr motT}"
      let .sort motL := ← Whnf motT.getForallBody l1 l2 | throwError "[topBackRW] motive's type isn't sort headed, it's {← ppExpr motT}"
      let .some (_,_,rep) := (← InferType eqProof l1 l2).eq? | throwError "[topBackRW] eq proof insn't ... it's {← ppExpr eqProof}"
      dbg_trace s!"[topBackRW] rep {← ppExpr rep}"
      dbg_trace s!"[topBackRW] eqProof {eqProof}, of type {← ppExpr (← inferType eqProof)},\nok ? {← isTypeCorrect eqProof}"
      let eqProof ← withLCtx l1 l2 <| do mkAppM `Eq.symm #[eqProof]
      dbg_trace s!"[topBackRW] eqProof {← ppExpr eqProof}, of type {← ppExpr (← inferType eqProof)}"
      let newGoal := (Expr.app motive rep).headBeta
      dbg_trace s!"[topBackRW] newGoal {← ppExpr newGoal}"
      let tn := tnode backIdx pos
      let ⟨_,l1,l2⟩ ← WithLocalDecl tn newGoal l1 l2
      let mainProof := mkAppN (.const `Eq.ndrec [motL,patTypeLevel]) #[patType, rep, motive, .fvar ⟨tn⟩ , pat, eqProof]
      dbg_trace s!"[topBackRW] mainProof {← ppExpr mainProof}, of type {← ppExpr (← inferType mainProof)}"
      let withRevs := mkAppN mainProof (proofs ++ (allRev.map .fvar) ++ tnodes)
      dbg_trace s!"[topBackRW] withRevs {← ppExpr withRevs}, of type {← ppExpr (← inferType withRevs)}"
      return ⟨withRevs,l1,l2⟩

#check 1

@[inline]
def castProofForRW (l1 : LocalContext) (l2 : LocalInstances)
  (pat rep patType eqProof x : Expr) (patTypeLevel : Level) : MetaM Expr :=
  withLCtx l1 l2 <| do
    let xT ← inferType x
    dbg_trace s!"[castProofForRW] xT {← ppExpr xT}"
    let eqMot := Expr.abstractPat pat xT
    let rT := (Expr.app (.lam `castProofForRW patType eqMot .default) rep).headBeta
    dbg_trace s!"[castProofForRW] rT {← ppExpr rT}"
    let eqMot := .lam `castProofForRW patType (mkAppN (.const `Eq [1]) #[.sort 0, xT,eqMot]) .default
    dbg_trace s!"[castProofForRW] eqMot {← ppExpr eqMot}, of type {← ppExpr (← inferType eqMot)}"
    let eqRfl := mkAppN (.const `Eq.refl [1]) #[.sort 0, xT]
    dbg_trace s!"[castProofForRW] eqRfl {← ppExpr eqRfl}, of type {← ppExpr (← inferType eqRfl)}"
    let eqP := mkAppN (.const `Eq.ndrec [0,patTypeLevel]) #[patType,pat,eqMot,eqRfl,rep,eqProof]
    dbg_trace s!"[castProofForRW] eqP {← ppExpr eqP}, of type {← ppExpr (← inferType eqP)}"
    let castMain := mkAppN (.const `cast [0]) #[xT,rT,eqP,x]
    dbg_trace s!"[castProofForRW] castMain {← ppExpr castMain}, of type {← ppExpr (← inferType castMain)}"
    return castMain
    -- assumes `pat` has no abstracted dependecies in the reverted types



#check cast
#check Eq.refl
#check Eq.ndrec

@[specialize]
def topForwRW
  (introAdmissible? : Nat → Bool)
  (depsCache : Array DepCache)
  (RevCutOff : Nat)
  (l1 : LocalContext) (l2 : LocalInstances)
  (dirs : rwDirs) (rwableFvar : Expr) (within pat eqProof : Expr)
  : MetaM (Prod3 Expr LocalContext LocalInstances) := do
  -- trace set Tracing.Flags.none in do
  let ⟨depFvs,l1,l2⟩ ←  getDeps l1 l2 dirs within pat 0
  dbg_trace s!"[topBackRW] depFvs {repr depFvs}"
  let .mk within _ allRev l1 l2 ← revert_NoTn_cutOff_wDepsCache
    introAdmissible? l1 l2 within depFvs.toArray
    depsCache #[] RevCutOff
  dbg_trace s!"[topForwRW] allRev {repr allRev}"
  -- if ← allRev.anyM (fun x => return !(← isProp (← x.getType)))
  -- then
  --   throwError s!"[topForwRW] 'within' contains dependent non-prop fvars: {← ppExpr within}"
  -- else
  dbg_trace s!"[topForwRW] within {← ppExpr within}"
  let .mk within proofs l1 l2 ← generalizeProofsIgnoring l1 l2 within #[]
      (fun x _ _ => return x == pat)
      (fun x l1 l2 => do
        let T ← InferType x l1 l2
        return Expr.hasPatternTR pat T)
  dbg_trace s!"[topForwRW] within {← ppExpr within}"
  dbg_trace s!"[topForwRW] proofs {← proofs.mapM ppExpr}"
  let patType ← InferType pat l1 l2
  dbg_trace s!"[topForwRW] patType {← ppExpr patType}"
  let patTypeLevel ←  withLCtx l1 l2 <| do getLevel patType
  let motive := Expr.abstractPatBind pat patType within .default
  dbg_trace s!"[topForwRW] motive {← ppExpr motive}"
  let motT ← InferType motive l1 l2
  dbg_trace s!"[topForwRW] motT {← ppExpr motT}"
  let .sort motL := ← Whnf motT.getForallBody l1 l2 | throwError "[topForwRW] motive's type isn't sort headed, it's {← ppExpr motT}"
  let .some (_,_,rep) := (← InferType eqProof l1 l2).eq? | throwError "[topForwRW] eq proof insn't ... it's {← ppExpr eqProof}"
  dbg_trace s!"[topForwRW] rep {← ppExpr rep}"
  let mainProof := mkAppN (.const `Eq.ndrec [motL,patTypeLevel]) #[patType, pat, motive, rwableFvar , rep, eqProof]
  dbg_trace s!"[topForwRW] mainProof {← ppExpr mainProof}, of type {← ppExpr (← inferType mainProof)}"
  let castedArgs ← (proofs ++ (allRev.map Expr.fvar)).mapM
    (fun x => castProofForRW l1 l2 pat rep patType eqProof x patTypeLevel)
  let withRevs := mkAppN mainProof castedArgs
  dbg_trace s!"[topForwRW] withRevs {← ppExpr withRevs}, of type {← ppExpr (← inferType withRevs)}"
  return ⟨withRevs,l1,l2⟩


#check funext
-- #exit

#check mkFunExt
/-- We prefer this over `mkFunExt` because the defeq with standard config that i relies on
doesn't have the properties we want. For example in the context of `(n : Nat) (h : ∀ x, n+x = x+n)`,
regular `mkFunExt` will infer `f` to be `HAdd`, instead f making a new fun, as we desire
-/
@[inline]
def mkFunExt!
  (l1 : LocalContext) (l2 : LocalInstances)
  (extHyp : Expr) : MetaM (Prod3 Expr LocalContext LocalInstances) := do
  -- trace set Tracing.Flags.none in do
  let T ← InferType extHyp l1 l2
  let .mk head extArgs l1 l2 ← ForallLetTelescope T 0 l1 l2
  let extArg := extArgs[0]! --should be only one
  let .some (eqT,L,R) := head.eq? | throwError s!"[mkFunExt!] expected eq, got {← ppExpr head}"
  dbg_trace s!"[mkFunExt!] eqT {← ppExpr eqT}, L {← ppExpr L}, R {← ppExpr R}"
  let α ← InferType extArg l1 l2
  let u ← withLCtx l1 l2 <| do  getLevel α
  dbg_trace s!"[mkFunExt!] α {← ppExpr α}, u {u}"
  let β := Expr.abstractPatBind extArg α eqT .default
  dbg_trace s!"[mkFunExt!] β {← ppExpr β}"
  let bT ← InferType β l1 l2
  let .sort v := bT.getForallBody | throwError s!"[mkFunExt!] expected ∀ with sort head, got {← ppExpr β}"
  dbg_trace s!"[mkFunExt!] v {v}"
  let f := Expr.abstractPatBind extArg α L .default
  let g := Expr.abstractPatBind extArg α R .default
  dbg_trace s!"[mkFunExt!] f {← ppExpr f}, g {← ppExpr g}"
  return .mk (mkAppN (.const `funext [u,v]) #[α,β,f,g,extHyp]) l1 l2

#check pi_congr


@[inline]
def mkPiCongr!
  (l1 : LocalContext) (l2 : LocalInstances)
  (extHyp : Expr) : MetaM (Prod3 Expr LocalContext LocalInstances) := do
    let T ← InferType extHyp l1 l2
    let .mk head extArgs l1 l2 ← ForallLetTelescope T 0 l1 l2
    let extArg := extArgs[0]! --should be only one
    let .some (_,L,R) := head.eq? | throwError s!"[mkPiCongr!] expected eq, got {← ppExpr head}"
    let α ← InferType extArg l1 l2
    let u ← withLCtx l1 l2 <| do getLevel α
    let β := Expr.abstractPatBind extArg α L .default
    let β' := Expr.abstractPatBind extArg α R .default
    let bT ← InferType β l1 l2
    let .sort v := bT.getForallBody | throwError s!"[mkPiCongr!] expected ∀ with sort head, got {← ppExpr β}"
    return .mk (mkAppN (.const `pi_congr [u,v]) #[α,β,β',extHyp]) l1 l2

#check let_body_congr

@[inline]
def mkLetBodyCongr!
  (l1 : LocalContext) (l2 : LocalInstances)
  (extHyp : Expr) (letVal : Expr) : MetaM (Prod3 Expr LocalContext LocalInstances) := do
  let T ← InferType extHyp l1 l2
  let .mk head extArgs l1 l2 ← ForallLetTelescope T 0 l1 l2
  let extArg := extArgs[0]! --should be only one
  let .some (eqT,L,R) := head.eq? | throwError s!"[mkLetBodyCongr!] expected eq, got {← ppExpr head}"
  let α ← InferType extArg l1 l2
  let u ← withLCtx l1 l2 <| do getLevel α
  let β := Expr.abstractPatBind extArg α eqT .default
  let bT ← InferType β l1 l2
  let .sort v := bT.getForallBody | throwError s!"[mkLetBodyCongr!] expected ∀ with sort head, got {← ppExpr β}"
  let b := Expr.abstractPatBind extArg α L .default
  let b' := Expr.abstractPatBind extArg α R .default
  let res := mkAppN (.const `let_body_congr [u,v]) #[α,β,b,b',letVal,extHyp]
  return ⟨res,l1,l2⟩


@[inline]
def adaptWorkers (workerDeps : Array (FVarId × (List FVarId))) (term : Expr) : Expr :=
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
partial def handleBinders
  (introAdmissible? : Nat → Bool)
  (depsCache : Array DepCache)
  (RevCutOff : Nat)
  (back? : Bool)
  (l1 : LocalContext) (l2 : LocalInstances)
  (currentDepth : Nat) (nextDepths : List Nat) (workerDeps : Array (FVarId × (List FVarId)))
  (dirs : rwDirs) (within pat eqProof : Expr)
  : MetaM (Prod3 Expr LocalContext LocalInstances) := do
  let rec @[inline] mainAct (k : rwDirs → Expr → Expr → Expr → Expr → Expr → LocalContext → LocalInstances → MetaM (Prod3 Expr LocalContext LocalInstances)) : MetaM (Prod3 Expr LocalContext LocalInstances) := do
    match nextDepths with
    | nextDepth :: furtherDepths =>
        dbg_trace s!"[handleBinders] call on within {← ppExpr within}, pat {← ppExpr pat}, dirs {repr dirs}"
        dbg_trace s!"[handleBinders] currentDepth {currentDepth}, nextDepth { nextDepth}"
        let ⟨boundedTermDirs, boundedTerm, l1,l2⟩ ← getNextBoundedTerm l1 l2 currentDepth nextDepth dirs within
        dbg_trace s!"[handleBinders] boundedTerm {← ppExpr boundedTerm}"
        let ⟨introTerm, introTermDirs, passWorker, workerDeps,l1,l2⟩ ← lambdaLetAllBoundedTelescopeWorkerDirsDeps l1 l2 boundedTerm #[] workerDeps nextDepth (nextDepth+1) boundedTermDirs
        dbg_trace s!"[handleBinders] introTerm {← ppExpr introTerm}, passWorker {← passWorker.mapM ppExpr}"
        --mtrace on .one with s!"[handleBinders] workerDeps {repr <| workerDeps.map (fun x => (x.1, x.2.map LocalDecl.fvarId))}"
        let ⟨res,l1,l2⟩ ← handleBinders introAdmissible? depsCache RevCutOff back? l1 l2 (nextDepth+1) furtherDepths workerDeps introTermDirs introTerm pat eqProof
        dbg_trace s!"[handleBinders] local return {← ppExpr res}"
        let extHyp ← withLCtx l1 l2 <| mkLambdaFVars passWorker res false false false false .default
        dbg_trace s!"[handleBinders] abstracted worker to {← ppExpr extHyp}"
        let ⟨extProof,l1,l2⟩ : (Prod3 Expr LocalContext LocalInstances) := ← do
          match boundedTermDirs with
          | .la .. => mkFunExt! l1 l2 extHyp
          | .al .. => mkPiCongr! l1 l2 extHyp
          | .le .. =>
              match boundedTerm with
              | .letE _ _ V _ _ => mkLetBodyCongr! l1 l2 extHyp V
              | _ => throwError s!"[handleBinders] expected letE, got {← ppExpr boundedTerm}"
          | _ => throwError s!"[handleBinders] expected binder, got {repr boundedTermDirs}"
        if currentDepth == 0
        then
          return ⟨extProof,l1,l2⟩
        else
          let .some (boundedType,_,boundedRep) := (← InferType extProof l1 l2).eq? | throwError s!"[handleBinders] expected eq, got {← ppExpr (← inferType extProof)}"
          dbg_trace s!"[handleBinders] boundedType {← ppExpr boundedType}"
          dbg_trace s!"[handleBinders] boundedRep {← ppExpr boundedRep}"
          let supTermDirs := replaceDirsAtSupPattern dirs within boundedTerm
          dbg_trace s!"[handleBinders] supTermDirs {repr supTermDirs}"
          k supTermDirs within boundedTerm boundedType boundedRep extProof l1 l2
      | [] =>
        if currentDepth == 0
        then
          return ⟨eqProof,l1,l2⟩
        else
          dbg_trace s!"[handleBinders] base case reached"
          --mtrace on .one with s!"[handleBinders] within before {← ppExpr within}"
          let within := adaptWorkers workerDeps within
          --mtrace on .one with s!"[handleBinders] within after {← ppExpr within}"
          --mtrace on .one with s!"[handleBinders] pat before {← ppExpr pat}"
          let pat := adaptWorkers workerDeps pat
          --mtrace on .one with s!"[handleBinders] pat after {← ppExpr pat}"
          --mtrace on .one with s!"[handleBinders] eqProof before {← ppExpr eqProof}"
          let eqProof := adaptWorkers workerDeps eqProof
          --mtrace on .one with s!"[handleBinders] eqProof after {← ppExpr eqProof}"
          let .some (patType,_,rep) := (← InferType eqProof l1 l2).eq? | throwError s!"[handleBinders] expected eq, got {← ppExpr (← inferType eqProof)}"
          k dirs within pat patType rep eqProof l1 l2
  mainAct <| fun supTermDirs within boundedTerm boundedType boundedRep extProof l1 l2 => do
    --mtrace on .two with s!"[handleBinders] in the context of boundedTerm {← ppExpr boundedTerm} and within {← ppExpr within}, supTermDirs {repr supTermDirs}, dirs {repr dirs}"
      let insta := within
      let instaT ← InferType insta l1 l2
      dbg_trace s!"[handleBinders] instaT {← ppExpr instaT}"
      let instaL ← withLCtx l1 l2 <| getLevel instaT
      let ⟨depFvs,l1,l2⟩ ← getDeps l1 l2 supTermDirs within boundedTerm currentDepth
      dbg_trace s!"[handleBinders] depFvs {repr depFvs}"
      if ← depFvs.anyM (fun fv => return !(← IsProp (← fv.getType) l1 l2))
      then
        throwError s!"[handleBinders] we reject non-prop fvars ; there is one in 'within': {← ppExpr within}"
      else
        dbg_trace s!"[handleBinders] depFvs {repr depFvs}"
        let rec @[inline] act (k : Expr → Array Expr → LocalContext → LocalInstances → MetaM (Prod3 Expr LocalContext LocalInstances)) : MetaM (Prod3 Expr LocalContext LocalInstances) := do
          if back?
          then
            let .mk tmp y l1 l2 ← generalizeTnodesSafeIgnoring l1 l2 within
              (workerDeps.map Prod.fst)
              (fun x _ _ => return x == boundedTerm )
            match tmp with
            | .none =>
                (throwError s!"[handleBinders] failed to generalize tnodes (non-prop one ?) in within {← ppExpr within}")
            | .some x => k x y l1 l2
          else
            k within #[] l1 l2
        act <| fun within tnodes l1 l2 => do
          dbg_trace s!"[handleBinders]  within {← ppExpr within}"
          --mtrace on .zero when back? with s!"[handleBinders] tnodes {← tnodes.mapM ppExpr}"
          let .mk within _ allRev l1 l2 ← revert_NoTn_cutOff_wDepsCache
            introAdmissible? l1 l2 within depFvs.toArray
            depsCache workerDeps RevCutOff
            --revert dummy.mvarId! depFvs.toArray l1 l2 workerDeps
          dbg_trace s!"[handleBinders] allRev {repr allRev}"
          if ← allRev.anyM (fun x => return !(← IsProp (← x.getType) l1 l2))
          then
            throwError s!"[handleBinders] 'within' contains dependent non-prop fvars: {← ppExpr within}"
          else
            dbg_trace s!"[handleBinders] within {← ppExpr within}"
            let .mk within proofs l1 l2 ← generalizeProofsIgnoring l1 l2 within
              (workerDeps.map Prod.fst)
              (fun x _ _ => return x == boundedTerm)
              (fun x l1 l2 => do
                let T ← InferType x l1 l2
                return Expr.hasPatternTR boundedTerm T)
            dbg_trace s!"[handleBinders] within {← ppExpr within}"
            dbg_trace s!"[handleBinders] proofs {← proofs.mapM ppExpr}"
            let boundedTypeLevel ← withLCtx l1 l2 <| getLevel boundedType
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
            dbg_trace s!"[handleBinders] eqMot {← ppExpr eqMot}, of type {← ppExpr (← inferType eqMot)}"
            let eqRfl := Expr.app (.lam `handleBinders boundedType eqRfl .default) boundedTerm
            dbg_trace s!"[handleBinders] eqRfl {← ppExpr eqRfl}, of type {← ppExpr (← inferType eqRfl)}"
            let eqP := mkAppN (.const `Eq.ndrec [0,boundedTypeLevel]) #[boundedType,boundedTerm,eqMot,eqRfl,boundedRep,extProof]
            dbg_trace s!"[handleBinders] eqP {← ppExpr eqP}, of type {← ppExpr (← inferType eqP)}"
            -- *Note* we don't filter out unodes since we assume all unodes to be non-prop typed,
            -- so if they were dependecies, we'd have failed already
            let castedArgs ← (proofs ++ (allRev.map Expr.fvar) ++ tnodes).mapM
              (fun x => castProofForRW l1 l2 boundedTerm boundedRep boundedType extProof x boundedTypeLevel)
            let finalProof := mkAppN eqP castedArgs
            dbg_trace s!"[handleBinders] finalProof {← ppExpr finalProof}, of type {← ppExpr (← inferType finalProof)}"
            return ⟨finalProof,l1,l2⟩


#check Eq.refl
#check Eq.ndrec
#check Expr.abstractPat

#check Expr.getWorkerIndsTrans

@[specialize, inline]
def mainBackRW
  (introAdmissible? : Nat → Bool)
  (depsCache : Array DepCache)
  (RevCutOff : Nat)
  (l1 : LocalContext) (l2 : LocalInstances)
  (dirs : rwDirs) (backIdx pos : Nat) (within pat eqProof : Expr)
  (ifSubgoalsThenAllWs : Option Nat)
  : MetaM (Prod3 Expr LocalContext LocalInstances) := do
  dbg_trace s!"[mainBackRW] within {← PpExpr within l1 l2}"
  dbg_trace s!"[mainBackRW] eqProof {← PpExpr eqProof l1 l2}"
  dbg_trace s!"[mainBackRW] pat {← PpExpr pat l1 l2}"
  let Prod3.mk ws l1 l2 ← (do
    match ifSubgoalsThenAllWs with
    | .none =>
      let r1 ← eqProof.getWorkerIndsTrans l1 l2
      let .mk w2 l1 l2 ← pat.getWorkerIndsTrans r1.2 r1.3
      return Prod3.mk (List.orderedUnion r1.1.toList w2.toList) l1 l2
    | .some wLen =>
      return Prod3.mk (List.range wLen) l1 l2
    )
  dbg_trace s!"[mainBackRW] ws {ws}"
  match ws with
  | _ :: _ =>
    let ⟨extProof,l1,l2⟩ ← handleBinders introAdmissible? depsCache RevCutOff true l1 l2 0 ws #[] dirs within pat eqProof
    dbg_trace s!"[mainBackRW] extProof {← PpExpr extProof l1 l2}"
    let .some (_,boundedTerm,_) := (← InferType extProof l1 l2).eq? | throwError s!"[mainBackRW] expected eq, got {← ppExpr (← inferType extProof)}"
    dbg_trace s!"[mainBackRW] boundedTerm {← PpExpr boundedTerm l1 l2}"
    let supTermDirs := replaceDirsAtSupPattern dirs within boundedTerm
    dbg_trace s!"[mainBackRW] supTermDirs {repr supTermDirs}"
    let ⟨term,l1,l2⟩ ← topBackRW introAdmissible? depsCache RevCutOff l1 l2 supTermDirs backIdx pos within boundedTerm extProof
      return ⟨term,l1,l2⟩
  | _ => do
    let ⟨term,l1,l2⟩ ← topBackRW introAdmissible? depsCache RevCutOff l1 l2 dirs backIdx pos within pat eqProof
    return ⟨term,l1,l2⟩

-- #exit

@[specialize, inline]
def mainForwRW
  (introAdmissible? : Nat → Bool)
  (depsCache : Array DepCache)
  (RevCutOff : Nat)
  (l1 : LocalContext) (l2 : LocalInstances)
  (dirs : rwDirs) (rwableFvar : Expr) (within pat eqProof : Expr)
  : MetaM (Prod3 Expr LocalContext LocalInstances) := do
  let .mk w1 l1 l2 ← eqProof.getWorkerIndsTrans l1 l2
  let .mk w2 l1 l2 ← pat.getWorkerIndsTrans l1 l2
  let ws := List.orderedUnion w1.toList w2.toList
  dbg_trace s!"[mainForwRW] eqProof {← ppExpr eqProof}"
  dbg_trace s!"[mainForwRW] pat {← ppExpr pat}"
  dbg_trace s!"[mainForwRW] ws {repr ws}"
  match ws with
  | _ :: _ =>
    let ⟨extProof,l1,l2⟩ ← handleBinders introAdmissible? depsCache RevCutOff false l1 l2 0 ws #[] dirs within pat eqProof
    let .some (_,boundedTerm,_) := (← InferType extProof l1 l2).eq? | throwError s!"[mainForwRW] expected eq, got {← ppExpr (← inferType extProof)}"
    let supTermDirs := replaceDirsAtSupPattern dirs within boundedTerm
    let ⟨term,l1,l2⟩ ← topForwRW introAdmissible? depsCache RevCutOff l1 l2 supTermDirs rwableFvar within boundedTerm extProof
    return ⟨term,l1,l2⟩
  | _ =>
    let ⟨term,l1,l2⟩ ← topForwRW introAdmissible? depsCache RevCutOff l1 l2 dirs rwableFvar within pat eqProof
    return ⟨term,l1,l2⟩

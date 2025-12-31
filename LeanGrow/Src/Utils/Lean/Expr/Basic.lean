

/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import LeanGrowBeta.Utils.Lean.Expr.Subterms
import LeanGrowBeta.Utils.Lean.Expr.Collect
import LeanGrowBeta.Utils.Lean.MetaAPI
import LeanGrowBeta.Utils.Std.List
import LeanGrowBeta.Utils.Lean.Expr.Level


open Lean Meta


-- # Binders

@[inline]
def Lean.Expr.getLamBody : Expr → Expr
| .lam _ _ b _ => b.getLamBody
| e => e

/-- Also handles let-/
@[specialize]
def Lean.Expr.surgeryForall (trafo : Expr → MetaM Expr) : Expr → MetaM Expr
  | .forallE n t b bi => return .forallE n t (← b.surgeryForall trafo) bi
  | .letE n t v b i => return .letE n t v (← b.surgeryForall trafo) i
  | x  => trafo x

/-- Also handles let-/
@[specialize]
def Lean.Expr.surgeryLambda (trafo : Expr → MetaM Expr) : Expr → MetaM Expr
  | .lam n t b bi => return .lam n t (← b.surgeryLambda trafo) bi
  | .letE n t v b i => return .letE n t v (← b.surgeryLambda trafo) i
  | x  => trafo x

/-- Also handles let-/
@[specialize]
def Lean.Expr.surgeryForallWD (trafo : Expr → Nat → MetaM Expr) (d : Nat) : Expr → MetaM Expr
  | .forallE n t b bi => return .forallE n t (← b.surgeryForallWD trafo (d+1)) bi
  | .letE n t v b i => return .letE n t v (← b.surgeryForallWD trafo (d+1)) i
  | x  => trafo x d

/-- Also handles let-/
@[specialize]
def Lean.Expr.surgeryBoundedForallWD (trafo : Expr → Nat → MetaM Expr) (d bound : Nat) (e : Expr) : MetaM Expr := do
  if bound == 0
  then trafo e d
  else
    match e with
    | .forallE n t b bi => return .forallE n t (← b.surgeryBoundedForallWD trafo (d+1) (bound - 1)) bi
    | .letE n t v b i => return .letE n t v (← b.surgeryBoundedForallWD trafo (d+1) (bound - 1)) i
    | x  => trafo x d



/-- Also handles let-/
@[specialize]
def Lean.Expr.surgeryLambdaWD (trafo : Expr → Nat →  MetaM Expr) (d : Nat) : Expr → MetaM Expr
  | .lam n t b bi => return .lam n t (← b.surgeryLambdaWD trafo (d+1)) bi
  | .letE n t v b i => return .letE n t v (← b.surgeryLambdaWD trafo (d+1)) i
  | x  => trafo x d

/-- Also handles let-/
@[specialize]
def Lean.Expr.lambdifyWD (trafo : Expr → Nat →  MetaM Expr) (d : Nat) : Expr → MetaM Expr
  | .forallE n t b bi => return .lam n t (← b.surgeryLambdaWD trafo (d+1)) bi -- shouldnt it be  lambdifyWD ??
  | .letE n t v b i => return .letE n t v (← b.surgeryLambdaWD trafo (d+1)) i
  | x  => trafo x d


/-- Also handles let-/
@[specialize]
def Lean.Expr.surgeryBoundedLambdaWD (trafo : Expr → Nat →  MetaM Expr) (d bound : Nat) (e : Expr) : MetaM Expr :=
  if bound == 0
  then trafo e d
  else
    match e with
    | .lam n t b bi => return .lam n t (← b.surgeryBoundedLambdaWD trafo (d+1) (bound - 1)) bi
    | .letE n t v b i => return .letE n t v (← b.surgeryBoundedLambdaWD trafo (d+1) (bound - 1)) i
    | x  => trafo x d

/-- Also handles let-/
@[specialize]
def Lean.Expr.lambdifyBoundedWD (trafo : Expr → Nat →  MetaM Expr) (d bound : Nat) (e : Expr) : MetaM Expr :=
  if bound == 0
  then trafo e d
  else
    match e with
    | .forallE n t b bi => return .lam n t (← b.lambdifyBoundedWD trafo (d+1) (bound - 1)) bi
    | .letE n t v b i => return .letE n t v (← b.lambdifyBoundedWD trafo (d+1) (bound - 1)) i
    | x  => trafo x d



private partial def forallMetaTagTelescopeReducingAux
  (tag : String) (lctx : LocalContext) (lins : LocalInstances)
  (e : Expr) (reducing : Bool) (maxMVars? : Option Nat) (kind : MetavarKind) : MetaM (Array Expr × Array BinderInfo × Expr) :=
  process #[] #[] 0 e
where
  process (mvars : Array Expr) (bis : Array BinderInfo) (j : Nat) (type : Expr) : MetaM (Array Expr × Array BinderInfo × Expr) := do
    if maxMVars?.isEqSome mvars.size then
      let type := type.instantiateRevRange j mvars.size mvars;
      return (mvars, bis, type)
    else
      match type with
      | .forallE n d b bi =>
        let d  := d.instantiateRevRange j mvars.size mvars
        let k  := if bi.isInstImplicit then  MetavarKind.synthetic else kind
        let mvar ← mkFreshExprMVarTag tag d lctx lins k n
        let mvars := mvars.push mvar
        let bis   := bis.push bi
        process mvars bis j b
      | _ =>
        let type := type.instantiateRevRange j mvars.size mvars;
        if reducing then do
          let newType ← Whnf type lctx lins
          if newType.isForall then
            process mvars bis mvars.size newType
          else
            return (mvars, bis, type)
        else
          return (mvars, bis, type)

/-- Given `e` of the form `forall ..xs, A`, this combinator will create a new
  metavariable for each `x` in `xs` and instantiate `A` with these.
  Returns a product containing
  - the new metavariables
  - the binder info for the `xs`
  - the instantiated `A`
-/
@[inline]
def forallMetaTagTelescope (lctx : LocalContext) (lins : LocalInstances) (tag : String) (e : Expr) (kind := MetavarKind.natural) : MetaM (Array Expr × Array BinderInfo × Expr) :=
  forallMetaTagTelescopeReducingAux tag lctx lins e (reducing := false) (maxMVars? := none) kind



partial def forallLetTelescope (l1 : LocalContext) (l2 : LocalInstances)
  (type : Expr) (sofarFvs : Array Expr)
  : MetaM (Prod4 Expr (Array Expr) LocalContext LocalInstances) := do
  match type with
  | .forallE n t b _ =>
      let ⟨nfv,b,l1,l2⟩ ← withFreeing n t b l1 l2
      forallLetTelescope l1 l2 b (sofarFvs.push (.fvar nfv))
  | .letE n t v b _ =>
      let ⟨nfv,b,l1,l2⟩ ← withFreeingLet n t v b l1 l2
      forallLetTelescope l1 l2 b (sofarFvs.push (.fvar nfv))
  | _ => return ⟨type,sofarFvs,l1,l2⟩


partial def Lean.Expr.zeta : Expr → Expr
  | .letE _ _ V B _ => (Expr.instantiate1 B V).zeta
  | x => x

@[inline]
def Lean.Expr.zetaFvs (within : Expr)
  (initD : LocalContext) (initI : LocalInstances) : MetaM Expr := do
  return (← within.onAllSubtermsMTR initD initI (fun
      | x@(.fvar fv), l1, l2 => do
          let dec ← fv.GetDecl l1 l2
          match dec with
          | .cdecl .. => return ⟨x,l1,l2⟩
          | .ldecl _ _ _ _ v .. => return ⟨v,l1,l2⟩
      | x,y,z => return ⟨x,y,z⟩)).1


-- # Abstract pattern

@[inline]
def Lean.Expr.abstractPat (pat within : Expr) : Expr :=
  within.onAllSubtermsWiDepth (fun x d =>
    if x == pat
    then
      .bvar d
    else
      match x with
      | .bvar i => if i ≥ d then .bvar (i+1) else x
      | _ => x)


@[inline]
def Lean.Expr.abstractPatBind (pat patType within : Expr) : Expr :=
  let absd := Expr.abstractPat pat within
  .lam `abstractPat.dummy patType absd .default



/--
- Expect fvars to be in context
- λ is in same order as `fvs`-/
@[specialize]
partial def Lean.Expr.abstractLetFvarWrt
  (initD : LocalContext) (initI : LocalInstances)
  (fvs : Array FVarId) (e : Expr)
  : MetaM (Prod3 Expr LocalContext LocalInstances) :=
    let rec bind (term : Expr) (i : Nat) : MetaM Expr := do
      -- **Bug potential** appearances in type `T` won't get abstracted
      match ← (fvs[i]!).GetDecl initD initI with
      | .cdecl _ _ _ T .. =>
          if i == 0
          then
            return .lam `abstractFvarWrt T term .default
          else
            bind (.lam `abstractFvarWrt T term .default) (i-1)
      | .ldecl _ _ _ T V nonDep .. =>
          if i == 0
          then
            return .letE `abstractFvarWrt T V term nonDep
          else
            bind (.letE `abstractFvarWrt T V term nonDep) (i-1)
    do
    let fvS := fvs.size
    if fvS == 0
    then return ⟨e,initD,initI⟩
    else
      let ⟨absd,initD,initI⟩ ← e.onAllSubtermsWiWorker initD initI (fun x d initD initI =>
        match x with
        | .fvar id =>
          match fvs.findIdx? (fun y => y == id) with
          | .none => return ⟨x,initD,initI⟩
          | .some i => return ⟨(.bvar (d + fvS - 1 - i)),initD,initI⟩
        | _ => return ⟨x,initD,initI⟩ )
      let res ← bind absd (fvs.size - 1)
      return ⟨res,initD,initI⟩


/--
- Expect fvars to be in context
- ∀ is in same order as `fvs`-/
@[specialize]
partial def Lean.Expr.abstractLetFvarAsAllWrt
  (initD : LocalContext) (initI : LocalInstances)
  (fvs : Array FVarId) (e : Expr)
  : MetaM (Prod3 Expr LocalContext LocalInstances) :=
    let rec bind (term : Expr) (i : Nat) : MetaM Expr := do
      match ← (fvs[i]!).GetDecl initD initI with
      | .cdecl _ _ _ T .. =>
          if i == 0
          then
            let term := Expr.abstractPat (.fvar fvs[i]!) term
            return .forallE `abstractFvarWrt T term .default
          else
            let term := Expr.abstractPat (.fvar fvs[i]!) term
            bind (.forallE `abstractFvarWrt T term .default) (i-1)
      | .ldecl _ _ _ T V nonDep .. =>
          if i == 0
          then
            let term := Expr.abstractPat (.fvar fvs[i]!) term
            return .letE `abstractFvarWrt T V term nonDep
          else
            let term := Expr.abstractPat (.fvar fvs[i]!) term
            bind (.letE `abstractFvarWrt T V term nonDep) (i-1)
    do
    let fvS := fvs.size
    if fvS == 0
    then return ⟨e,initD,initI⟩
    else
      let res ← bind e (fvs.size - 1)
      return ⟨res,initD,initI⟩

#check Expr.abstract
#check Expr.abstractPat



@[inline, specialize]
partial def Lean.Expr.instantiateLooseBvar (fvs : List FVarId) (e : Expr) : Expr :=
    e.onAllSubtermsWiDepth (fun x d =>
        match x with
        | .bvar i =>
            if  i ≥ d
            then
              let fid := fvs[i - d]!
              (.fvar fid)
            else
              x
        | _ => x )


-- # Check pattern

@[inline]
def Lean.Expr.hasPatternTR (pat within : Expr) : Bool :=
  within.onAllSubtermsCheckExistsTR (fun x => x == pat)

@[inline]
def Lean.Expr.hasWorkerTR (within : Expr) : Bool :=
  within.onAllSubtermsCheckExistsTR (fun | .fvar x => x.isWorker | _ => false)

@[inline]
def Lean.Expr.hasWorkerExcpet (exe : List FVarId) (within : Expr) : Bool :=
  within.onAllSubtermsCheckExistsTR (fun | .fvar x => if x.isWorker then !(exe.contains x) else false | _ => false)


@[inline]
def Lean.Expr.hasTnodes (within : Expr) : Bool :=
  within.onAllSubtermsCheckExistsTR (fun
    | .fvar ⟨(.num (.num ..) ..)⟩ => true
    | .sort u => u.hasTnodes
    | .const _ lvls => lvls.any Level.hasTnodes
    | _ => false)


@[inline]
def Lean.Expr.hasLnodes (within : Expr) : Bool :=
  within.onAllSubtermsCheckExistsTR (fun | .mvar ⟨(.num (.num ..) ..)⟩ => true | _ => false)



-- # Collect

@[inline]
def Lean.Expr.getFVars (e : Expr) : List Expr :=
  e.onAllSubtermsFold []
    (fun x sofar =>
      match x with
      | .fvar .. => sofar.insert x
      | _ => sofar
      )

@[inline]
def Lean.Expr.getFVarIds (e : Expr) : List FVarId :=
  e.onAllSubtermsFold []
    (fun x sofar =>
      match x with
      | .fvar id => sofar.insert id
      | _ => sofar
      )

@[inline]
def Lean.Expr.getDeepestWorker (proof : Expr) : Option Nat :=
  proof.onAllSubtermsFold .none (fun e st =>
    match e with
    | .fvar ⟨.num (.str _ k) d⟩ =>
        if k == "w"
        then
          match st with
          | .none => .some d
          | .some x =>
              if d > x
              then .some d
              else st
        else st
    | _ => st
    )


@[inline]
def Lean.Expr.getWorkerInds (proof : Expr) : List Nat :=
  proof.onAllSubtermsFold [] (fun e st =>
    match e with
    | .fvar ⟨.num (.str _ k) d⟩ =>
        if k == "w"
        then st.orderedInsertOrLeave d
        else st
    | _ => st
    )

@[inline]
def Lean.Expr.getWorkerIndsTrans (l1 : LocalContext) (l2 : LocalInstances) (proof : Expr) : MetaM (List Nat) := do
  let ⟨res,_,_⟩ ← proof.onAllSubtermsFoldEnqueueM l1 l2 [] (fun e D ws l1 l2 st =>
    match e with
    | .fvar fv@⟨W@(.num (.str _ k) d)⟩ => do
        if k == "w"
        then
          if (ws.find? W.toString.toUTF8).isNone
          then
            let st := st.orderedInsertOrLeave d
            let T ← fv.GetType l1 l2
            if T.hasFVar
            then
              return ⟨.enq st D T,l1,l2⟩
            else
              return ⟨.std st,l1,l2⟩
          else
            return ⟨.std st,l1,l2⟩
        else return ⟨.std st,l1,l2⟩
    | _ => return ⟨.std st,l1,l2⟩
    )
  return res

#print FoldEnqueueT

@[inline]
def Lean.Expr.getGUFVarsIds (e : Expr) : List FVarId :=
  e.onAllSubtermsFold []
    (fun x sofar =>
      match x with
      | .fvar y@⟨.num k _⟩ =>
        if k == `u || k == `g
        then sofar.insert y
        else sofar
      | _ => sofar
      )

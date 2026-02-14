

/-
Copyright (c) 2026 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/



import LeanGrow.Src.Utils.Lean.Expr.Basic
import LeanGrow.Src.SampleGenScore.Delab
import LeanGrow.Src.Utils.Lean.Blacklisting

open Lean Meta


def deltaZetaBeta? (l1 : LocalContext) (l2 : LocalInstances)
  (depthStop : Nat) (deltaFuzz zetaFuzz : Option Nat)
  (e : Expr) : MetaM (OptionProd3 Nat Expr (Option FVarId)) := do
  match deltaFuzz, zetaFuzz with
  | .some deltafuel, .some zetafuel =>
      match e with
      | .app .. =>
          match e.getAppFn' with
          | .const h _ =>
              if h.blackListSampleDelta
              then return .none
              else
                match (← getEnv).find? h with
                | .some (.thmInfo I) =>
                  let prf := I.value
                  let as := e.getAppArgs
                  let final := (mkAppN prf as).headBetaLet
                  return .some (depthStop - deltafuel) final .none
                | _ => return .none
          | .fvar fvid =>
              let dec ← fvid.GetDecl l1 l2
              match dec with
              | .ldecl _ _ _ type val .. =>
                if ← IsProp type l1 l2
                then
                  let as := e.getAppArgs
                  let val := (mkAppN val as).headBetaLet
                  return .some (depthStop - zetafuel) val fvid
                else return .none
              | _ => return .none
          | _ => return .none
      | .fvar fvid =>
          let dec ← fvid.GetDecl l1 l2
          match dec with
          | .ldecl _ _ _ type val .. =>
            if ← IsProp type l1 l2
            then
              return .some (depthStop - zetafuel) val fvid
            else return .none
          | _ => return .none
      | _ => return .none
  | .some deltafuel, .none =>
      match e with
      | .app .. =>
          match e.getAppFn' with
          | .const h _ =>
              if h.blackListSampleDelta
              then return .none
              else
                match (← getEnv).find? h with
                | .some (.thmInfo I) =>
                  let prf := I.value
                  let as := e.getAppArgs
                  let final := (mkAppN prf as).headBetaLet
                  return .some (depthStop - deltafuel) final .none
                | _ => return .none
          | _ => return .none
      | _ => return .none
  | .none, .some zetafuel =>
      match e with
      | .app .. =>
          match e.getAppFn' with
          | .fvar fvid =>
              let dec ← fvid.GetDecl l1 l2
              match dec with
              | .ldecl _ _ _ type val .. =>
                if ← IsProp type l1 l2
                then
                  let as := e.getAppArgs
                  let val := (mkAppN val as).headBetaLet
                  return .some (depthStop - zetafuel) val fvid
                else return .none
              | _ => return .none
          | _ => return .none
      | .fvar fvid =>
          let dec ← fvid.GetDecl l1 l2
          match dec with
          | .ldecl _ _ _ type val .. =>
            if ← IsProp type l1 l2
            then
              return .some (depthStop - zetafuel) val fvid
            else return .none
          | _ => return .none
      | _ => return .none
  | .none, .none => return .none

#check 1

-- #exit

/--
*Bug potential*
- when we zetaFuzz, we get rid of the have-fvar, since we continue delab-ing its proof,
  but it may be present multiple times on the proof term, and when we get rid of fvars
  when making the final hyps to be stored, this will be dismissed ...
-/
partial def sampleHypsCore
  (preProcessed : CTrie SimpCongrTheorem)
  (l1 : LocalContext) (l2 : LocalInstances)
  (depthStart depthStop : Nat) (e : Expr)
  (digLifted : List FVarId) (deltaFuzz zetaFuzz : Option Nat)
  : MetaM (Prod3 (ListProd (List FVarId) (List SubProof)) LocalContext LocalInstances) := do
  mtracing
  let rec inner (l1 : LocalContext) (l2 : LocalInstances) (d : Nat) (Lifted : List FVarId)
      (sh : ListProd Nat SubProof) (todo : ListProd4 Nat Nat (List FVarId) (ListProd Nat SubProof)) (L : ListProd Nat SubProof) (count : Nat)
    : MetaM (Prod3 (ListProd4 Nat Nat (List FVarId) (ListProd Nat SubProof)) LocalContext LocalInstances) :=
    match L with
    | .nil => return .mk todo l1 l2
    | .cons hdepth h hs => do
        match h with
        | H@(.irreducible h) =>
          mtrace on .zero with s!" inner at hdepth {hdepth} ireducible h {← ppExpr h}"
          inner l1 l2 d Lifted (.cons hdepth H sh) todo hs (count+1)
        | H@(.raw h) =>
          mtrace on .zero with s!" inner at hdepth {hdepth} raw h {← ppExpr h}"
          let .mk lifted subp delZet l1 l2 ← delabSample preProcessed h l1 l2
          match subp with
          | [] =>
              -- ignore lifted ...
              mtrace on .zero with s!" delaborated to empty, marking irreducible"
              match delZet with
              | .some delZet =>
                match ← deltaZetaBeta? l1 l2 depthStop deltaFuzz zetaFuzz delZet with
                | .some pdd E fv? =>
                  let dd := max hdepth pdd
                  let para := .cons dd (.raw E) (sh.foldl hs .cons)
                  let Lifted' := (match fv? with | .none => Lifted | .some fv => Lifted.erase fv)
                  inner l1 l2 d Lifted (.cons hdepth (.irreducible h) sh) (.cons (max dd d) count Lifted' para todo) hs (count+1)
                | _ =>
                  inner l1 l2 d Lifted (.cons hdepth (.irreducible h) sh) todo hs (count+1)
              | _ =>
                inner l1 l2 d Lifted (.cons hdepth (.irreducible h) sh) todo hs (count+1)
          | _ =>
              mtrace on .zero with s!" delaborated to {← subp.mapM (fun x => x.pp l1 l2)}"
              let nx := ((subp.foldl (fun a b => ListProd.cons (hdepth + 1) b a) sh).foldl hs .cons)
              match delZet with
              | .some delZet =>
                match ← deltaZetaBeta? l1 l2 depthStop deltaFuzz zetaFuzz delZet with
                | .some pdd E fv? =>
                  let dd := max hdepth pdd
                  let para := .cons dd (.raw E) (sh.foldl hs .cons)
                  let Lifted' := (match fv? with | .none => Lifted | .some fv => Lifted.erase fv)
                  let todo := (.cons (max dd d) count Lifted' para todo)
                  inner l1 l2 d Lifted (.cons hdepth H sh) (.cons (if hdepth + 1 > d then hdepth + 1 else d) count (lifted ++ Lifted) nx todo) hs (count+1)
                | _ =>
                  inner l1 l2 d Lifted (.cons hdepth H sh) (.cons (if hdepth + 1 > d then hdepth + 1 else d) count (lifted ++ Lifted) nx todo) hs (count+1)
              | _ =>
                  inner l1 l2 d Lifted (.cons hdepth H sh) (.cons (if hdepth + 1 > d then hdepth + 1 else d) count (lifted ++ Lifted) nx todo) hs (count+1)
        | H@(.simp simpSteps nonTerminal usedFv) =>
          mtrace on .zero with s!" inner at hdepth {hdepth} simp {← H.pp l1 l2}"
          match simpSteps with
          | .cons _ _ _ more =>
            let nx := (ListProd.cons (hdepth + 1) (.simp more nonTerminal usedFv)  sh).foldl hs .cons
            inner l1 l2 d Lifted (.cons hdepth H sh) (.cons (if hdepth + 1 > d then hdepth + 1 else d) count  Lifted nx todo) hs (count+1)
          | .nil =>
            match nonTerminal with
            | .none => -- proceed
                inner l1 l2 d Lifted (.cons hdepth H sh) todo hs (count+1)
            | .some nx => -- restart ìnner`
                inner l1 l2 d Lifted hs todo (.cons hdepth (.raw nx) hs) count
  let rec go (l1 : LocalContext) (l2 : LocalInstances) (done : ListProd (List FVarId) (List SubProof))
    (L : ListProd4 Nat Nat (List FVarId) (ListProd Nat SubProof))
    : MetaM (Prod3 (ListProd (List FVarId) (List SubProof)) LocalContext LocalInstances) :=
    match L with
    | .nil => return .mk done l1 l2
    | .cons maxdepth gen lifted hyps more => do
        /- Idea: gen instructs how many h's in hyps to skip.
        The invariant is (proof?) that all expantions on a h with position prior to gen
        have already been made, so it only remains to do those where it remained unexpanded
        ...
        `hyps` now contains the hyp depth, while `depth` maintains the maximum depth
        over the hyps, and we only add to done whne the maximum is larg enough
        -/
        mtrace on .zero with s!" go on hyps {← hyps.toListOfProd.mapM (fun x => x.2.pp l1 l2)}"
        if maxdepth >= depthStop
        then
          mtrace on .zero with s!" out of depth, storing"
          go l1 l2 (.cons lifted (hyps.foldl [] (fun _ x l =>
            match x with
            | .raw (.fvar ..) | .irreducible (.fvar ..) => l
            | _ => x :: l
            )) done) more
        else
          let rec skip (sh : ListProd Nat SubProof) : Nat → ListProd Nat SubProof → (ListProd Nat SubProof) × (ListProd Nat SubProof)
            | x+1, .cons yn y ys => skip (.cons yn y sh) x ys
            | 0, hs => (sh,hs)
            | _, _ => panic " skip"
          let (sh, hs) := skip .nil gen hyps
          let .mk next l1 l2 ← inner l1 l2 maxdepth lifted sh more hs gen
          mtrace on .zero with s!" depth {maxdepth} depthStart {depthStart}"
          let ntodo :=
            if maxdepth ≥ depthStart
            then
              let (hs, mind) := (hyps.foldl ([],maxdepth) (fun d x (l,md) =>
                match x with
                | .raw (.fvar ..) | .irreducible (.fvar ..) => (l,md) -- expected in lifted
                | _ => (x :: l, if d < md then d else md)))
              if mind ≥ depthStart
              then .cons lifted hs done
              else done
            else done
          go l1 l2 ntodo next
  go l1 l2 .nil (.cons 0 0 digLifted (.cons 0 (.raw e) .nil) .nil)



#check 1



partial def digExpr
  (preProcessed : CTrie SimpCongrTheorem)
  (l1 : LocalContext) (l2 : LocalInstances)
  (depth : Nat) (e : SubProof) (todo : ListProd SubProof (List FVarId)) (initLifted : List FVarId)
  : MetaM (Prod4 (ListProd SubProof (List FVarId)) (ListProd3 Expr Expr (List Expr)) LocalContext LocalInstances) := do
  mtracing
  let rec inner (l1 : LocalContext) (l2 : LocalInstances)
    (d : Nat) (todo : ListProd3 Nat SubProof (List FVarId)) (h : SubProof) (Lifted : List FVarId)
    (haves : List SubProof) (havePatters : ListProd3 Expr Expr (List Expr))
    : MetaM (Prod5 (ListProd3 Nat SubProof (List FVarId)) (List SubProof) (ListProd3 Expr Expr (List Expr)) LocalContext LocalInstances) := do
    mtrace on .zero with s!"[digExprTask] inner on {← h.pp l1 l2}\nLifted : {repr Lifted}"
    match h with
    | .raw h | .irreducible h =>
      match h with
      | .mdata _ h => inner l1 l2 d todo (.raw h) Lifted haves havePatters
      | .lam name type body _ =>
          let desambig ← mkFreshId
          let .mk nfv l1 l2 ← WithLocalDecl (name ++ desambig) type l1 l2
          let h := Expr.instantiate1 body (.fvar nfv)
          inner l1 l2 d todo (.raw h) (nfv :: Lifted) haves havePatters
      | _ => do
          mtrace on .zero with s!" calling delabDig on {← ppExpr h}"
          let .mk haveT? lifted res lhaves l1 l2 ← delabDig preProcessed h l1 l2
          match haveT? with
          | .none =>
              let Lifted := (lifted ++ Lifted)
              return .mk (res.foldl (fun l x => l.cons (d-1) x Lifted) todo) (lhaves.foldl (fun x y => y :: x) haves) havePatters l1 l2
          | .some haveT =>
              let body :=
                match res with
                | (.raw B) :: _ => B
                | _ => panic! "[digExpr] Akwaaard"
              let usedFv := h.getFVarIds
              let locLifted := Lifted.filter (fun x => usedFv.contains x)
              let presinks ← locLifted.mapM (fun fv => do
                let T ← fv.GetType l1 l2
                let T ← WhnfR T l1 l2
                return (fv,T))
              let presinks ← presinks.foldlM (fun S (_,T) => do
                let nonSink := T.getFVarIds
                return S.filter (fun (x,_) => !(nonSink.contains x))
                ) presinks
              let hyps := presinks.mapTRR Prod.snd
              let goal ← InferType body l1 l2
              let Lifted := (lifted ++ Lifted)
              mtrace on .zero with s!" adding to havePattern {← ppExpr haveT}\nwith goal {← ppExpr goal}\nand hyps {← hyps.mapM ppExpr}"
              let havePatters := .cons haveT goal hyps havePatters
              return .mk (res.foldl (fun l x => l.cons (d-1) x Lifted) todo) (lhaves.foldl (fun x y => y :: x) haves) havePatters l1 l2
    | .simp simpSteps nonTerminal usedFv =>
        mtrace on .zero with s!" simp {← h.pp l1 l2}"
        match simpSteps with
        | .cons _ _ _ more =>
          return .mk (todo.cons (d-1) (.simp more nonTerminal usedFv) Lifted) haves havePatters l1 l2
        | .nil =>
          match nonTerminal with
          | .none =>
              return .mk todo haves havePatters l1 l2
          | .some nx =>
              return .mk (todo.cons (d-1) (.raw nx) Lifted) haves havePatters l1 l2
  let rec go (l1 : LocalContext) (l2 : LocalInstances) (havePatters : ListProd3 Expr Expr (List Expr))
    (done : ListProd SubProof (List FVarId)) (L : ListProd3 Nat SubProof (List FVarId))
    : MetaM (Prod4 (ListProd SubProof (List FVarId)) (ListProd3 Expr Expr (List Expr)) LocalContext LocalInstances) := do
    match L with
    | .nil => return .mk done havePatters l1 l2
    | .cons fuel hyp lifted more => do
        mtrace on .zero with s!"[digExprTask] on {← hyp.pp l1 l2}"
        if fuel == 0
        then
          mtrace on .zero with s!"[digExprTask] out of fuel, adding"
          go l1 l2 havePatters (.cons hyp lifted done) more
        else
          let .mk next haves havePatters l1 l2 ← inner l1 l2 fuel more hyp lifted [] havePatters
          let done := haves.foldl (fun l x => l.cons x lifted) done
          go l1 l2 havePatters done next
  go l1 l2 .nil todo (.cons depth e initLifted .nil)


#check 1
-- #exit


@[inline]
def LambdaOnlyTelescope (e : Expr) (initD : LocalContext) (initI : LocalInstances)
    : MetaM (Prod4 Expr (Array Expr) LocalContext LocalInstances) := do
  process initD initI #[] e
where
  process (initD : LocalContext) (initI : LocalInstances) (fvars : Array Expr) (e : Expr)
    : MetaM (Prod4 Expr (Array Expr) LocalContext LocalInstances) := do
      match e with
      | .lam n d b bi =>
          let d := d.instantiateRevRange 0 fvars.size fvars
          let d := d.cleanupAnnotations
          match bi with
          | .instImplicit =>
              let ⟨fvarId, initD,initI⟩ ← WithLocalDeclU n d initD initI
              let fvar := mkFVar fvarId
              process initD initI (fvars.push fvar) b
          | _ =>
              let (fvarId, initD) ← withNonInstLocalDeclU n d initD
              let fvar := mkFVar fvarId
              process initD initI (fvars.push fvar) b
      | _ =>
          let e := e.instantiateRevRange 0 fvars.size fvars
          return ⟨e, fvars, initD, initI⟩


#check 1


def Lean.Expr.isRefl? (e : Expr) : Bool := Id.run <| do
  let h := e.getAppFn'
  let .const h _ := h | return false
  return (h == ``Eq.refl || h == ``Iff.refl || h == ``Iff.rfl || h == ``rfl)

#check 1
#check rfl

def postCleanReject (l1 : LocalContext) (l2 : LocalInstances) (T : Expr) : MetaM (Option Expr) := do
  if ← IsProp T l1 l2
  then
    match T with
    | .forallE _ (.const u? _) b _ =>
      if u? == ``Unit || u? == ``PUnit
      then
        if b.hasLooseBVars
        then return .some T
        else return .some b
      else
        return .some T
    | _ => return .some T
  else
    return .none

#check Expr.getFVarIds'
#check Name.isPrefixOf
#print SampleData

def Lean.Name.getPrefix! : Name → String
  | anonymous => "anonymous"
  | str .anonymous p => p
  | num p _   => p.getPrefix!
  | str p _   => p.getPrefix!




partial def sampleCoreBack
  (preProcessed : CTrie SimpCongrTheorem) (conjable : CTrie (List Nat))
  (l1 : LocalContext) (l2 : LocalInstances)
  (depthDig depthStart depthStop : Nat) (deltaFuzz zetaFuzz : Option Nat) (todo : ListProd SubProof (List FVarId))
  (samples : ListProd4 SampleData (List FVarId) Expr (List Expr)) (havePats : ListProd3 Expr Expr (List Expr))
  : MetaM (Prod4 (ListProd4 SampleData (List FVarId) Expr (List Expr)) (ListProd3 Expr Expr (List Expr)) LocalContext LocalInstances) := do
  mtracing
  match todo with
  | .cons e lifted todo => do
      mtrace on .zero with s!" looking at sample:\nterm : {← e.pp l1 l2}"
      match e with
      | .raw e | .irreducible e =>
        -- ↑ irreducible is no mistake : induction should yield empty delabSample, but will yield non empty delabDig
        let .mk e fvs l1 l2 ← LambdaOnlyTelescope e l1 l2
        mtrace on .zero with s!" possibly introed to:\nterm : {← ppExpr e}"
        -- Note : here and in all other sampling fuctions : shouldn't ever synthesise instances,
        -- because local instance don't get cleaned ...
        let lifted := (fvs.foldl (fun x y => x.cons y.fvarId!) lifted)
        let .mk todo haveP l1 l2 ← digExpr preProcessed l1 l2 depthDig (.raw e) todo lifted
        let .mk postLift r l1 l2 ← delabTopBack preProcessed conjable e l1 l2 []
        let lifted := postLift ++ lifted
        match r with
        | .none =>
            sampleCoreBack preProcessed conjable l1 l2 depthDig depthStart depthStop deltaFuzz zetaFuzz todo samples (haveP.foldl havePats ListProd3.cons)
        | .thm  sn | .thmC sn .. =>
          if sn.getPrefix! == "_private"
          then
            sampleCoreBack preProcessed conjable l1 l2 depthDig depthStart depthStop deltaFuzz zetaFuzz todo samples (haveP.foldl havePats ListProd3.cons)
          else
            let .mk hyps l1 l2 ← sampleHypsCore preProcessed l1 l2 depthStart depthStop e lifted deltaFuzz zetaFuzz
            let goal ← InferType e l1 l2
            let goal ← WhnfR goal l1 l2
            let usedFv := e.getFVarIds
            mtrace on .zero with s!" goal {← ppExpr goal}"
            match hyps with
            | .nil =>
              let lifted := lifted.filter (fun x => usedFv.contains x)
              -- let presinks ← withLCtx l1 l2 <| lifted.foldlM (fun L fv => do
              --   let T ← fv.getType
              --   let T ← (do match ← isClass? T with | .none => whnfR T | _ => return T)
              --   match ← postCleanReject l1 l2 T with
              --   | .none => return L
              --   | .some T => return (fv,T) :: L
              --   ) []
              -- let presinks ← presinks.foldlM (fun S (_,T) => do
              --   let nonSink := T.getFVarIds
              --   return S.filter (fun (x,_) => !(nonSink.contains x))
              --   ) presinks
              -- let hyps := presinks.map Prod.snd
              let hyps ← withLCtx l1 l2 <| lifted.foldlM (fun L fv => do
                let T ← fv.getType
                let T ← (do match ← isClass? T with | .none => whnfR T | _ => return T)
                match ← postCleanReject l1 l2 T with
                | .none => return L
                | .some T => return T :: L
                ) []
              mtrace on .zero with s!" hyps {← hyps.mapM ppExpr}"
              sampleCoreBack preProcessed conjable l1 l2 depthDig depthStart depthStop deltaFuzz zetaFuzz todo (.cons r lifted goal hyps samples) (haveP.foldl havePats ListProd3.cons)
            | _ =>
              let samples ← withLCtx l1 l2 <| hyps.foldlM samples (fun locLifted hs R => do
                let superseeded := hs.foldl (fun U h =>
                  match h with
                  | .raw h | .irreducible h => h.getFVarIds' U
                  | .simp _ _ us => us.foldl (fun x y => x.insert y) U
                  ) []
                let locLifted := locLifted.filter (fun x => usedFv.contains x && !(superseeded.contains x))
                -- ugly, and should be fixed by having sampleHypsCore be run on empty lifted ??
                -- point is, when hyps was non-empty, we don't want binder hyps ...
                -- let presinks ← locLifted.foldlM (fun L fv => do
                --   let T ← fv.getType
                --   let T ← (do match ← isClass? T with | .none => whnfR T | _ => return T)
                --   match ← postCleanReject l1 l2 T with
                --   | .none => return L
                --   | .some T => return (fv,T) :: L
                --   ) []
                -- let presinks ← presinks.foldlM (fun S (_,T) => do
                --   let nonSink := T.getFVarIds
                --   return S.filter (fun (x,_) => !(nonSink.contains x))
                --   ) presinks
                let presinks ← locLifted.foldlM (fun L fv => do
                  let T ← fv.getType
                  let T ← (do match ← isClass? T with | .none => whnfR T | _ => return T)
                  match ← postCleanReject l1 l2 T with
                  | .none => return L
                  | .some T => return T :: L
                  ) []
                let hyps ← hs.foldlM (fun H h => do
                  match h with
                  | .raw h | .irreducible h =>
                    if h.isRefl?
                    then return H
                    else
                      let T ← inferType h
                      let T ← whnfR T
                      match ← postCleanReject l1 l2 T with
                      | .none => return H
                      | .some T => return T :: H
                  | .simp simpSteps nonTerminal _ =>
                    match simpSteps with
                    | .nil =>
                      match nonTerminal with
                      | .none => return H
                      | .some nonTerminal =>
                          let T ← inferType nonTerminal
                          let T ← whnfR T
                          match ← postCleanReject l1 l2 T with
                          | .none => return H
                          | .some T => return T :: H
                    | .cons _ T _ _ =>
                      let T ← whnfR (cleanBetaTopType T)
                      return T :: H
                  ) presinks -- []
                -- let hyps ← presinks.foldlM (fun S (fv,fvT) => do
                --   let nonSink := hyps.any (fun HT => HT.onAllSubtermsCheckExistsTR (fun | .fvar id => fv == id | _ => false))
                --   if nonSink then return S else return  fvT :: S
                --   ) hyps
                mtrace on .zero with s!" hyps {← hyps.mapM ppExpr}"
                return .cons r locLifted goal hyps R)
              sampleCoreBack preProcessed conjable l1 l2 depthDig depthStart depthStop deltaFuzz zetaFuzz todo samples (haveP.foldl havePats ListProd3.cons)
        | .induc sn =>
          if sn.getPrefix! == "_private"
          then
            sampleCoreBack preProcessed conjable l1 l2 depthDig depthStart depthStop deltaFuzz zetaFuzz todo samples (haveP.foldl havePats ListProd3.cons)
          else
            let goal ← InferType e l1 l2
            let usedFv := e.getFVarIds
            let lifted := lifted.filter (fun x => usedFv.contains x)
            let goal ← WhnfR goal l1 l2
            mtrace on .zero with s!" goal {← ppExpr goal}"
            let hyps ← lifted.foldlM (fun L fv => do
              let T ← fv.GetType l1 l2
              let T ←  (do match ← IsClass? T l1 l2 with | .none => WhnfR T l1 l2 | _ => return T)
              match ← postCleanReject l1 l2 T with
              | .none => return L
              | .some T => return T :: L --return (fv,T) :: L
              ) []
            -- let presinks ← presinks.foldlM (fun S (_,T) => do
            --   let nonSink := T.getFVarIds
            --   return S.filter (fun (x,_) => !(nonSink.contains x))
            --   ) presinks
            -- let hyps := presinks.mapTRR Prod.snd
            mtrace on .zero with s!" hyps {← hyps.mapM ppExpr}"
            let samples := .cons r lifted goal hyps samples
            sampleCoreBack preProcessed conjable l1 l2 depthDig depthStart depthStop deltaFuzz zetaFuzz todo samples (haveP.foldl havePats ListProd3.cons)
      | .simp simpSteps _ usedFv =>
          match ← simpProof_topDelab' simpSteps with
          | .some fvs goal n =>
              -- let locLifted := (fvs.foldl (fun x y => x.insert y) lifted) -- worried about duplication
              -- let locLifted := locLifted.filter (fun x => usedFv.contains x)
              let locLifted := (fvs.foldl (fun x y => x.insert y) usedFv)  --fvs
              let hyps ← locLifted.foldlM (fun L fv => do
                let T ← fv.GetType l1 l2
                let T ← (do match ← IsClass? T l1 l2 with | .none => WhnfR T l1 l2 | _ => return T)
                match ← postCleanReject l1 l2 T with
                | .none => return L
                | .some T => return T :: L --return (fv,T) :: L
                ) []
              -- let presinks ← presinks.foldlM (fun S (_,T) => do
              --   let nonSink := T.getFVarIds
              --   return S.filter (fun (x,_) => !(nonSink.contains x))
              --   ) presinks
              -- let hyps := presinks.mapTRR Prod.snd
              let samples := .cons (.thm n) lifted (cleanBetaTopType goal) hyps samples
              let .mk todo haveP l1 l2 ← digExpr preProcessed l1 l2 depthDig e todo lifted
              sampleCoreBack preProcessed conjable l1 l2 depthDig depthStart depthStop deltaFuzz zetaFuzz todo samples (haveP.foldl havePats ListProd3.cons)
          | .none =>
              let .mk todo haveP l1 l2 ← digExpr preProcessed l1 l2 depthDig e todo lifted
              sampleCoreBack preProcessed conjable l1 l2 depthDig depthStart depthStop deltaFuzz zetaFuzz todo samples (haveP.foldl havePats ListProd3.cons)
  | .nil => return .mk samples havePats l1 l2


#check 1

-- #exit

partial def sampleCoreForw
  (preProcessed : CTrie SimpCongrTheorem) --(conjable : CTrie (List Nat))
  (l1 : LocalContext) (l2 : LocalInstances) (withHyps : Bool)
  (depthDig depthStart depthStop : Nat) (deltaFuzz zetaFuzz : Option Nat) (todo : ListProd SubProof (List FVarId))
  (samples : ListProd4 SampleData (List FVarId) Expr (List Expr))
  : MetaM (Prod3 (ListProd4 SampleData (List FVarId) Expr (List Expr)) LocalContext LocalInstances) := do
  mtracing
  let rec inner (l1 : LocalContext) (l2 : LocalInstances)
    (goal : Expr) (lifted : List FVarId) (presinks : List (FVarId × Expr))
    (seenH : List Expr) (samples : ListProd4 SampleData (List FVarId) Expr (List Expr))
    : ListProd (Option Expr) Expr → MetaM (Prod3 (ListProd4 SampleData (List FVarId) Expr (List Expr)) LocalContext LocalInstances)
    | .nil => return .mk samples l1 l2
    | .cons term type more => do
        match term with
        | .none =>
          -- akward case to handle simp
          inner l1 l2 goal lifted presinks (type :: seenH) samples more
        | .some term =>
          let .mk dr subhyp l1 l2 ← (if withHyps then delabTopForw_withHyps preProcessed term l1 l2 else delabTopForw preProcessed term l1 l2)
          match dr with
          | .none | .induc .. => inner l1 l2 goal lifted presinks (type :: seenH) samples more
          | .thm sn | .thmC sn .. =>
            if sn.getPrefix! == "_private"
            then
              inner l1 l2 goal lifted presinks (type :: seenH) samples more
            else
              let shT ← withLCtx l1 l2 <| subhyp.foldlM (fun H x => do
                let t ← inferType x
                let t ← whnfR t
                match ← postCleanReject l1 l2 t with
                | .none => return H
                | .some t => return t :: H
                ) seenH
              let hyps := more.foldl shT (fun _ t H => t :: H)
              let hyps ← presinks.foldlM (fun S (fv,fvT) => do
                -- let nonSink := hyps.any (fun HT => HT.onAllSubtermsCheckExistsTR (fun | .fvar id => fv == id | _ => false))
                -- if nonSink then return S else return  fvT :: S
                return  fvT :: S
                ) hyps
              mtrace on .zero with s!" hyps {← hyps.mapM ppExpr}"
              let samples := .cons dr lifted goal hyps samples
              inner l1 l2 goal lifted presinks (type :: seenH) samples more
  match todo with
  | .cons e lifted todo => do
      mtrace on .zero with s!" looking at sample:\nterm : {← e.pp l1 l2}"
      match e with
      | .raw e | .irreducible e =>
        let .mk e fvs l1 l2 ← LambdaOnlyTelescope e l1 l2
        mtrace on .zero with s!" possibly introed to:\nterm : {← ppExpr e}"
        -- Note : here and in all other sampling fuctions : shouldn't ever synthesise instances,
        -- because local instance don't get cleaned ...
        let lifted := (fvs.foldl (fun x y => x.cons y.fvarId!) lifted)
        let .mk todo _ l1 l2 ← digExpr preProcessed l1 l2 depthDig (.raw e) todo lifted
        let .mk hyps l1 l2 ← sampleHypsCore preProcessed l1 l2 depthStart depthStop e lifted deltaFuzz zetaFuzz
        let goal ← InferType e l1 l2
        let usedFv := e.getFVarIds
        let goal ← WhnfR goal l1 l2
        mtrace on .zero with s!" goal {← ppExpr goal}"
        let .mk samples l1 l2 ← hyps.foldlM (Prod3.mk samples l1 l2) (fun locLifted hs (.mk samples l1 l2) => do
          withLCtx l1 l2 <| do
            let locLifted := locLifted.filter (fun x => usedFv.contains x)
            let presinks ← locLifted.foldlM (fun L fv => do
              let T ← fv.getType
              let T ← (do match ← isClass? T with | .none => whnfR T | _ => return T)
              match ← postCleanReject l1 l2 T with
              | .none => return L
              | .some T => return (fv,T) :: L
              ) []
            -- let presinks ← presinks.foldlM (fun S (_,T) => do
            --   let nonSink := T.getFVarIds
            --   return S.filter (fun (x,_) => !(nonSink.contains x))
            --   ) presinks
            let prehyps ← hs.foldlM (fun H h => do
              match h with
              | .raw h | .irreducible h =>
                if h.isRefl?
                then return H
                else
                  let T ← inferType h
                  let T ← whnfR T
                  match ← postCleanReject l1 l2 T with
                  | .none => return H
                  | .some T => return ListProd.cons (.some h) T H
              | .simp simpSteps nonTerminal _ =>
                  match simpSteps with
                  | .nil =>
                    match nonTerminal with
                    | .none => return H
                    | .some nonTerminal =>
                        let T ← inferType nonTerminal
                        let T ← whnfR T
                        match ← postCleanReject l1 l2 T with
                        | .none => return H
                        | .some T => return .cons (.some nonTerminal) T H
                  | .cons _ T _ _ =>
                    let T ← WhnfR (cleanBetaTopType T) l1 l2
                    return .cons .none T H
              ) .nil
            -- let print ← @ListProd.foldlM MetaM _ (Option Expr) Expr (ListProd (Option Format) Format) prehyps (ListProd.nil) (fun x y z => do
            --   let px ← x.mapM ppExpr
            --   let py ← ppExpr y
            --   return ListProd.cons px py z)
            -- dbg_trace s!" prehyps {print.toListOfProd}"
            inner l1 l2 goal lifted presinks [] samples prehyps
          )
        sampleCoreForw preProcessed l1 l2 withHyps depthDig depthStart depthStop deltaFuzz zetaFuzz todo samples
      | .simp simpSteps _  _ =>
          if withHyps
          then
            match ← simpProof_topDelab' simpSteps with
            | .some fvs shyp n =>
                -- let locLifted := (fvs.foldl (fun x y => x.insert y) lifted) -- worried about duplication
                -- let locLifted := locLifted.filter (fun x => usedFv.contains x)
                --let locLifted := fvs
                let locLifted := (fvs.foldl (fun x y => x.insert y) [])
                let presinks ← locLifted.foldlM (fun L fv => do
                let T ← fv.GetType l1 l2
                let T ← (do match ← IsClass? T l1 l2 with | .none => WhnfR T l1 l2 | _ => return T)
                match ← postCleanReject l1 l2 T with
                | .none => return L
                | .some T => return T :: L --return (fv,T) :: L
                ) []
                -- let presinks ← presinks.foldlM (fun S (_,T) => do
                --   let nonSink := T.getFVarIds
                --   return S.filter (fun (x,_) => !(nonSink.contains x))
                --   ) presinks
                let hyps := (cleanBetaTopType shyp) :: presinks --presinks.mapTRR Prod.snd
                let samples := .cons (.thm n) lifted (.const `True []) hyps samples
                -- ficticous goal true ... idealy we want this to be a forward step in any goal,
                -- and our framework doesn't really allow us to track that
                let .mk todo _ l1 l2 ← digExpr preProcessed l1 l2 depthDig e todo lifted
                sampleCoreForw preProcessed l1 l2 withHyps depthDig depthStart depthStop deltaFuzz zetaFuzz todo samples
            | .none =>
                let .mk todo _ l1 l2 ← digExpr preProcessed l1 l2 depthDig e todo lifted
                sampleCoreForw preProcessed l1 l2 withHyps depthDig depthStart depthStop deltaFuzz zetaFuzz todo samples
          else
            sampleCoreForw preProcessed l1 l2 withHyps depthDig depthStart depthStop deltaFuzz zetaFuzz todo samples
  | .nil => return .mk samples l1 l2


#check 1

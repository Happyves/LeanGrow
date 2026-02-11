
/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/


import LeanGrow.Src.Core.Embedding.EmbedQueryBackRW
import LeanGrow.Src.Core.Rewriting.Main


open Lean Meta




/--
Synthesises instances.
Continuation expects:
- goal type with assigned lnodes instantiated (exlcude it and its computation if useless for ranking)
- level params, some with dummy assignements
- the level params not assigned yet
- theorem args, some with dummy assignements
- the args not yes assigne, by position and with their type
  with assigned lnodes instantiated
-/
@[inline]
def embedBackProcess (l1 : LocalContext) (l2 : LocalInstances) (thmData : ThmFormat) (res : embedBackData)
  : MetaM (OptionProd5 Expr (Array Level) (List Nat) (Array Expr) (ListProd Nat Expr)) := do
  do
  mtracing
  -- *Note*, we expect the defeqs to have assigned transitive dependet arguments
  let arg_lvls : Array Level := Array.replicate thmData.lvlParamsNum .zero
  let arg_exprs : Array Expr := Array.replicate thmData.hypsNum (failExpr "embedBackProcess")
  let (arg_lvls, todo_lvls) := res.llv.foldl (arg_lvls, List.range thmData.lvlParamsNum)
    (fun pos al (arg_lvls, todo_lvls) =>
      let arg_lvls := arg_lvls.set! pos al
      let todo_lvls := List.orderedEraseOrLeave pos todo_lvls
      (arg_lvls, todo_lvls))
  mtrace on .zero with s!"[embedBackProcess] arg_lvls {repr arg_lvls}, todo_lvls {todo_lvls}"
  let (arg_exprs, todo_expr_inds) := res.ln.foldl (arg_exprs, List.range thmData.hypsNum)
    (fun pos al (arg_exprs, todo_expr_inds) =>
      let arg_exprs := arg_exprs.set! pos al
      let todo_expr_inds := List.orderedEraseOrLeave pos todo_expr_inds
      (arg_exprs, todo_expr_inds))
  mtrace on .zero with s!"[embedBackProcess] arg_exprs {← arg_exprs.mapM (PpExpr ·  l1 l2)}, todo_expr_inds {todo_expr_inds}"
  let todo_expr : ListProd Nat Expr := .nil
  todo_expr_inds.foldlMcps (Prod3.mk arg_exprs todo_expr todo_expr_inds) (fun i (.mk arg_exprs todo_expr todo_expr_inds) cont => do
    let T := thmData.hypsTypes[i]!
    mtrace on .zero with s!"[embedBackProcess] todo type {← PpExpr T l1 l2}"
    let T := T.onAllSubtermsTR (fun
      | x@(.mvar ⟨.num _ p⟩) =>
          if (todo_expr_inds.orderedContains p)
          -- missed the negation in ↑ and it eluded test for ages ; check if bug anwhere else
          then x
          else arg_exprs[p]!
      | .sort lv => .sort <| lv.onAllSubtermsTR (fun
          | x@(.mvar ⟨.num _ p⟩) =>
              if !(todo_lvls.orderedContains p)
              then x
              else arg_lvls[p]!
          | x => x)
      | .const n lvs => .const n  <| lvs.map <| fun lv => lv.onAllSubtermsTR (fun
          | x@(.mvar ⟨.num _ p⟩) =>
              if !(todo_lvls.orderedContains p)
              then x
              else arg_lvls[p]!
          | x => x)
      | x => x)
    mtrace on .zero with s!"[embedBackProcess] instantaited to {← PpExpr T l1 l2}"
    match thmData.hyps[i]! with
    | .reg .. =>
        cont (.mk arg_exprs (.cons i T todo_expr) todo_expr_inds)
    | .inst .. =>
        let val? ← (SynthInstance T l1 l2)
        match val? with
        | .none =>
            mtrace on .zero with s!"[embedBackProcess] ways instance, but synthesis failed"
            return .none
          -- *Note* ↑ is an avoidable design choice. We could keep unsythesised instances as new goals,
          -- but this is most commonly more of a burden then anything else, so we just fail.
        | .some val =>
            mtrace on .zero with s!"[embedBackProcess] successfully synthesised instance for it"
            cont (.mk (arg_exprs.set! i val) todo_expr (todo_expr_inds.orderedEraseOrLeave i))
    ) <| fun (.mk arg_exprs todo_expr _) => do
      let G := thmData.goal
      mtrace on .zero with s!"[embedBackProcess] goal {← PpExpr G l1 l2}"
      let G := G.onAllSubtermsTR (fun
        | x@(.mvar ⟨.num _ p⟩) =>
            if (todo_expr_inds.orderedContains p)
            then x
            else arg_exprs[p]!
        | .sort lv => .sort <| lv.onAllSubtermsTR (fun
            | x@(.mvar ⟨.num _ p⟩) =>
                if !(todo_lvls.orderedContains p)
                then x
                else arg_lvls[p]!
            | x => x)
        | .const n lvs => .const n  <| lvs.map <| fun lv => lv.onAllSubtermsTR (fun
            | x@(.mvar ⟨.num _ p⟩) =>
                if !(todo_lvls.orderedContains p)
                then x
                else arg_lvls[p]!
            | x => x)
        | x => x)
      mtrace on .zero with s!"[embedBackProcess] instantiated to {← PpExpr G l1 l2}"
      let todo_expr := todo_expr.foldl .nil ListProd.cons
      -- we must reverse it as next functions expect dependencies
      return .some G arg_lvls todo_lvls arg_exprs todo_expr

#check 1



/--
Synthesises instances.
Continuation expects:
- goal type with assigned lnodes instantiated (exlcude it and its computation if useless for ranking)
- level params, some with dummy assignements
- the level params not assigned yet
- theorem args, some with dummy assignements
- the args not yes assigne, by position and with their type
  with assigned lnodes instantiated
-/
@[inline]
def embedBackProcess' (l1 : LocalContext) (l2 : LocalInstances) (thmData : ThmFormat) (res : embedBackData)
  : MetaM (OptionProd5 Expr (Array Level) (List Nat) (Array Expr) (ListProd Nat Expr)) := do
  do
  mtracing
  -- *Note*, we expect the defeqs to have assigned transitive dependet arguments
  let arg_lvls : Array Level := Array.replicate thmData.lvlParamsNum .zero
  let arg_exprs : Array Expr := Array.replicate thmData.hypsNum (failExpr "embedBackProcess")
  let (arg_lvls, todo_lvls) := res.llv.foldl (arg_lvls, List.range thmData.lvlParamsNum)
    (fun pos al (arg_lvls, todo_lvls) =>
      let al := al.onAllSubterms (fun
        | l@(.param ((.num (.num _ bi) po))) =>
          match res.tlv.find? (fun x y _ => x == bi && y == po) with
          | .none => l
          | .some _ _ rep => rep
        | x => x
        )
      let arg_lvls := arg_lvls.set! pos al
      let todo_lvls := List.orderedEraseOrLeave pos todo_lvls
      (arg_lvls, todo_lvls))
  mtrace on .zero with s!"[embedBackProcess] arg_lvls {repr arg_lvls}, todo_lvls {todo_lvls}"
  let (arg_exprs, todo_expr_inds) := res.ln.foldl (arg_exprs, List.range thmData.hypsNum)
    (fun pos al (arg_exprs, todo_expr_inds) =>
      let al := al.onAllSubterms (fun
        | l@(.fvar (.mk (.num (.num _ bi) po))) =>
          match res.tn.find? (fun x y _ => x == bi && y == po) with
          | .none => l
          | .some _ _ rep => rep
        | .sort u => .sort <| u.onAllSubterms (fun
            | l@(.param ((.num (.num _ bi) po))) =>
              match res.tlv.find? (fun x y _ => x == bi && y == po) with
              | .none => l
              | .some _ _ rep => rep
            | x => x
            )
        | .const n us => .const n <| us.map <| fun u => u.onAllSubterms (fun
            | l@(.param ((.num (.num _ bi) po))) =>
              match res.tlv.find? (fun x y _ => x == bi && y == po) with
              | .none => l
              | .some _ _ rep => rep
            | x => x
            )
        | x => x
        )
      let arg_exprs := arg_exprs.set! pos al
      let todo_expr_inds := List.orderedEraseOrLeave pos todo_expr_inds
      (arg_exprs, todo_expr_inds))
  mtrace on .zero with s!"[embedBackProcess] arg_exprs {← arg_exprs.mapM (PpExpr ·  l1 l2)}, todo_expr_inds {todo_expr_inds}"
  let todo_expr : ListProd Nat Expr := .nil
  todo_expr_inds.foldlMcps (Prod3.mk arg_exprs todo_expr todo_expr_inds) (fun i (.mk arg_exprs todo_expr todo_expr_inds) cont => do
    let T := thmData.hypsTypes[i]!
    mtrace on .zero with s!"[embedBackProcess] todo type {← PpExpr T l1 l2}"
    let T := T.onAllSubtermsTR (fun
      | x@(.mvar ⟨.num _ p⟩) =>
          if (todo_expr_inds.orderedContains p)
          -- missed the negation in ↑ and it eluded test for ages ; check if bug anwhere else
          then x
          else arg_exprs[p]!
      | .sort lv => .sort <| lv.onAllSubtermsTR (fun
          | x@(.mvar ⟨.num _ p⟩) =>
              if !(todo_lvls.orderedContains p)
              then x
              else arg_lvls[p]!
          | x => x)
      | .const n lvs => .const n  <| lvs.map <| fun lv => lv.onAllSubtermsTR (fun
          | x@(.mvar ⟨.num _ p⟩) =>
              if !(todo_lvls.orderedContains p)
              then x
              else arg_lvls[p]!
          | x => x)
      | x => x)
    mtrace on .zero with s!"[embedBackProcess] instantaited to {← PpExpr T l1 l2}"
    match thmData.hyps[i]! with
    | .reg .. =>
        cont (.mk arg_exprs (.cons i T todo_expr) todo_expr_inds)
    | .inst .. =>
        let val? ← (SynthInstance T l1 l2)
        match val? with
        | .none =>
            mtrace on .zero with s!"[embedBackProcess] ways instance, but synthesis failed"
            return .none
          -- *Note* ↑ is an avoidable design choice. We could keep unsythesised instances as new goals,
          -- but this is most commonly more of a burden then anything else, so we just fail.
        | .some val =>
            mtrace on .zero with s!"[embedBackProcess] successfully synthesised instance for it"
            cont (.mk (arg_exprs.set! i val) todo_expr (todo_expr_inds.orderedEraseOrLeave i))
    ) <| fun (.mk arg_exprs todo_expr _) => do
      let G := thmData.goal
      mtrace on .zero with s!"[embedBackProcess] goal {← PpExpr G l1 l2}"
      let G := G.onAllSubtermsTR (fun
        | x@(.mvar ⟨.num _ p⟩) =>
            if (todo_expr_inds.orderedContains p)
            then x
            else arg_exprs[p]!
        | .sort lv => .sort <| lv.onAllSubtermsTR (fun
            | x@(.mvar ⟨.num _ p⟩) =>
                if !(todo_lvls.orderedContains p)
                then x
                else arg_lvls[p]!
            | x => x)
        | .const n lvs => .const n  <| lvs.map <| fun lv => lv.onAllSubtermsTR (fun
            | x@(.mvar ⟨.num _ p⟩) =>
                if !(todo_lvls.orderedContains p)
                then x
                else arg_lvls[p]!
            | x => x)
        | x => x)
      mtrace on .zero with s!"[embedBackProcess] instantiated to {← PpExpr G l1 l2}"
      let todo_expr := todo_expr.foldl .nil ListProd.cons
      -- we must reverse it as next functions expect dependencies
      return .some G arg_lvls todo_lvls arg_exprs todo_expr


#check 1



/--
Adds tnodes, makes term and orders tnodes and returns their pos-index size.

- Level tnode pos is actual pos in thm params
- Expr tnode pos is arbitrary, but indexed from 0 to the Nat expected by `k`, so as to use Arrays
-/
@[inline]
def embedBackPreIntegrate
  (l1 : LocalContext) (l2 : LocalInstances)
  (thmData : ThmFormat) (NewBackIdx : Nat)
  (arg_lvls : Array Level) (todo_lvls : List Nat) (arg_exprs : Array Expr) (todo_expr : ListProd Nat Expr)
  : MetaM (Prod4 Expr Nat LocalContext LocalInstances) :=
    do
    mtracing
    let mut arg_lvls := arg_lvls
    for i in todo_lvls do
      let lmid := tnode NewBackIdx i
      arg_lvls := arg_lvls.set! i (.param lmid)
    mtrace on .zero with s!"[embedBackPreIntegrate] arg_lvls {repr arg_lvls}"
    todo_expr.foldlMcps (⟨arg_exprs,0,l1,l2⟩ : Prod4 _ _ _ _) (fun i T ⟨arg_exprs,c,l1,l2⟩ cont => do
      mtrace on .zero with s!"[embedBackPreIntegrate] todo type {← PpExpr T l1 l2}"
      let T := T.onAllSubtermsTR (fun
        | (.mvar ⟨.num _ p⟩) =>
            match todo_expr.findIdx? (fun n _ => n == p) 0 with
            | .none => failExpr "embedBackPreIntegrate"
            | .some idx => .fvar ⟨tnode NewBackIdx idx⟩
        | .sort lv => .sort <| lv.onAllSubtermsTR (fun
            | (.mvar ⟨.num _ p⟩) => arg_lvls[p]!
            | x => x)
        | .const n lvs => .const n  <| lvs.map <| fun lv => lv.onAllSubtermsTR (fun
            | (.mvar ⟨.num _ p⟩) => arg_lvls[p]!
            | x => x)
        | x => x)
      mtrace on .zero with s!"[embedBackPreIntegrate] instantaited to {← PpExpr T l1 l2}"
      let tn := tnode NewBackIdx c
      mtrace on .zero with s!"[embedBackPreIntegrate] assigned tnode id {tn}"
      let ⟨wtn,l1,l2⟩ ← WithLocalDecl tn T l1 l2
      cont ⟨arg_exprs.set! i (.fvar wtn), c+1,l1,l2⟩
      ) <| fun ⟨arg_exprs,c,l1,l2⟩ => do
        let term := mkAppN (match thmData.name with | .inl n => .const n arg_lvls.toList | .inr id => .fvar id) arg_exprs
        mtrace on .zero with s!"[embedBackPreIntegrate] term {← PpExpr term l1 l2}"
        return ⟨term, c,l1,l2⟩


#check 1

-- #exit


/-- we should still bump backIdx at failure, as tnodes have been added ? -/
@[specialize, inline]
def embedBackRWPreIntegrate
  (introAdmissible? : Nat → Bool)
  (l1 : LocalContext) (l2 : LocalInstances)
  (depsCache : Array DepCache) (RevCutOff : Nat)
  (dirs : rwDirs) (NewBackIdx : Nat) (within : Expr) (extWorkas : List FVarId) (thmData : ThmFormat)
  (arg_lvls : Array Level) (todo_lvls : List Nat) (arg_exprs : Array Expr) (todo_expr : ListProd Nat Expr)
  : MetaM (Prod3 (OptionProd Expr Nat) LocalContext LocalInstances) :=
  do
  mtracing
  match thmData with
  | .std .. => throwError s!"[embedBackRWPreIntegrate] tryto to perform rewrite with non rewrite lemm {repr thmData.name}"
  | .rw _ _ kind .. =>
      do
      let mut arg_lvls := arg_lvls
      for i in todo_lvls do
        let lmid := tnode NewBackIdx i
        arg_lvls := arg_lvls.set! i (.param lmid)
      mtrace on .zero with s!"[embedBackRWPreIntegrate] arg_lvls {repr arg_lvls}"
      let extWorkas : Array FVarId := extWorkas.reverse.toArray
      let aws := extWorkas.map Expr.fvar
      mtrace on .zero with s!"[embedBackRWPreIntegrate] aws/extWorkas {← aws.mapM (PpExpr · l1 l2)} of types {← aws.mapM (fun e => return ← PpExpr (← InferType e l1 l2) l1 l2)}"
      todo_expr.foldlMcps (⟨arg_exprs,0,l1,l2⟩ : Prod4 _ _ _ _) (fun i T ⟨arg_exprs,c,l1,l2⟩ cont => do
        mtrace on .zero with s!"[embedBackRWPreIntegrate] todo type {← PpExpr T l1 l2}"
        let T := T.onAllSubtermsTR (fun
          | (.mvar ⟨.num _ p⟩) =>
              match todo_expr.findIdx? (fun n _ => n == p) 0 with
              | .none => failExpr "embedBackRWPreIntegrate"
              | .some idx => mkAppN (.fvar ⟨tnode NewBackIdx idx⟩) aws
          | .sort lv => .sort <| lv.onAllSubtermsTR (fun
              | (.mvar ⟨.num _ p⟩) => arg_lvls[p]!
              | x => x)
          | .const n lvs => .const n  <| lvs.map <| fun lv => lv.onAllSubtermsTR (fun
              | (.mvar ⟨.num _ p⟩) => arg_lvls[p]!
              | x => x)
          | x => x)
        mtrace on .zero with s!"[embedBackRWPreIntegrate] instanciated to {← PpExpr T l1 l2}"
        let ⟨T,l1,l2⟩ ← T.abstractLetFvarAll l1 l2 extWorkas
        mtrace on .zero with s!"[embedBackRWPreIntegrate] instantaited to {← PpExpr T l1 l2}"
        let tn := tnode NewBackIdx c
        mtrace on .zero with s!"[embedBackRWPreIntegrate] assigned tnode id {tn}"
        let ⟨wtn,l1,l2⟩ ← WithLocalDecl tn T l1 l2
        cont ⟨arg_exprs.set! i (mkAppN (.fvar wtn) aws), c+1,l1,l2⟩
        ) <| fun ⟨arg_exprs,c,l1,l2⟩ => do
          let term := mkAppN (match thmData.name with | .inl n => .const n arg_lvls.toList | .inr id => .fvar id) arg_exprs
          mtrace on .zero with s!"[embedBackRWPreIntegrate] term {← PpExpr term l1 l2}"
          let prefixed : Expr := ← withLCtx l1 l2 <| do
            match kind with
            | .eq_mp => return term
            | .eq_mpr => mkAppM `Eq.symm #[term]
            | .iff_mp => mkAppM `propext #[term]
            | .iff_mpr => mkAppM `Eq.symm #[← mkAppM `propext #[term]]
          let T ← InferType prefixed l1 l2
          let .some (_,pat,_) := T.eq? | throwError s!"[embedBackRWPreIntegrate] expected eq, got {← PpExpr T l1 l2}"
          mtrace on .zero with s!"[embedBackRWPreIntegrate] start mainBackRWData with pat {← PpExpr pat l1 l2} and within {← PpExpr within l1 l2}"
          let .mk wis l1 l2 ← (do
            if c != 0
            then return Prod3.mk (List.range aws.size) l1 l2
            else
              let r1 ← prefixed.getWorkerIndsTrans l1 l2
              let .mk w2 l1 l2 ← pat.getWorkerIndsTrans r1.2 r1.3
              let ws := (List.orderedUnion r1.1.toList w2.toList)
              return .mk ws l1 l2
            )
          let ⟨fullProof,l1,l2⟩ ← mainBackRW introAdmissible? depsCache RevCutOff l1 l2 dirs NewBackIdx c within pat prefixed wis
          match fullProof with
          | .none => return .mk .none l1 l2
          | .some fullProof =>
            if ← IsTypeCorrect fullProof l1 l2
            then return .mk (.some fullProof (c+1)) l1 l2
            else
              mtrace on .zero with s!"[embedBackRWPreIntegrate] proof not type correct: {← PpExpr fullProof l1 l2}"
              let dbugHelp (l1 : LocalContext) (fullProof : Expr) : MetaM Unit := do
                let hmm := Kernel.check (← getEnv) l1 fullProof
                match hmm with
                | .ok _ => IO.println "Correct: yes"
                | .error e => IO.println s!"Correct: no\n{← MessageData.format (e.toMessageData {})}" ;
              mtrace on .zero with s!"[embedBackRWPreIntegrate] Kernel check: {← dbugHelp l1 fullProof}"
              return .mk .none l1 l2
#check 1


/--
- we should still bump backIdx at failure, as tnodes have been added ?
- difference to ↑ is that we replace tnodes of within with matched values
-/
@[specialize, inline]
def embedBackRWPreIntegrate'
  (introAdmissible? : Nat → Bool)
  (l1 : LocalContext) (l2 : LocalInstances)
  (depsCache : Array DepCache) (RevCutOff : Nat)
  (dirs : rwDirs) (NewBackIdx : Nat) (within : Expr) (extWorkas : List FVarId)
  (thmData : ThmFormat) (res : embedBackData)
  (arg_lvls : Array Level) (todo_lvls : List Nat) (arg_exprs : Array Expr) (todo_expr : ListProd Nat Expr)
  : MetaM (Prod3 (OptionProd Expr Nat) LocalContext LocalInstances) :=
  do
  mtracing
  match thmData with
  | .std .. => throwError s!"[embedBackRWPreIntegrate] tryto to perform rewrite with non rewrite lemm {repr thmData.name}"
  | .rw _ _ kind .. =>
      do
      let mut arg_lvls := arg_lvls
      for i in todo_lvls do
        let lmid := tnode NewBackIdx i
        arg_lvls := arg_lvls.set! i (.param lmid)
      mtrace on .zero with s!"[embedBackRWPreIntegrate] arg_lvls {repr arg_lvls}"
      let extWorkas : Array FVarId := extWorkas.reverse.toArray
      let aws := extWorkas.map Expr.fvar
      mtrace on .zero with s!"[embedBackRWPreIntegrate] aws/extWorkas {← aws.mapM (PpExpr · l1 l2)} of types {← aws.mapM (fun e => return ← PpExpr (← InferType e l1 l2) l1 l2)}"
      todo_expr.foldlMcps (⟨arg_exprs,0,l1,l2⟩ : Prod4 _ _ _ _) (fun i T ⟨arg_exprs,c,l1,l2⟩ cont => do
        mtrace on .zero with s!"[embedBackRWPreIntegrate] todo type {← PpExpr T l1 l2}"
        let T := T.onAllSubtermsTR (fun
          | (.mvar ⟨.num _ p⟩) =>
              match todo_expr.findIdx? (fun n _ => n == p) 0 with
              | .none => failExpr "embedBackRWPreIntegrate"
              | .some idx => mkAppN (.fvar ⟨tnode NewBackIdx idx⟩) aws
          | .sort lv => .sort <| lv.onAllSubtermsTR (fun
              | (.mvar ⟨.num _ p⟩) => arg_lvls[p]!
              | x => x)
          | .const n lvs => .const n  <| lvs.map <| fun lv => lv.onAllSubtermsTR (fun
              | (.mvar ⟨.num _ p⟩) => arg_lvls[p]!
              | x => x)
          | x => x)
        mtrace on .zero with s!"[embedBackRWPreIntegrate] instanciated to {← PpExpr T l1 l2}"
        let ⟨T,l1,l2⟩ ← T.abstractLetFvarAll l1 l2 extWorkas
        mtrace on .zero with s!"[embedBackRWPreIntegrate] instantaited to {← PpExpr T l1 l2}"
        let tn := tnode NewBackIdx c
        mtrace on .zero with s!"[embedBackRWPreIntegrate] assigned tnode id {tn}"
        let ⟨wtn,l1,l2⟩ ← WithLocalDecl tn T l1 l2
        cont ⟨arg_exprs.set! i (mkAppN (.fvar wtn) aws), c+1,l1,l2⟩
        ) <| fun ⟨arg_exprs,c,l1,l2⟩ => do
          let term := mkAppN (match thmData.name with | .inl n => .const n arg_lvls.toList | .inr id => .fvar id) arg_exprs
          mtrace on .zero with s!"[embedBackRWPreIntegrate] term {← PpExpr term l1 l2}"
          let prefixed : Expr := ← withLCtx l1 l2 <| do
            match kind with
            | .eq_mp => return term
            | .eq_mpr => mkAppM `Eq.symm #[term]
            | .iff_mp => mkAppM `propext #[term]
            | .iff_mpr => mkAppM `Eq.symm #[← mkAppM `propext #[term]]
          let T ← InferType prefixed l1 l2
          let .some (_,pat,_) := T.eq? | throwError s!"[embedBackRWPreIntegrate] expected eq, got {← PpExpr T l1 l2}"
          let within := within.onAllSubtermsTR (fun
            | l@(.fvar (.mk (.num (.num _ bi) po))) =>
              match res.tn.find? (fun x y _ => x == bi && y == po) with
              | .none => l
              | .some _ _ rep => rep
            | .sort u => .sort <| u.onAllSubterms (fun
                | l@(.param ((.num (.num _ bi) po))) =>
                  match res.tlv.find? (fun x y _ => x == bi && y == po) with
                  | .none => l
                  | .some _ _ rep => rep
                | x => x
                )
            | .const n us => .const n <| us.map <| fun u => u.onAllSubterms (fun
                | l@(.param ((.num (.num _ bi) po))) =>
                  match res.tlv.find? (fun x y _ => x == bi && y == po) with
                  | .none => l
                  | .some _ _ rep => rep
                | x => x
                )
            | x => x
            )
          mtrace on .zero with s!"[embedBackRWPreIntegrate] start mainBackRWData with pat {← PpExpr pat l1 l2} and within {← PpExpr within l1 l2}"
          let .mk wis l1 l2 ← (do
            if c != 0
            then return Prod3.mk (List.range aws.size) l1 l2
            else
              let r1 ← prefixed.getWorkerIndsTrans l1 l2
              let .mk w2 l1 l2 ← pat.getWorkerIndsTrans r1.2 r1.3
              let ws := (List.orderedUnion r1.1.toList w2.toList)
              return .mk ws l1 l2
            )
          let ⟨fullProof,l1,l2⟩ ← mainBackRW introAdmissible? depsCache RevCutOff l1 l2 dirs NewBackIdx c within pat prefixed wis
          match fullProof with
          | .none => return .mk .none l1 l2
          | .some fullProof =>
            if ← IsTypeCorrect fullProof l1 l2
            then return .mk (.some fullProof (c+1)) l1 l2
            else
              mtrace on .zero with s!"[embedBackRWPreIntegrate] proof not type correct: {← PpExpr fullProof l1 l2}"
              let dbugHelp (l1 : LocalContext) (fullProof : Expr) : MetaM Unit := do
                let hmm := Kernel.check (← getEnv) l1 fullProof
                match hmm with
                | .ok _ => IO.println "Correct: yes"
                | .error e => IO.println s!"Correct: no\n{← MessageData.format (e.toMessageData {})}" ;
              mtrace on .zero with s!"[embedBackRWPreIntegrate] Kernel check: {← dbugHelp l1 fullProof}"
              return .mk .none l1 l2


/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import Lean.Meta.Tactic.Grind.RevertAll
import LeanGrow.Src.Utils.LeanGrow.Expr

open Lean Meta


structure DepCache where
  proof : Bool
  forw : List FVarId
  back : List FVarId
  fTrans : UInt32Array
deriving Repr, Inhabited


@[inline]
partial def DepCache.addGU (D : Array DepCache) (gu_fv : FVarId) (l1 : LocalContext) (l2 : LocalInstances) : MetaM (Array DepCache) := do
  let (p?,bd) ← withLCtx l1 l2 <| do
    let d ← gu_fv.getDecl
    match d with
    | .cdecl _ _ _ T .. =>
      let p? ← isProp T
      return (p?,T.getGUFVarsIds)
    | .ldecl _ _ _ T V .. =>
      let p? ← isProp T
      if p?
      then return (p?,T.getGUFVarsIds)
      else
        let bd := T.getGUFVarsIds' <| V.getGUFVarsIds
        return (p?,bd)
  match gu_fv.name with
  | .num _ i =>
      let I := i.toUInt32
      let D := bd.foldl (fun d ⟨fv⟩ =>
        match fv with
        | .num _ idx => d.modify idx (fun l => {l with forw := gu_fv :: l.forw})
        | _ => d
        ) D
      let rec trD (D : Array DepCache) (todoPass : List FVarId) (todoStock : List (List FVarId)) : Array DepCache :=
        match todoPass with
        | [] => match todoStock with | nx :: more => trD D nx more | [] => D
        | nx :: more =>
            match nx.name with
            | .num _ idx =>
                let D := D.modify idx (fun l => {l with fTrans := if l.fTrans.isEmpty then l.fTrans.push I else (if l.fTrans[l.fTrans.size - 1]! == I then l.fTrans else l.fTrans.push I)})
                -- to make sure that fTrans stays sorted, assuming gu_fv index is increasing and largest, push is enough
                -- Because of dependecy diamonds, we must make sure to add it only once though
                let next := (D[idx]!.back) :: todoStock
                trD D more next
            | _ => panic s!"[DepCache.addGU] unexpected formats {nx.name}"
      let D := trD D bd []
      return D.push ⟨p?,[],bd,.empty⟩ -- assumes gu-idx is size
  | _ => throwError s!"[DepCache.addGU] unexpected formats {gu_fv.name}"



@[specialize]
def List.takeWhileCounting (p : α → Bool) (c max : Nat) (done : List α) : (xs : List α) → List α
  | [] => done
  | hd :: tl =>
    if c < max
    then
      match p hd with
      | true  => takeWhileCounting p (c+1) max (hd :: done) tl
      | false => takeWhileCounting p c max done tl
    else
      done

@[specialize]
def List.takeWhileCountingM (p : α → MetaM Bool) (c max : Nat) (done : List α) : (xs : List α) → MetaM (List α)
  | [] => return done
  | hd :: tl => do
    if c < max
    then
      match ← p hd with
      | true  => takeWhileCountingM p (c+1) max (hd :: done) tl
      | false => takeWhileCountingM p c max done tl
    else
      return done


/--
- Expect fvars to be in context
- ∀ & let are in same order as `fvs`,  without checking for consistency of abstraction !
- proof valued lets become ∀s
-/
@[inline]
partial def Lean.Expr.abstractLetFvarAll_proofLet
  (initD : LocalContext) (initI : LocalInstances)
  (depsCache : Array DepCache)
  (fvs : Array FVarId) (e : Expr)
  : MetaM (Prod4 Expr (Array FVarId) LocalContext LocalInstances) :=
    let rec bind (term : Expr) (i : Nat) (initD : LocalContext) (initI : LocalInstances) : MetaM (Prod3 Expr LocalContext LocalInstances) := do
      let fvd := (fvs[i]!)
      match ← fvd.GetDecl initD initI with
      | .cdecl _ _ _ T .. =>
          let ⟨T,initD,initI⟩ ← T.onAllSubtermsM initD initI (fun x d initD initI =>
            match x with
            | .fvar id =>
              match fvs.findIdx? (fun y => y == id) with
              | .none => return ⟨x,initD,initI⟩
              | .some j => return ⟨(.bvar (d + i - 1 - j)),initD,initI⟩
            | _ => return ⟨x,initD,initI⟩ )
          if i == 0
          then
            match ← IsClass? T initD initI with
            | .none =>  return ⟨.forallE `abstractFvarWrt T term .default,initD,initI⟩
            | _ =>  return ⟨.forallE `abstractFvarWrt T term .instImplicit,initD,initI⟩
          else
            match ← IsClass? T initD initI with
            | .none => bind (.forallE `abstractFvarWrt T term .default) (i-1) initD initI
            | _ => bind (.forallE `abstractFvarWrt T term .instImplicit) (i-1) initD initI
      | .ldecl _ _ _ T V nonDep .. =>
          let ⟨T,initD,initI⟩ ← T.onAllSubtermsM initD initI (fun x d initD initI =>
            match x with
            | .fvar id =>
              match fvs.findIdx? (fun y => y == id) with
              | .none => return ⟨x,initD,initI⟩
              | .some j => return ⟨(.bvar (d + i - 1 - j)),initD,initI⟩
            | _ => return ⟨x,initD,initI⟩ )
          let p? : Bool ← (do
            match fvd.name with
            | .num k i =>
              if (k == `g || k == `u) then return depsCache[i]!.proof else IsProof T initD initI -- case of workers
            | n => panic! s!"[abstractLetFvarAll_proofLet] unexpected {n}")
          if i == 0
          then
            if p?
            then
              match ← IsClass? T initD initI with
              | .none => return ⟨.forallE `abstractFvarWrt T term .default,initD,initI⟩
              | _ => return ⟨.forallE `abstractFvarWrt T term .instImplicit,initD,initI⟩
            else return ⟨.letE `abstractFvarWrt T V term nonDep,initD,initI⟩
          else
            if p?
            then
              match ← IsClass? T initD initI with
              | .none => bind (.forallE `abstractFvarWrt T term .default) (i-1) initD initI
              | _ => bind (.forallE `abstractFvarWrt T term .instImplicit) (i-1) initD initI
            else bind (.letE `abstractFvarWrt T V term nonDep) (i-1) initD initI
    do
    let fvS := fvs.size
    if fvS == 0
    then return ⟨e,fvs,initD,initI⟩
    else
      let ⟨absd,initD,initI⟩ ← e.onAllSubtermsM initD initI (fun x d initD initI =>
        match x with
        | .fvar id =>
          match fvs.findIdx? (fun y => y == id) with
          | .none => return ⟨x,initD,initI⟩
          | .some i => return ⟨(.bvar (d + fvS - 1 - i)),initD,initI⟩
        | _ => return ⟨x,initD,initI⟩ )
      let ⟨r,l1,l2⟩ ← bind absd (fvs.size - 1) initD initI
      return ⟨r,fvs,l1,l2⟩


/--
- workerDepsCache should increase in depth and have no duplicates !
- the returned fvars don't contain all reverts, not those in the term, where Type.typed lets are missing
- first expr is type, snd is (fun x => x revs)
-/
@[specialize]
partial def revert_NoTn_cutOff_wDepsCache (introAdmissible? : Nat → Bool)
  (l1 : LocalContext) (l2 : LocalInstances)
  (goal : Expr) (guFvs : Array FVarId)
  (depsCache : Array DepCache)
  (workerDepsCache : Array (FVarId × (List FVarId))) (RevCutOff : Nat)
  : MetaM (Prod5 Expr Expr (Array FVarId) LocalContext LocalInstances) :=
  let spread := RevCutOff / guFvs.size
  let rec @[specialize] augment (track : UInt32Array) (final : Array FVarId) (pass : List FVarId) (next : List (List FVarId)) : UInt32Array × Array FVarId :=
    -- dbg_trace (s!"[augment]\n track {repr track}\n final {repr final} \n pass {repr pass}\n next {repr next}")
    if final.size < RevCutOff
    then
      match pass with
      | [] =>
        match next with
        | [] =>
            let res := final.qsort (fun x y =>
              match x.name, y.name with
              | .num _ i, .num _ j => i < j -- increase in dependence ; qsort expects strict order
              | _, _ => panic s!"[revert_NoTn_cutOff_wDepsCache][augment] unexpected formats {x.name} {y.name}")
            (track, res)
        | f :: fs => augment track final f fs
      | nx :: more =>
        match nx.name with
        | .num _ i =>
            let I := i.toUInt32
            if track.oContains I
            then augment track final more next
            else
              let lD := depsCache[i]!.forw.takeWhileCounting (fun x =>
                match x.name with
                | .num _ i => introAdmissible? i
                | _ => panic s!"[revert_NoTn_cutOff_wDepsCache][augment] unexpected formats {x.name}"
                ) 0 spread []
              -- dbg_trace s!"before {repr track}"
              let track := track.oInsert I
              -- dbg_trace s!"after {repr track}"
              augment track (final.push nx) more (next ++ [lD]) -- add to back
        | _ =>
             panic s!"[revert_NoTn_cutOff_wDepsCache][augment] unexpected formats {nx.name}"
    else
      let res := final.qsort (fun x y =>
        match x.name, y.name with
        | .num _ i, .num _ j => i < j -- increase in dependence ; qsort expects strict order
        | _, _ => panic s!"[revert_NoTn_cutOff_wDepsCache][augment] unexpected formats {x.name} {y.name}")
      (track, res)
  let allFwdDeps : UInt32Array := guFvs.foldl (fun D fv =>
    match fv.name with
    | .num _ i =>
        let d := depsCache[i]!
        D.union d.fTrans
    | _ =>
        panic s!"[allFwdDeps] unexpected formats {fv.name}"
    ) .empty
  -- dbg_trace (s!"[allFwdDeps]\n allFwdDeps {repr allFwdDeps}")
  let rec filterBD (bd done : List FVarId) : List FVarId :=
    match bd with
    | fv@⟨.num _ i⟩ :: more  => if allFwdDeps.oContains i.toUInt32 then filterBD more (fv :: done) else filterBD more done
    | [] => done
    | _ => panic s!"[filterBD] unexpected format"
  let rec close (track : UInt32Array) (final : Array FVarId) (idx : Nat) (pass : List FVarId) : Array FVarId :=
    -- dbg_trace (s!"[close]\n track {repr track}\n final {repr final} \n pass {repr pass}\n idx {repr idx}")
    match pass with
    | [] =>
      let idx := idx+1
      if idx >= final.size
      then final
      else
        let nx := final[idx]!
        match nx.name with
        | .num _ i =>
            let D := filterBD depsCache[i]!.back []
            close track final idx D
        | _ =>
            panic s!"[revert_NoTn_cutOff_wDepsCache][close] unexpected formats {nx.name}"
    | nx :: more =>
      let seen := final.binSearchContains nx (fun x y =>
        match x.name, y.name with
        | .num _ i, .num _ j => i < j -- expects strict order
        | _, _ => panic s!"[revert_NoTn_cutOff_wDepsCache][close] unexpected formats {x.name} {y.name}"
        ) 0 idx
      if seen -- backward dependence must have smaller index, so it suffices to search in [0,idx]
      then close track final idx more
      else
        match nx.name with
        | .num _ i =>
            let D := filterBD depsCache[i]!.back []
            let final := final.binInsert (fun x y =>
                match x.name, y.name with
                | .num _ i, .num _ j => i < j -- expects strict order
                | _, _ => panic s!"[revert_NoTn_cutOff_wDepsCache][close] unexpected formats {x.name} {y.name}"
              ) nx
            close track final (idx+1) (D ++ more)
        | _ =>
            panic s!"[revert_NoTn_cutOff_wDepsCache][close] unexpected formats {nx.name}"
  let rec @[specialize] mkRevs : Array FVarId :=
    if spread == 0
    then
      let res := guFvs.qsort (fun x y =>
        match x.name, y.name with
        | .num _ i, .num _ j => i < j -- increase in dependence ; qsort expects strict order
        | _, _ => panic s!"[revert_NoTn_cutOff_wDepsCache][mkRevs] unexpected formats {x.name} {y.name}")
      let track : UInt32Array :=
        res.foldl (fun A nx =>
          match nx.name with
          | .num _ i =>
              A.push i.toUInt32
          | _ =>
              panic s!"[revert_NoTn_cutOff_wDepsCache][mkRevs] unexpected formats {nx.name}"
          ) (.emptyWithCapacity res.size)
      let ini := res[0]!
      match ini.name with
      | .num _ i =>
          let pass := filterBD depsCache[i]!.back []
          close track res 0 pass
      | _ =>
          panic s!"[revert_NoTn_cutOff_wDepsCache][mkRevs] unexpected formats {ini.name}"
    else
      let (track,res) := augment (UInt32Array.emptyWithCapacity RevCutOff) (.emptyWithCapacity RevCutOff) guFvs.toList []
      let ini := res[0]!
      match ini.name with
        | .num _ i =>
            let pass := filterBD depsCache[i]!.back []
            close track res 0 pass
        | _ =>
            panic s!"[revert_NoTn_cutOff_wDepsCache][mkRevs] unexpected formats {ini.name}"
  let mkRevs := mkRevs
  -- dbg_trace s!"[mkRevs] {repr mkRevs}"
  let rec @[specialize] finalRevs : Array FVarId :=
    (workerDepsCache.foldl ( fun (final, aw) (wfid,wd) =>
      if wd.any (fun w =>
        (aw.contains w) ||
        (match w.name with
         | .num k i => if (k == `g || k == `u) then (if (allFwdDeps.oContains i.toUInt32) then true else guFvs.contains w) else false
         | _ => false ))
      then (final.push wfid, aw.push wfid)
      else (final, aw)
    ) (mkRevs,#[])).1
  do
  mtracing
  let ⟨revGoalT,finalRevsPass,l1,l2⟩ ← goal.abstractLetFvarAll_proofLet l1 l2 depsCache finalRevs
  mtrace on .zero with s!"\n revGoalT {← PpExpr revGoalT l1 l2}\n finalRevsPass {repr finalRevsPass}"
  -- let mv ← mkFreshExprMVarAt l1 l2 revGoalT
  let apFv ← withLCtx l1 l2 <| do finalRevsPass.filterM (fun fvd => do
    match ← fvd.getDecl with
    | .cdecl .. => return true
    | .ldecl _ _ _ T .. =>
        match fvd.name with
        | .num k i => if (k == `g || k == `u) then return depsCache[i]!.proof else isProof T -- case of workers
        | n => panic! s!"[revert_NoTn_cutOff_wDepsCache] unexpected {n}")
  let term := .lam `revertHelp revGoalT (mkAppN (.bvar 0) (apFv.map Expr.fvar)) .default
  return ⟨revGoalT,term,apFv,l1,l2⟩

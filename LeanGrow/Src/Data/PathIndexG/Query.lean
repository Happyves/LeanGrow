/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/


import LeanGrow.Src.Data.PathIndexG.Build


open Lean Meta

variable {IdxCollType : Type _}

inductive ListProd3SigL (α β γ δ: Type _) where
| nil
| sig (_ : ListProd3SigL α β γ δ)
| sigL (_ : IdxCollType) (_ : δ) (_ : ListProd3SigL α β γ δ)
| cons (_ : α) (_ : β) (_ : γ) (_ : ListProd3SigL α β γ δ)
deriving Inhabited, Repr, BEq

def ListProd3SigL.printDBG {α β γ δ: Type _} : @ListProd3SigL IdxCollType α β γ δ → String
  | .nil => "nil"
  | .sig nx => s!"sig <| {nx.printDBG}"
  | .sigL _ _  nx => s!"sigL <| {nx.printDBG}"
  | .cons _ _ _ nx => s!"cons <| {nx.printDBG}"


inductive ListProd3S (α β γ : Type _) where
| nil
| cons (_ : α) (_ : β) (_ : γ) (_ : ListProd3S α β γ)
| consSpe (_ : α) (_ : β) (_ : γ) (_ : ListProd3S α β γ)
deriving Inhabited, Repr, BEq

def ListProd3S.getSpe {α β γ : Type _} : ListProd3S α β γ → OptionProd4 α β γ (ListProd3S α β γ )
  | .nil => .none
  | .cons _ _ _ nx => nx.getSpe
  | .consSpe a b c nx => .some a b c nx



namespace PaInG


@[specialize, inline]
partial def queryCore [Repr IdxCollType]
    (l1 : LocalContext) (l2 : LocalInstances)
    {α : Sort _}
    (unionS : α → α → α)
    (empty? : IdxCollType → Bool) (intersect union : IdxCollType → IdxCollType → IdxCollType)
    (constr : IdxCollType) (state : α)
    (naive? throw? revert? skipP : Bool) (revCount revCountMax : Nat)
    (ankers : ListProd3S IdxCollType (@ListProd3SigL IdxCollType Expr (PaInG IdxCollType) (List FVarId) α) α)
    (todo : @ListProd3SigL IdxCollType Expr (PaInG IdxCollType) (List FVarId) α)
    (revertAct : Expr → (PaInG IdxCollType) → (List FVarId) → IdxCollType → α → LocalContext → LocalInstances → MetaM (Prod5 Bool IdxCollType α LocalContext LocalInstances))
    (tProcess : Expr → (List FVarId) → ListProd IdxCollType (Nat × Nat) → IdxCollType → α → LocalContext → LocalInstances → MetaM (Prod4 IdxCollType α LocalContext LocalInstances) )
    (lProcess : Expr → (List FVarId) → CTrie (ListProd IdxCollType (Nat × Nat)) → IdxCollType → α → LocalContext → LocalInstances → MetaM (Prod4 IdxCollType α LocalContext LocalInstances))
    (appProcess lamProcess allProcess : Expr → Expr → (PaInG IdxCollType) → (PaInG IdxCollType) → IdxCollType → IdxCollType → α → Bool → LocalContext → LocalInstances → MetaM (Prod5 UInt8 IdxCollType α LocalContext LocalInstances))
    (letProcess : Expr → Expr → Expr → (PaInG IdxCollType) → (PaInG IdxCollType) → (PaInG IdxCollType) → IdxCollType → IdxCollType → α → Bool → LocalContext → LocalInstances → MetaM (Prod5 UInt8 IdxCollType α LocalContext LocalInstances))
    (projProcess : Name → Nat → Expr → (CTrie (ListProd IdxCollType (Nat × PaInG IdxCollType))) → IdxCollType → α → Bool → LocalContext → LocalInstances → MetaM (Prod6 UInt8 (OptionProd Expr (PaInG IdxCollType)) IdxCollType α LocalContext LocalInstances))
    (bProcess gProcess uProcess : Nat → ListProd IdxCollType Nat → IdxCollType → α → Bool → LocalContext → LocalInstances → MetaM (Prod5 UInt8 IdxCollType α LocalContext LocalInstances))
    (sProcess : Level → ListProd IdxCollType Level → IdxCollType → α → Bool → LocalContext → LocalInstances → MetaM (Prod5 UInt8 IdxCollType α LocalContext LocalInstances))
    (liProcess : Literal → ListProd IdxCollType Literal → IdxCollType → α → Bool → LocalContext → LocalInstances → MetaM (Prod5 UInt8 IdxCollType α LocalContext LocalInstances))
    (cProcess : Name → List Level → CTrie (ListProd IdxCollType (List Level))→ IdxCollType → α → Bool → LocalContext → LocalInstances → MetaM (Prod5 UInt8 IdxCollType α LocalContext LocalInstances))
    (tnProcess : Nat → Nat → ListProd IdxCollType (Nat × Nat) → (List FVarId) →  (PaInG IdxCollType) → IdxCollType → α → Bool → LocalContext → LocalInstances → MetaM (Prod5 UInt8 IdxCollType α LocalContext LocalInstances))
    (lnProcess : Name → Nat → Nat → CTrie (ListProd IdxCollType (Nat × Nat)) → (List FVarId) → (PaInG IdxCollType) → IdxCollType → α → Bool → LocalContext → LocalInstances → MetaM (Prod5 UInt8 IdxCollType α LocalContext LocalInstances))
    : MetaM (Prod5 UInt8 IdxCollType α LocalContext LocalInstances) :=
    let rec @[specialize] go (l1 : LocalContext) (l2 : LocalInstances)
      (constr : IdxCollType) (state : α) (naive? throw? revert? skipP : Bool) (revCount : Nat)
      (ankers : ListProd3S IdxCollType (ListProd3SigL Expr (PaInG IdxCollType) (List FVarId) α) α)
      (todo : ListProd3SigL Expr (PaInG IdxCollType) (List FVarId) α) : MetaM (Prod5 UInt8 IdxCollType α LocalContext LocalInstances) := do
      mtracing
      if revert?
      then
        mtrace on .zero with s!"[queryCore] entered revert with count {revCount}"
        if revCount > revCountMax
        then
          match ankers.getSpe with
          | .none => return ⟨0,constr,state,l1,l2⟩ --fail state
          | .some constr todo state moreA =>
              go l1 l2 constr state false true false false 0 moreA todo
        else
          match ankers with
          | .nil => return ⟨0,constr,state,l1,l2⟩ --fail state
          | .consSpe constr todo state moreA =>
              go l1 l2 constr state false true false false 0 moreA todo
          | .cons constr todo state moreA =>
              match todo with
              | .nil => return ⟨0,constr,state,l1,l2⟩ --fail state
              | .sig .. | .sigL .. => throwError s!"[queryCore] sig at anker durring revert : should have been freed ; this is a bug"
              | .cons e T workas moreT =>
                  mtrace on .zero with s!"[queryCore] revert constr {repr constr}"
                  mtrace on .zero with s!"[queryCore] revert e {← PpExpr e l1 l2}"
                  mtrace on .zero with s!"[queryCore] revert T {← T.pp l1 l2 workas 0 intersect empty?}"
                  let ⟨fstarg,constr,state,l1,l2⟩ ← revertAct e T workas constr state l1 l2
                  if fstarg
                  then
                    go l1 l2 constr state false true false false 0 moreA moreT
                  else
                    go l1 l2 constr state false true true false (revCount + 1) moreA moreT
      else
        if empty? constr
        then return ⟨0,constr,state,l1,l2⟩ --fail state
        else
          match todo with
          | .nil => return ⟨3,constr,state,l1,l2⟩ --k constr state
          | .sig nx =>
            match ankers with
            | .nil => throwError s!"[queryCore] sig at todo and empty ankers ; this is a bug"
            | .cons _ _ _ more | .consSpe _ _ _ more =>
                mtrace on .one with s!"[queryCore] freed anker"
                go l1 l2 constr state naive? throw? revert? skipP revCount more nx
          | .sigL reI reU nx =>
                mtrace on .one with s!"[queryLCore] reinsering contraints {repr reI}"
                let constr := union reI constr
                let state := unionS state reU -- order matters wrt. `uniUnion` and `embedUnion`
                go l1 l2 constr state naive? throw? revert? skipP revCount ankers nx
          | .cons e T workas moreT =>
              mtrace on .one with s!"[queryCore] call on constr {repr constr}"
              mtrace on .one with s!"[queryCore] call on e {← PpExpr e l1 l2}"
              mtrace on .one with s!"[queryCore] call on T {← T.pp l1 l2 workas 0 intersect empty?}"
              mtrace on .one with s!"[queryCore] naive? {naive?} throw? {throw?} revert? {revert?} "
              match T with
              | .dead => return ⟨1,constr,state,l1,l2⟩ --deadC constr state
              | .br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai alf ala ali lef lea lez lei projs proofsOf proofs =>
                  let ⟨constr,state,l1,l2⟩ ← tProcess e workas tnodes constr state l1 l2
                  let ⟨constr,state,l1,l2⟩ ← lProcess e workas lnodes constr state l1 l2
                  if ← (if !skipP then IsProof e l1 l2 else return false)
                  then
                    let eT ← InferType e l1 l2
                    mtrace on .zero with s!"[queryCore] recognized proof of {← PpExpr eT l1 l2}"
                    go l1 l2 constr state naive? throw? revert? true revCount
                      (.consSpe constr (.cons eT proofsOf workas moreT) state ankers)
                      (.cons e proofs workas <| .sig <| .sigL constr state <| .cons eT proofsOf workas moreT)
                      /- We first try to unify proofs ; the typical case is when the proof will be a node
                      meant for unification, wich we'll want to assign the proof ; if this fails, we
                      revert to the curent stage, and check if the types of the proofs match  ;
                      even if proof unification is successful, for example due to unificaiton with a
                      node, we should still get matches of the types, to not miss terms with different
                      proofs of te same prop ; this requires restoring those candidates -/
                  else
                    match e with
                    | .app f a =>
                        if throw?
                        then
                          mtrace on .zero with s!"[queryCore] app case with thrown anker"
                          go l1 l2 constr state naive? false revert? skipP revCount (.cons constr todo state ankers) (.cons e T workas <| .sig moreT)
                        else
                          let ⟨fstarg,constr,state,l1,l2⟩ ← appProcess f a apf apa api constr state
                            naive? l1 l2
                          if fstarg == 0
                          then return ⟨2,constr,state,l1,l2⟩ -- naiveFail
                          else if fstarg == 1 -- failure in non-naive case : revert
                          then go l1 l2 constr state naive? throw? true skipP revCount ankers todo
                          else -- success, keep `throw?` at false until we reach head
                            go l1 l2 constr state naive? false revert? skipP revCount ankers (.cons f apf workas <| .cons a apa workas <| moreT)
                    | .lam _ f a _ =>
                        let ⟨fstarg,constr,state,l1,l2⟩ ← lamProcess f a laf laa lai constr state
                          naive? l1 l2
                        if fstarg == 0
                        then return ⟨2,constr,state,l1,l2⟩ -- naiveFail
                        else if fstarg == 1 -- failure in non-naive case : revert
                        then go l1 l2 constr state naive? throw? true skipP revCount ankers todo
                        else -- allow throwing,
                          let w ← worker workas.length
                          let ⟨wfv,a,l1,l2⟩ ← withFreeing w f a l1 l2
                          go l1 l2 constr state naive? true revert? skipP revCount ankers (.cons f laf workas <| .cons a laa (wfv :: workas) <| moreT)
                    | .forallE _ f a _ =>
                        let ⟨fstarg,constr,state,l1,l2⟩ ← allProcess f a alf ala ali constr state
                          naive? l1 l2
                        if fstarg == 0
                        then return ⟨2,constr,state,l1,l2⟩ -- naiveFail
                        else if fstarg == 1 -- failure in non-naive case : revert
                        then go l1 l2 constr state naive? throw? true skipP revCount ankers todo
                        else -- allow throwing,
                          let w ← worker workas.length
                          let ⟨wfv,a,l1,l2⟩ ← withFreeing w f a l1 l2
                          go l1 l2 constr state naive? true revert? skipP revCount ankers (.cons f alf workas <| .cons a ala (wfv :: workas) <| moreT)
                    | .letE _ f a z _ =>
                        let ⟨fstarg,constr,state,l1,l2⟩ ← letProcess f a z lef lea lez lei constr state
                          naive? l1 l2
                        if fstarg == 0
                        then return ⟨2,constr,state,l1,l2⟩ -- naiveFail
                        else if fstarg == 1 -- failure in non-naive case : revert
                        then go l1 l2 constr state naive? throw? true skipP revCount ankers todo
                        else -- allow throwing,
                          let w ← worker workas.length
                          let ⟨wfv,z,l1,l2⟩ ← withFreeingLet w f a z l1 l2
                          go l1 l2 constr state naive? true revert? skipP revCount ankers (.cons f lef workas <| .cons a lea workas <| .cons z lez (wfv :: workas) <| moreT)
                    | .proj n i e =>
                        if throw?
                        then
                          mtrace on .zero with s!"[queryCore] proj case with thrown anker"
                          go l1 l2 constr state naive? throw? revert? skipP revCount (.cons constr todo state ankers) (.cons e T workas <| .sig moreT)
                          -- *Note* for the case of `⟨...⟩.1` ; allow to throw inside projected arg
                        else
                          let ⟨fstarg,spe,constr,state,l1,l2⟩ ← projProcess n i e projs constr state
                            naive? l1 l2
                          if fstarg == 0
                          then return ⟨2,constr,state,l1,l2⟩ -- naiveFail
                          else if fstarg == 1 -- failure in non-naive case : revert
                          then go l1 l2 constr state naive? throw? true skipP revCount ankers todo
                          else
                            match spe with
                            | .none => throwError "[queryCore] case mismatch at proj handling"
                            | .some e T =>-- success ; expects proj arg, proj branch tree, workers remain unaffcted
                                go l1 l2 constr state naive? true revert? skipP revCount ankers (.cons e T workas moreT)
                    | .bvar i =>
                        let ⟨fstarg,constr,state,l1,l2⟩ ← bProcess i bvars constr state
                          naive? l1 l2
                        if fstarg == 0
                        then return ⟨2,constr,state,l1,l2⟩ -- naiveFail
                        else if fstarg == 1 -- failure in non-naive case : revert
                        then go l1 l2 constr state naive? throw? true skipP revCount ankers todo
                        else -- success, set `throw?` to true
                          go l1 l2 constr state false true revert? skipP revCount ankers moreT
                    | .sort u =>
                        let ⟨fstarg,constr,state,l1,l2⟩ ← sProcess u sorts constr state
                          naive? l1 l2
                        if fstarg == 0
                        then return ⟨2,constr,state,l1,l2⟩ -- naiveFail
                        else if fstarg == 1 -- failure in non-naive case : revert
                        then go l1 l2 constr state naive? throw? true skipP revCount ankers todo
                        else -- success, set `throw?` to true
                          go l1 l2 constr state false true revert? skipP revCount ankers moreT
                    | .const n l =>
                        let ⟨fstarg,constr,state,l1,l2⟩ ← cProcess n l consts constr state
                          naive? l1 l2
                        if fstarg == 0
                        then return ⟨2,constr,state,l1,l2⟩ -- naiveFail
                        else if fstarg == 1 -- failure in non-naive case : revert
                        then go l1 l2 constr state naive? throw? true skipP revCount ankers todo
                        else -- success, set `throw?` to true
                          go l1 l2 constr state false true revert? skipP revCount ankers moreT
                    | .lit l =>
                        let ⟨fstarg,constr,state,l1,l2⟩ ← liProcess l lits constr state
                          naive? l1 l2
                        if fstarg == 0
                        then return ⟨2,constr,state,l1,l2⟩ -- naiveFail
                        else if fstarg == 1 -- failure in non-naive case : revert
                        then go l1 l2 constr state naive? throw? true skipP revCount ankers todo
                        else -- success, set `throw?` to true
                          go l1 l2 constr state false true revert? skipP revCount ankers moreT
                    | .fvar fid =>
                        match fid.name with
                        | .num (.num _ backIdx) pos =>
                          let ⟨fstarg,constr,state,l1,l2⟩ ← tnProcess backIdx pos tnodes workas T constr state
                            naive? l1 l2
                          if fstarg == 0
                          then return ⟨2,constr,state,l1,l2⟩ -- naiveFail
                          else if fstarg == 1 -- failure in non-naive case : revert
                          then go l1 l2 constr state naive? throw? true skipP revCount ankers todo
                          else -- success, set `throw?` to true
                            go l1 l2 constr state false true revert? skipP revCount ankers moreT
                        | .num (.str _ kind) i =>
                          if kind == "w"
                          then
                            mtrace on .zero with s!"[queryCore] worker fvar {i}, treated at bvar {(workas.length - 1 - i)}"
                            let ⟨fstarg,constr,state,l1,l2⟩ ← bProcess (workas.length - 1 - i) bvars constr state
                              naive? l1 l2
                            if fstarg == 0
                            then return ⟨2,constr,state,l1,l2⟩ -- naiveFail
                            else if fstarg == 1 -- failure in non-naive case : revert
                            then go l1 l2 constr state naive? throw? true skipP revCount ankers todo
                            else -- success, set `throw?` to true
                              go l1 l2 constr state false true revert? skipP revCount ankers moreT
                          else
                            if kind == "g"
                            then
                              let ⟨fstarg,constr,state,l1,l2⟩ ← gProcess i gnodes constr state
                                naive? l1 l2
                              if fstarg == 0
                              then return ⟨2,constr,state,l1,l2⟩ -- naiveFail
                              else if fstarg == 1 -- failure in non-naive case : revert
                              then go l1 l2 constr state naive? throw? true skipP revCount ankers todo
                              else -- success, set `throw?` to true
                                go l1 l2 constr state false true revert? skipP revCount ankers moreT
                            else
                              if kind == "u"
                              then
                                let .some V ← fid.GetValue? l1 l2 | throwError s!"[queryCore] unode {repr fid} without value ?!"
                                let ⟨fstarg,constr,state,l1,l2⟩ ← uProcess i unodes constr state
                                  naive? l1 l2
                                  -- In both cases of unode failure, unfold it and try with the value
                                if fstarg == 0
                                then
                                  mtrace on .zero with s!"[queryCore] trying by unfolding unode {i}"
                                  go l1 l2 constr state naive? throw? revert? skipP revCount ankers (.cons V T workas moreT)
                                else if fstarg == 1 -- failure in non-naive case : revert
                                then
                                  mtrace on .zero with s!"[queryCore] trying by unfolding unode {i}"
                                  go l1 l2 constr state naive? throw? revert? skipP revCount ankers (.cons V T workas moreT)
                                else -- success, set `throw?` to true
                                  go l1 l2 constr state false true revert? skipP revCount ankers moreT
                              else
                                throwError s!"[queryCore] unsupported fvar id {repr fid}"
                        | _ => throwError s!"[queryCore] unsupported fvar id {repr fid}"
                    | .mvar fid =>
                        match fid.name with
                        | .num (.num module Idx) pos =>
                          if module == `t
                          then
                            let ⟨fstarg,constr,state,l1,l2⟩ ← tnProcess Idx pos tnodes workas T constr state
                              naive? l1 l2
                            if fstarg == 0
                            then return ⟨2,constr,state,l1,l2⟩ -- naiveFail
                            else if fstarg == 1 -- failure in non-naive case : revert
                            then go l1 l2 constr state naive? throw? true skipP revCount ankers todo
                            else -- success, set `throw?` to true
                              go l1 l2 constr state false true revert? skipP revCount ankers moreT
                          else
                            let ⟨fstarg,constr,state,l1,l2⟩ ← lnProcess module Idx pos lnodes workas T constr state
                              naive? l1 l2
                            if fstarg == 0
                            then return ⟨2,constr,state,l1,l2⟩ -- naiveFail
                            else if fstarg == 1 -- failure in non-naive case : revert
                            then go l1 l2 constr state naive? throw? true skipP revCount ankers todo
                            else -- success, set `throw?` to true
                              go l1 l2 constr state false true revert? skipP revCount ankers moreT
                        | _ => throwError s!"[queryCore] unsupported mvar id {repr fid}"
                    | .mdata _ e =>
                        go l1 l2 constr state naive? throw? revert? skipP revCount ankers (.cons e T workas moreT)
    go l1 l2 constr state naive? throw? revert? skipP revCount ankers todo


#check 1



@[specialize, inline]
partial def queryLCore [Repr IdxCollType]
    (l1 : LocalContext) (l2 : LocalInstances)
    {α : Sort _}
    (unionS : α → α → α)
    (empty? : IdxCollType → Bool) (intersect union : IdxCollType → IdxCollType → IdxCollType)
    (constr : IdxCollType) (state : α)
    (naive? throw? revert? skipP : Bool) (revCount revCountMax : Nat)
    (ankers : ListProd3S IdxCollType (@ListProd3SigL IdxCollType Expr (PaInG IdxCollType) (List FVarId) α) α)
    (todo : @ListProd3SigL IdxCollType Expr (PaInG IdxCollType) (List FVarId) α)
    (revertAct : Expr → (PaInG IdxCollType) → (List FVarId) → IdxCollType → α → LocalContext → LocalInstances → MetaM (Prod5 Bool IdxCollType α LocalContext LocalInstances))
    (tProcess : Expr → (List FVarId) → ListProd IdxCollType (Nat × Nat) → IdxCollType → α → LocalContext → LocalInstances → MetaM (Prod5 Bool IdxCollType α LocalContext LocalInstances) )
    (lProcess : IdxCollType → α → Expr → (List FVarId) → CTrie (ListProd IdxCollType (Nat × Nat)) → IdxCollType → α → LocalContext → LocalInstances → MetaM (Prod5 Bool IdxCollType α LocalContext LocalInstances))
    (appProcess lamProcess allProcess : Expr → Expr → (PaInG IdxCollType) → (PaInG IdxCollType) → IdxCollType → IdxCollType → α → Bool → LocalContext → LocalInstances → MetaM (Prod5 UInt8 IdxCollType α LocalContext LocalInstances))
    (letProcess : Expr → Expr → Expr → (PaInG IdxCollType) → (PaInG IdxCollType) → (PaInG IdxCollType) → IdxCollType → IdxCollType → α → Bool → LocalContext → LocalInstances → MetaM (Prod5 UInt8 IdxCollType α LocalContext LocalInstances))
    (projProcess : Name → Nat → Expr → (CTrie (ListProd IdxCollType (Nat × PaInG IdxCollType))) → IdxCollType → α → Bool → LocalContext → LocalInstances → MetaM (Prod6 UInt8 (OptionProd Expr (PaInG IdxCollType)) IdxCollType α LocalContext LocalInstances))
    (bProcess gProcess uProcess : Nat → ListProd IdxCollType Nat → IdxCollType → α → Bool → LocalContext → LocalInstances → MetaM (Prod5 UInt8 IdxCollType α LocalContext LocalInstances))
    (sProcess : Level → ListProd IdxCollType Level → IdxCollType → α → Bool → LocalContext → LocalInstances → MetaM (Prod5 UInt8 IdxCollType α LocalContext LocalInstances))
    (liProcess : Literal → ListProd IdxCollType Literal → IdxCollType → α → Bool → LocalContext → LocalInstances → MetaM (Prod5 UInt8 IdxCollType α LocalContext LocalInstances))
    (cProcess : Name → List Level → CTrie (ListProd IdxCollType (List Level))→ IdxCollType → α → Bool → LocalContext → LocalInstances → MetaM (Prod5 UInt8 IdxCollType α LocalContext LocalInstances))
    (tnProcess : Nat → Nat → ListProd IdxCollType (Nat × Nat) → (List FVarId) →  (PaInG IdxCollType) → IdxCollType → α → Bool → LocalContext → LocalInstances → MetaM (Prod5 UInt8 IdxCollType α LocalContext LocalInstances))
    (lnProcess : Name → Nat → Nat → CTrie (ListProd IdxCollType (Nat × Nat)) → (List FVarId) → (PaInG IdxCollType) → IdxCollType → α → Bool → LocalContext → LocalInstances → MetaM (Prod5 UInt8 IdxCollType α LocalContext LocalInstances))
    : MetaM (Prod5 UInt8 IdxCollType α LocalContext LocalInstances) :=
    let rec @[specialize] go (l1 : LocalContext) (l2 : LocalInstances)
      (constr : IdxCollType) (state : α) (naive? throw? revert? skipP : Bool) (revCount : Nat)
      (ankers : ListProd3S IdxCollType (ListProd3SigL Expr (PaInG IdxCollType) (List FVarId) α) α)
      (todo : ListProd3SigL Expr (PaInG IdxCollType) (List FVarId) α) : MetaM (Prod5 UInt8 IdxCollType α LocalContext LocalInstances) := do
      mtracing
      if revert?
      then
        mtrace on .zero with s!"[queryCore] entered revert with count {revCount}"
        if revCount > revCountMax
        then
          match ankers.getSpe with
          | .none => return ⟨0,constr,state,l1,l2⟩ --fail state
          | .some constr todo state moreA =>
              go l1 l2 constr state false true false false 0 moreA todo
        else
          match ankers with
          | .nil => return ⟨0,constr,state,l1,l2⟩ --fail state
          | .consSpe constr todo state moreA =>
              go l1 l2 constr state false true false false 0 moreA todo
          | .cons constr todo state moreA =>
              match todo with
              | .nil => return ⟨0,constr,state,l1,l2⟩ --fail state
              | .sig .. | .sigL .. => throwError s!"[queryCore] sig at anker durring revert : should have been freed ; this is a bug"
              | .cons e T workas moreT =>
                  mtrace on .zero with s!"[queryCore] revert constr {repr constr}"
                  mtrace on .zero with s!"[queryCore] revert e {← PpExpr e l1 l2}"
                  mtrace on .zero with s!"[queryCore] revert T {← T.pp l1 l2 workas 0 intersect empty?}"
                  let ⟨fstarg,constr,state,l1,l2⟩ ← revertAct e T workas constr state l1 l2
                  if fstarg
                  then
                    go l1 l2 constr state false true false false 0 moreA moreT
                  else
                    go l1 l2 constr state false true true false (revCount + 1) moreA moreT
      else
        if empty? constr
        then return ⟨0,constr,state,l1,l2⟩ --fail state
        else
          match todo with
          | .nil => return ⟨3,constr,state,l1,l2⟩ --k constr state
          | .sig nx =>
            match ankers with
            | .nil => throwError s!"[queryCore] sig at todo and empty ankers ; this is a bug"
            | .cons _ _ _ more | .consSpe _ _ _ more =>
                mtrace on .one with s!"[queryCore] freed anker"
                go l1 l2 constr state naive? throw? revert? skipP revCount more nx
          | .sigL reI reU nx =>
                mtrace on .one with s!"[queryLCore] reinsering contraints {repr reI}"
                let constr := union reI constr
                let state := unionS state reU -- order matters wrt. `uniUnion` and `embedUnion`
                go l1 l2 constr state naive? throw? revert? skipP revCount ankers nx
          | .cons e T workas moreT =>
              mtrace on .one with s!"[queryCore] call on constr {repr constr}"
              mtrace on .one with s!"[queryCore] call on e {← PpExpr e l1 l2}"
              mtrace on .one with s!"[queryCore] call on T {← T.pp l1 l2 workas 0 intersect empty?}"
              mtrace on .one with s!"[queryCore] naive? {naive?} throw? {throw?} revert? {revert?} "
              match T with
              | .dead => return ⟨1,constr,state,l1,l2⟩ --deadC constr state
              | .br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai alf ala ali lef lea lez lei projs proofsOf proofs =>
                  let ⟨savef,saveI,saveS,l1,l2⟩ ← tProcess e workas tnodes constr state l1 l2
                  let ⟨saves,saveI,saveS,l1,l2⟩ ← lProcess saveI saveS e workas lnodes constr state l1 l2
                  let save? := savef || saves
                  if ← (if !skipP then IsProof e l1 l2 else return false)
                  then
                    let eT ← InferType e l1 l2
                    mtrace on .zero with s!"[queryCore] recognized proof of {← PpExpr eT l1 l2}"
                    let ankers := if save? then (.consSpe saveI moreT saveS ankers) else ankers
                    let moreT := if save? then .sig moreT else moreT
                    go l1 l2 constr state naive? throw? revert? true revCount
                      (.consSpe constr (.cons eT proofsOf workas moreT) state ankers)
                      (.cons e proofs workas <| .sig <| .sigL saveI saveS <| .cons eT proofsOf workas moreT)
                      /- We first try to unify proofs ; the typical case is when the proof will be a node
                      meant for unification, wich we'll want to assign the proof ; if this fails, we
                      revert to the curent stage, and check if the types of the proofs match  ;
                      even if proof unification is successful, for example due to unificaiton with a
                      node, we should still get matches of the types, to not miss terms with different
                      proofs of te same prop ; this requires restoring those candidates -/
                  else
                    match e with
                    | .app f a =>
                        if throw?
                        then
                          mtrace on .zero with s!"[queryCore] app case with thrown anker"
                          go l1 l2 constr state naive? false revert? skipP revCount (.cons constr todo state ankers) (.cons e T workas <| .sig moreT)
                        else
                          let ⟨fstarg,constr,state,l1,l2⟩ ← appProcess f a apf apa api constr state
                            naive? l1 l2
                          if fstarg == 0
                          then
                            if save?
                            then go l1 l2 saveI saveS false false revert? skipP revCount ankers moreT
                            else return ⟨2,constr,state,l1,l2⟩ -- naiveFail
                          else if fstarg == 1 -- failure in non-naive case : revert
                          then
                            if save?
                            then go l1 l2 saveI saveS false true revert? skipP revCount ankers moreT
                            else go l1 l2 constr state naive? throw? true skipP revCount ankers todo
                          else -- success, keep `throw?` at false until we reach head
                            let ankers := if save? then (.consSpe saveI moreT saveS ankers) else ankers
                            let moreT := if save? then .sig moreT else moreT
                            go l1 l2 constr state naive? false revert? skipP revCount ankers (.cons f apf workas <| .cons a apa workas <| (if save? then .sigL saveI saveS moreT else moreT))
                    | .lam _ f a _ =>
                        let ⟨fstarg,constr,state,l1,l2⟩ ← lamProcess f a laf laa lai constr state
                          naive? l1 l2
                        if fstarg == 0
                        then
                          if save?
                          then go l1 l2 saveI saveS false false revert? skipP revCount ankers moreT
                          else return ⟨2,constr,state,l1,l2⟩ -- naiveFail
                        else if fstarg == 1 -- failure in non-naive case : revert
                        then
                          if save?
                          then go l1 l2 saveI saveS false true revert? skipP revCount ankers moreT
                          else go l1 l2 constr state naive? throw? true skipP revCount ankers todo
                        else -- allow throwing,
                          let w ← worker workas.length
                          let ⟨wfv,a,l1,l2⟩ ← withFreeing w f a l1 l2
                          let ankers := if save? then (.consSpe saveI moreT saveS ankers) else ankers
                          let moreT := if save? then .sig moreT else moreT
                          go l1 l2 constr state naive? true revert? skipP revCount ankers (.cons f laf workas <| .cons a laa (wfv :: workas) <| (if save? then .sigL saveI saveS moreT else moreT))
                    | .forallE _ f a _ =>
                        let ⟨fstarg,constr,state,l1,l2⟩ ← allProcess f a alf ala ali constr state
                          naive? l1 l2
                        if fstarg == 0
                        then
                          if save?
                          then go l1 l2 saveI saveS false false revert? skipP revCount ankers moreT
                          else return ⟨2,constr,state,l1,l2⟩ -- naiveFail
                        else if fstarg == 1 -- failure in non-naive case : revert
                        then
                          if save?
                          then go l1 l2 saveI saveS false true revert? skipP revCount ankers moreT
                          else go l1 l2 constr state naive? throw? true skipP revCount ankers todo
                        else -- allow throwing,
                          let w ← worker workas.length
                          let ⟨wfv,a,l1,l2⟩ ← withFreeing w f a l1 l2
                          let ankers := if save? then (.consSpe saveI moreT saveS ankers) else ankers
                          let moreT := if save? then .sig moreT else moreT
                          go l1 l2 constr state naive? true revert? skipP revCount ankers (.cons f alf workas <| .cons a ala (wfv :: workas) <| (if save? then .sigL saveI saveS moreT else moreT))
                    | .letE _ f a z _ =>
                        let ⟨fstarg,constr,state,l1,l2⟩ ← letProcess f a z lef lea lez lei constr state
                          naive? l1 l2
                        if fstarg == 0
                        then
                          if save?
                          then go l1 l2 saveI saveS false false revert? skipP revCount ankers moreT
                          else return ⟨2,constr,state,l1,l2⟩ -- naiveFail
                        else if fstarg == 1 -- failure in non-naive case : revert
                        then
                          if save?
                          then go l1 l2 saveI saveS false true revert? skipP revCount ankers moreT
                          else go l1 l2 constr state naive? throw? true skipP revCount ankers todo
                        else -- allow throwing,
                          let w ← worker workas.length
                          let ⟨wfv,z,l1,l2⟩ ← withFreeingLet w f a z l1 l2
                          let ankers := if save? then (.consSpe saveI moreT saveS ankers) else ankers
                          let moreT := if save? then .sig moreT else moreT
                          go l1 l2 constr state naive? true revert? skipP revCount ankers (.cons f lef workas <| .cons a lea workas <| .cons z lez (wfv :: workas) <| (if save? then .sigL saveI saveS moreT else moreT))
                    | .proj n i e =>
                        if throw?
                        then
                          mtrace on .zero with s!"[queryCore] proj case with thrown anker"
                          go l1 l2 constr state naive? throw? revert? skipP revCount (.cons constr todo state ankers) (.cons e T workas <| .sig moreT)
                          -- *Note* for the case of `⟨...⟩.1` ; allow to throw inside projected arg
                        else
                          let ⟨fstarg,spe,constr,state,l1,l2⟩ ← projProcess n i e projs constr state
                            naive? l1 l2
                          if fstarg == 0
                          then
                            if save?
                            then go l1 l2 saveI saveS false false revert? skipP revCount ankers moreT
                            else return ⟨2,constr,state,l1,l2⟩ -- naiveFail
                          else if fstarg == 1 -- failure in non-naive case : revert
                          then
                            if save?
                            then go l1 l2 saveI saveS false true revert? skipP revCount ankers moreT
                            else go l1 l2 constr state naive? throw? true skipP revCount ankers todo
                          else
                            match spe with
                            | .none => throwError "[queryCore] case mismatch at proj handling"
                            | .some e T =>-- success ; expects proj arg, proj branch tree, workers remain unaffcted
                                let ankers := if save? then (.consSpe saveI moreT saveS ankers) else ankers
                                let moreT := if save? then .sig moreT else moreT
                                go l1 l2 constr state naive? true revert? skipP revCount ankers (.cons e T workas (if save? then .sigL saveI saveS moreT else moreT))
                    | .bvar i =>
                        let ⟨fstarg,constr,state,l1,l2⟩ ← bProcess i bvars constr state
                          naive? l1 l2
                        if fstarg == 0
                        then
                          if save?
                          then go l1 l2 saveI saveS false false revert? skipP revCount ankers moreT
                          else return ⟨2,constr,state,l1,l2⟩ -- naiveFail
                        else if fstarg == 1 -- failure in non-naive case : revert
                        then
                          if save?
                          then go l1 l2 saveI saveS false true revert? skipP revCount ankers moreT
                          else go l1 l2 constr state naive? throw? true skipP revCount ankers todo
                        else -- success, set `throw?` to true
                          let ankers := if save? then (.consSpe saveI moreT saveS ankers) else ankers
                          let moreT := if save? then .sig moreT else moreT
                          go l1 l2 constr state false true revert? skipP revCount ankers (if save? then .sigL saveI saveS moreT else moreT)
                    | .sort u =>
                        let ⟨fstarg,constr,state,l1,l2⟩ ← sProcess u sorts constr state
                          naive? l1 l2
                        if fstarg == 0
                        then
                          if save?
                          then go l1 l2 saveI saveS false false revert? skipP revCount ankers moreT
                          else return ⟨2,constr,state,l1,l2⟩ -- naiveFail
                        else if fstarg == 1 -- failure in non-naive case : revert
                        then
                          if save?
                          then go l1 l2 saveI saveS false true revert? skipP revCount ankers moreT
                          else go l1 l2 constr state naive? throw? true skipP revCount ankers todo
                        else -- success, set `throw?` to true
                          let ankers := if save? then (.consSpe saveI moreT saveS ankers) else ankers
                          let moreT := if save? then .sig moreT else moreT
                          go l1 l2 constr state false true revert? skipP revCount ankers (if save? then .sigL saveI saveS moreT else moreT)
                    | .const n l =>
                        let ⟨fstarg,constr,state,l1,l2⟩ ← cProcess n l consts constr state
                          naive? l1 l2
                        if fstarg == 0
                        then
                          if save?
                          then go l1 l2 saveI saveS false false revert? skipP revCount ankers moreT
                          else return ⟨2,constr,state,l1,l2⟩ -- naiveFail
                        else if fstarg == 1 -- failure in non-naive case : revert
                        then
                          if save?
                          then go l1 l2 saveI saveS false true revert? skipP revCount ankers moreT
                          else go l1 l2 constr state naive? throw? true skipP revCount ankers todo
                        else -- success, set `throw?` to true
                          let ankers := if save? then (.consSpe saveI moreT saveS ankers) else ankers
                          let moreT := if save? then .sig moreT else moreT
                          go l1 l2 constr state false true revert? skipP revCount ankers (if save? then .sigL saveI saveS moreT else moreT)
                    | .lit l =>
                        let ⟨fstarg,constr,state,l1,l2⟩ ← liProcess l lits constr state
                          naive? l1 l2
                        if fstarg == 0
                        then
                          if save?
                          then go l1 l2 saveI saveS false false revert? skipP revCount ankers moreT
                          else return ⟨2,constr,state,l1,l2⟩ -- naiveFail
                        else if fstarg == 1 -- failure in non-naive case : revert
                        then
                          if save?
                          then go l1 l2 saveI saveS false true revert? skipP revCount ankers moreT
                          else go l1 l2 constr state naive? throw? true skipP revCount ankers todo
                        else -- success, set `throw?` to true
                          let ankers := if save? then (.consSpe saveI moreT saveS ankers) else ankers
                          let moreT := if save? then .sig moreT else moreT
                          go l1 l2 constr state false true revert? skipP revCount ankers (if save? then .sigL saveI saveS moreT else moreT)
                    | .fvar fid =>
                        match fid.name with
                        | .num (.num _ backIdx) pos =>
                          let ⟨fstarg,constr,state,l1,l2⟩ ← tnProcess backIdx pos tnodes workas T constr state
                            naive? l1 l2
                          if fstarg == 0
                          then
                            if save?
                            then go l1 l2 saveI saveS false false revert? skipP revCount ankers moreT
                            else return ⟨2,constr,state,l1,l2⟩ -- naiveFail
                          else if fstarg == 1 -- failure in non-naive case : revert
                          then
                            if save?
                            then go l1 l2 saveI saveS false true revert? skipP revCount ankers moreT
                            else go l1 l2 constr state naive? throw? true skipP revCount ankers todo
                          else -- success, set `throw?` to true
                            let ankers := if save? then (.consSpe saveI moreT saveS ankers) else ankers
                            let moreT := if save? then .sig moreT else moreT
                            go l1 l2 constr state false true revert? skipP revCount ankers (if save? then .sigL saveI saveS moreT else moreT)
                        | .num (.str _ kind) i =>
                          if kind == "w"
                          then
                            mtrace on .zero with s!"[queryCore] worker fvar {i}, treated at bvar {(workas.length - 1 - i)}"
                            let ⟨fstarg,constr,state,l1,l2⟩ ← bProcess (workas.length - 1 - i) bvars constr state
                              naive? l1 l2
                            if fstarg == 0
                            then
                              if save?
                              then go l1 l2 saveI saveS false false revert? skipP revCount ankers moreT
                              else return ⟨2,constr,state,l1,l2⟩ -- naiveFail
                            else if fstarg == 1 -- failure in non-naive case : revert
                            then
                              if save?
                              then go l1 l2 saveI saveS false true revert? skipP revCount ankers moreT
                              else go l1 l2 constr state naive? throw? true skipP revCount ankers todo
                            else -- success, set `throw?` to true
                              let ankers := if save? then (.consSpe saveI moreT saveS ankers) else ankers
                              let moreT := if save? then .sig moreT else moreT
                              go l1 l2 constr state false true revert? skipP revCount ankers (if save? then .sigL saveI saveS moreT else moreT)
                          else
                            if kind == "g"
                            then
                              let ⟨fstarg,constr,state,l1,l2⟩ ← gProcess i gnodes constr state
                                naive? l1 l2
                              if fstarg == 0
                              then
                                if save?
                                then go l1 l2 saveI saveS false false revert? skipP revCount ankers moreT
                                else return ⟨2,constr,state,l1,l2⟩ -- naiveFail
                              else if fstarg == 1 -- failure in non-naive case : revert
                              then
                                if save?
                                then go l1 l2 saveI saveS false true revert? skipP revCount ankers moreT
                                else go l1 l2 constr state naive? throw? true skipP revCount ankers todo
                              else -- success, set `throw?` to true
                                let ankers := if save? then (.consSpe saveI moreT saveS ankers) else ankers
                                let moreT := if save? then .sig moreT else moreT
                                go l1 l2 constr state false true revert? skipP revCount ankers (if save? then .sigL saveI saveS moreT else moreT)
                            else
                              if kind == "u"
                              then
                                let .some V ← fid.GetValue? l1 l2 | throwError s!"[queryCore] unode {repr fid} without value ?!"
                                let ⟨fstarg,constr,state,l1,l2⟩ ← uProcess i unodes constr state
                                  naive? l1 l2
                                  -- In both cases of unode failure, unfold it and try with the value
                                if fstarg == 0
                                then
                                  mtrace on .zero with s!"[queryCore] trying by unfolding unode {i}"
                                  let ankers := if save? then (.consSpe saveI moreT saveS ankers) else ankers
                                  let moreT := if save? then .sig moreT else moreT
                                  go l1 l2 constr state naive? throw? revert? skipP revCount ankers (.cons V T workas moreT)
                                else if fstarg == 1 -- failure in non-naive case : revert
                                then
                                  mtrace on .zero with s!"[queryCore] trying by unfolding unode {i}"
                                  let ankers := if save? then (.consSpe saveI moreT saveS ankers) else ankers
                                  let moreT := if save? then .sig moreT else moreT
                                  go l1 l2 constr state naive? throw? revert? skipP revCount ankers (.cons V T workas moreT)
                                else -- success, set `throw?` to true
                                  let ankers := if save? then (.consSpe saveI moreT saveS ankers) else ankers
                                  let moreT := if save? then .sig moreT else moreT
                                  go l1 l2 constr state false true revert? skipP revCount ankers (if save? then .sigL saveI saveS moreT else moreT)
                              else
                                throwError s!"[queryCore] unsupported fvar id {repr fid}"
                        | _ => throwError s!"[queryCore] unsupported fvar id {repr fid}"
                    | .mvar fid =>
                        match fid.name with
                        | .num (.num module Idx) pos =>
                          if module == `t
                          then
                            let ⟨fstarg,constr,state,l1,l2⟩ ← tnProcess Idx pos tnodes workas T constr state
                              naive? l1 l2
                            if fstarg == 0
                            then
                              if save?
                              then go l1 l2 saveI saveS false false revert? skipP revCount ankers moreT
                              else return ⟨2,constr,state,l1,l2⟩ -- naiveFail
                            else if fstarg == 1 -- failure in non-naive case : revert
                            then
                              if save?
                              then go l1 l2 saveI saveS false true revert? skipP revCount ankers moreT
                              else go l1 l2 constr state naive? throw? true skipP revCount ankers todo
                            else -- success, set `throw?` to true
                              let ankers := if save? then (.consSpe saveI moreT saveS ankers) else ankers
                              let moreT := if save? then .sig moreT else moreT
                              go l1 l2 constr state false true revert? skipP revCount ankers (if save? then .sigL saveI saveS moreT else moreT)
                          else
                            let ⟨fstarg,constr,state,l1,l2⟩ ← lnProcess module Idx pos lnodes workas T constr state
                              naive? l1 l2
                            if fstarg == 0
                            then
                              if save?
                              then go l1 l2 saveI saveS false false revert? skipP revCount ankers moreT
                              else return ⟨2,constr,state,l1,l2⟩ -- naiveFail
                            else if fstarg == 1 -- failure in non-naive case : revert
                            then
                              if save?
                              then go l1 l2 saveI saveS false true revert? skipP revCount ankers moreT
                              else go l1 l2 constr state naive? throw? true skipP revCount ankers todo
                            else -- success, set `throw?` to true
                              let ankers := if save? then (.consSpe saveI moreT saveS ankers) else ankers
                              let moreT := if save? then .sig moreT else moreT
                              go l1 l2 constr state false true revert? skipP revCount ankers (if save? then .sigL saveI saveS moreT else moreT)
                        | _ => throwError s!"[queryCore] unsupported mvar id {repr fid}"
                    | .mdata _ e =>
                        go l1 l2 constr state naive? throw? revert? skipP revCount ankers (.cons e T workas moreT)
    go l1 l2 constr state naive? throw? revert? skipP revCount ankers todo

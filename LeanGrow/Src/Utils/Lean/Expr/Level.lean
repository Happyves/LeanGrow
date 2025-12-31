
/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import Lean.Level
import LeanGrowBeta.Utils.Tracing
import LeanGrowBeta.Data.Amalgames


open Lean Meta


set_option autoImplicit true

-- # onAllSubterms



private inductive AssembleTaskL where
| nil
| max (_ : AssembleTaskL) (post? : Bool)
| imax (_ : AssembleTaskL) (post? : Bool)
| succ (_ : AssembleTaskL)
deriving Inhabited, Repr, BEq



@[specialize f, inline]
partial def Lean.Level.onAllSubtermsTR (e : Level) (f : Level → Level) : Level :=
  trace set TracingFlags.none in
  let rec @[specialize f] go (ta : List Level) (aT : AssembleTaskL) (up? : Bool) : List Level → Level
    | last@([]) =>
      trace on .zero with s!"[onAllSubterms] empty todos ; \n  ta : {repr ta}\n  aT : {repr aT}" in
      match aT with
      | .succ ats =>
        match ta with
        | x :: L => go ((.succ x) :: L) ats up? last
        | _ => .mvar ⟨`failure⟩
      | .max ats false =>
        match ta with
        | x :: y :: L => go ((.max y x) :: L) ats up? last
        | _ => .mvar ⟨`failure⟩
      | .imax ats false =>
        match ta with
        | x :: y :: L => go ((.imax y x) :: L) ats up? last
        | _ => .mvar ⟨`failure⟩
      | .nil =>
        match ta with
        | res :: _ => res
        | _ => .mvar ⟨`failure⟩
      | _ => .mvar ⟨`failure⟩
    | todo@(nx :: more) =>
      trace on .zero with s!"[onAllSubterms] cons todos ; mode up? is {up?}" in
      if up?
      then
        trace on .zero with s!"[onAllSubterms]\n  ta : {repr ta}\n  aT : {repr aT}\n  todo : {repr todo}" in
        match aT with
        | .succ ats =>
          match ta with
          | x :: L => go ((.succ x) :: L) ats up? todo
          | _ => .mvar ⟨`failure⟩
        | .max ats true => go ta (.max ats false) false todo
        | .max ats false =>
          match ta with
          | x :: y :: L => go ((.max y x) :: L) ats up? todo
          | _ => .mvar ⟨`failure⟩
        | .imax ats true => go ta (.imax ats false) false todo
        | .imax ats false =>
          match ta with
          | x :: y :: L => go ((.imax y x) :: L) ats up? todo
          | _ => .mvar ⟨`failure⟩
        | _ => .mvar ⟨`failure⟩
      else
        let here := f nx
        trace on .zero with s!"[onAllSubterms]\n  here : {repr here}\n  ta : {repr ta}\n  aT : {repr aT}\n  todo : {repr todo}" in
        match here with
        | .max l r => go ta (.max aT true) false (l :: r :: more)
        | .imax l r => go ta (.imax aT true) false (l :: r :: more)
        | .succ l => go ta (.succ aT) false (l :: more)
        | _ => go (here :: ta) aT true more
  go [] .nil false [e]




@[specialize f,inline]
partial def Lean.Level.onAllSubtermsMTR  (e : Level) (initD : LocalContext) (initI : LocalInstances)
  (f : Level → LocalContext → LocalInstances → MetaM (Prod3 Level LocalContext LocalInstances)) : MetaM (Prod3 Level LocalContext LocalInstances) :=
  trace set TracingFlags.none in
  let rec @[specialize f] go (initD : LocalContext) (initI : LocalInstances) (ta : List Level) (aT : AssembleTaskL) (up? : Bool) : List Level → MetaM (Prod3 Level LocalContext LocalInstances)
    | last@([]) =>
      trace on .zero with s!"[onAllSubterms] empty todos ; \n  ta : {repr ta}\n  aT : {repr aT}" in
      match aT with
      | .succ ats =>
        match ta with
        | x :: L => go initD initI ((.succ x) :: L) ats up? last
        | _ => return ⟨.mvar ⟨`failure⟩,initD,initI⟩
      | .max ats false =>
        match ta with
        | x :: y :: L => go initD initI ((.max y x) :: L) ats up? last
        | _ => return ⟨.mvar ⟨`failure⟩,initD,initI⟩
      | .imax ats false =>
        match ta with
        | x :: y :: L => go initD initI ((.imax y x) :: L) ats up? last
        | _ => return ⟨.mvar ⟨`failure⟩,initD,initI⟩
      | .nil =>
        match ta with
        | res :: _ => return ⟨res,initD,initI⟩
        | _ => return ⟨.mvar ⟨`failure⟩,initD,initI⟩
      | _ => return ⟨.mvar ⟨`failure⟩,initD,initI⟩
    | todo@(nx :: more) => do
      trace on .zero with s!"[onAllSubterms] cons todos ; mode up? is {up?}" in
      if up?
      then
        trace on .zero with s!"[onAllSubterms]\n  ta : {repr ta}\n  aT : {repr aT}\n  todo : {repr todo}" in
        match aT with
        | .succ ats =>
          match ta with
          | x :: L => go initD initI ((.succ x) :: L) ats up? todo
          | _ => return ⟨.mvar ⟨`failure⟩,initD,initI⟩
        | .max ats true => go initD initI ta (.max ats false) false todo
        | .max ats false =>
          match ta with
          | x :: y :: L => go initD initI ((.max y x) :: L) ats up? todo
          | _ => return ⟨.mvar ⟨`failure⟩,initD,initI⟩
        | .imax ats true => go initD initI ta (.imax ats false) false todo
        | .imax ats false =>
          match ta with
          | x :: y :: L => go initD initI ((.imax y x) :: L) ats up? todo
          | _ => return ⟨.mvar ⟨`failure⟩,initD,initI⟩
        | _ => return ⟨.mvar ⟨`failure⟩,initD,initI⟩
      else do
        let here ← f nx initD initI
        let initD := here.2
        let initI := here.3
        let here := here.1
        trace on .zero with s!"[onAllSubterms]\n  here : {repr here}\n  ta : {repr ta}\n  aT : {repr aT}\n  todo : {repr todo}" in
        match here with
        | .max l r => go initD initI ta (.max aT true) false (l :: r :: more)
        | .imax l r => go initD initI ta (.imax aT true) false (l :: r :: more)
        | .succ l => go initD initI ta (.succ aT) false (l :: more)
        | _ => go initD initI (here :: ta) aT true more
  go initD initI [] .nil false [e]



@[inline]
partial def Lean.Level.EqUpToMVar (a b : Level) : Bool :=
  let rec go : ListProd Level Level → Bool
    | .nil => true
    | .cons x y nx =>
      match x, y with
      | .mvar _ , _ | _, .mvar _ => go nx
      | .max l r, .max l' r' => go <| .cons l l' <| .cons r r' nx
      | .imax l r, .imax l' r' => go <| .cons l l' <| .cons r r' nx
      | .succ l, .succ l' => go <| .cons l l' nx
      | .param u, .param v => if u == v then go nx else false
      | .zero, .zero => go nx
      | _, _ => false
  go <| .cons a b .nil





@[specialize f,inline]
partial def Lean.Level.onAllSubtermsCheckExistsTR (e : Level) (f : Level → Bool) : Bool :=
  let rec @[specialize f] go : List Level → Bool
    | [] => false
    | e :: more =>
      if f e
      then true
      else
        match e with
        | .max l r | .imax l r => go (l :: r :: more)
        | .succ e => go (e :: more)
        | _ => go more
  go [e]

@[specialize f,inline]
partial def Lean.Level.onAllSubtermsgetFirst (e : Level) {α : Sort _} (f : Level → Option α) : Option α :=
  let rec @[specialize f] go : List Level → Option α
    | [] => .none
    | e :: more =>
      match f e with
      | res@(.some ..) => res
      | .none =>
          match e with
          | .max l r | .imax l r => go (l :: r :: more)
          | .succ e => go (e :: more)
          | _ => go more
  go [e]

@[inline]
def Lean.Level.hasTnodes (within : Level) : Bool :=
  within.onAllSubtermsCheckExistsTR (fun | .param (.num (.num ..) ..) => true | _ => false)

@[inline]
def Lean.Level.hasLnodes (within : Level) : Bool :=
  within.onAllSubtermsCheckExistsTR (fun | .mvar ⟨(.num (.num ..) ..)⟩ => true | _ => false)

@[specialize f,inline]
partial def Lean.Level.onAllSubtermsFold (e : Level)
  {α : Sort _} (init : α) (f : Level → α → α) : α :=
  let rec @[specialize f] go (col : α) : List Level → α
    | [] => col
    | e :: more =>
      let here := f e col
      match e with
      | .max l r | .imax l r => go (here) (l :: r :: more)
      | .succ e => go (here)  (e :: more)
      | _ => go (here) more
  go init [e]



@[specialize,inline]
partial def Lean.Level.onAllSubtermsWiWorkerCpsSkipTravState (e : Level) (initD : LocalContext) (initI : LocalInstances) {β: Sort _} (init : β)
  (f : Level → β → LocalContext → LocalInstances → MetaM (Prod4 (Except Level Level) β LocalContext LocalInstances)) : MetaM (Prod4 (Except Level Level) β LocalContext LocalInstances) :=
  trace set TracingFlags.none in
  let rec @[specialize f] go (state : β) (initD : LocalContext) (initI : LocalInstances) (ta : List Level) (aT : AssembleTaskL) (up? : Bool)
  : List Level → MetaM (Prod4 (Except Level Level) β LocalContext LocalInstances)
    | last@(.nil) => do
      trace on .zero with s!"[onAllSubterms] empty todos ; \n  ta : {repr ta}\n  aT : {repr aT}" in
      match aT with
      | .succ ats =>
        match ta with
        | x :: L => go state initD initI ((.succ x) :: L) ats up? last
        | _ => return ⟨.error (.mvar ⟨`failure⟩),state,initD,initI⟩
      | .max ats false =>
        match ta with
        | x :: y :: L => go state initD initI  ((.max y x) :: L) ats up? last
        | _ => return ⟨.error (.mvar ⟨`failure⟩),state,initD,initI⟩
      | .imax ats false =>
        match ta with
        | x :: y :: L => go state initD initI  ((.imax y x) :: L) ats up? last
        | _ => return ⟨.error (.mvar ⟨`failure⟩),state,initD,initI⟩
      | .nil =>
        match ta with
        | res :: _ => return ⟨.ok res,state,initD,initI⟩
        | _ => return ⟨.error (.mvar ⟨`failure⟩),state,initD,initI⟩
      | _ => return ⟨.error (.mvar ⟨`failure⟩),state,initD,initI⟩
    | todo@(nx :: more) => do
      trace on .zero with s!"[onAllSubterms] cons todos ; mode up? is {up?}" in
      if up?
      then
        trace on .zero with s!"[onAllSubterms]\n  ta : {repr ta}\n  aT : {repr aT}\n  todo : {repr todo}" in
        match aT with
        | .succ ats =>
          match ta with
          | x :: L => go state initD initI ((.succ x) :: L) ats up? todo
          | _ => return ⟨.error (.mvar ⟨`failure⟩),state,initD,initI⟩
        | .max ats true => go state initD initI ta (.max ats false) false todo
        | .max ats false =>
          match ta with
          | x :: y :: L => go state initD initI ((.max y x) :: L) ats up? todo
          | _ => return ⟨.error (.mvar ⟨`failure⟩),state,initD,initI⟩
        | .imax ats true => go state initD initI ta (.imax ats false) false todo
        | .imax ats false =>
          match ta with
          | x :: y :: L => go state initD initI ((.imax y x) :: L) ats up? todo
          | _ => return ⟨.error (.mvar ⟨`failure⟩),state,initD,initI⟩
        | _ => return ⟨.error (.mvar ⟨`failure⟩),state,initD,initI⟩
      else do
        let here ← f nx state initD initI
        trace on .zero with s!"[onAllSubterms]\n  here : {repr here}\n  ta : {repr ta}\n  aT : {repr aT}\n  todo : {repr todo}" in
        let initD := here.3
        let initI := here.4
        let state := here.2
        let here := here.1
        match here with
        | .ok here  =>
          match here with
          | .max l r => go state initD initI ta (.max aT true) false (l :: r :: more)
          | .imax l r => go state initD initI ta (.imax aT true) false (l :: r :: more)
          | .succ l => go state initD initI ta (.succ aT) false (l :: more)
          | _ => go state initD initI (here :: ta) aT true more
        | .error here => go state initD initI (here :: ta) aT true more
  go init initD initI [] .nil false [e]

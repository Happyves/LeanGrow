

/-
Copyright (c) 2026 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/


import LeanGrow.Src.Utils.Std.ByteArray
import LeanGrow.Src.Utils.Std.Array
import LeanGrow.Src.Data.Amalgames

import Lean.Meta.Basic

open Lean



inductive CTrie (α : Type _) where
  | leaf : CTrie α
  | fruit : α → CTrie α
  | lnode1 : ByteArray → CTrie α → CTrie α
  | fnode1 : α → ByteArray → CTrie α → CTrie α
  | lnode : Array ByteArray → Array (CTrie α) → CTrie α
  | fnode : α → Array ByteArray → Array (CTrie α) → CTrie α
deriving Inhabited, Repr, BEq


namespace CTrie

variable {α : Sort _}

set_option autoImplicit true


-- # Exmpty and inhabited

def empty : CTrie α := leaf

instance : EmptyCollection (CTrie α) :=
  ⟨empty⟩

instance : Inhabited (CTrie α) where
  default := empty


inductive CTrieZipU (α : Type _) where
  | nil : CTrieZipU α
  | leaf : CTrieZipU α → CTrieZipU α
  | fruit : α → CTrieZipU α → CTrieZipU α
  | lnode1 : ByteArray → CTrieZipU α → CTrieZipU α
  | fnode1 : α → ByteArray → CTrieZipU α → CTrieZipU α
  | lnode : Array ByteArray → Array (CTrie α) → Nat → CTrieZipU α → CTrieZipU α
  | fnode : α → Array ByteArray → Array (CTrie α) → Nat → CTrieZipU α → CTrieZipU α
deriving Inhabited, Repr, BEq



partial def unzip (z : CTrieZipU α) : CTrie α → CTrieZipU α
  | .leaf => .leaf z
  | .fruit v => .fruit v z
  | .lnode1 c t => unzip (.lnode1 c z) t
  | .fnode1 v c t => unzip (.fnode1 v c z) t
  | .lnode cs ts => unzip (.lnode cs ts 0 z) ts[0]!
  | .fnode v cs ts => unzip (.fnode v cs ts 0 z) ts[0]!


partial def cleanUp (t : CTrie α) : CTrieZipU α → CTrie α
  | .nil => t
  | .leaf nx => cleanUp (.leaf) nx
  | .fruit v nx => cleanUp (.fruit v) nx
  | .lnode1 c nx =>
      match t with
      | .leaf => cleanUp t nx
      | .lnode1 c' k => cleanUp (.lnode1 (c ++ c') k) nx
      | _ =>
        if c.isEmpty
        then cleanUp t nx
        else cleanUp (.lnode1 c t) nx
  | .fnode1 v c nx =>
      match t with
      | .leaf => cleanUp (.fruit v) nx
      | .lnode1 c' k => cleanUp (.fnode1 v (c ++ c') k) nx
      | _ => cleanUp (.fnode1 v c t) nx
  | .lnode cs ts idx nx =>
      if idx == ts.size - 1
      then
        let ts := ts.set! idx t
        let (nax,ncx) := clean_inner cs ts [] [] cs.size
        match nax, ncx with
        | [], _ => cleanUp (.leaf) nx
        | [NAX], [NCX] => cleanUp (.lnode1 NAX NCX) nx
        | _, _ => cleanUp (.lnode nax.toArray ncx.toArray) nx
      else
        let ts := ts.set! idx t
        let NX := unzip (.lnode cs ts (idx+1) nx) ts[idx+1]!
        cleanUp t NX
  | .fnode v cs ts idx nx =>
      if idx == ts.size - 1
      then
        let ts := ts.set! idx t
        let (nax,ncx) := clean_inner cs ts [] [] cs.size
        match nax, ncx with
        | [], _ => cleanUp (.fruit v) nx
        | [NAX], [NCX] => cleanUp (.fnode1 v NAX NCX) nx
        | _, _ => cleanUp (.fnode v nax.toArray ncx.toArray) nx
      else
        let ts := ts.set! idx t
        let NX := unzip (.fnode v cs ts (idx+1) nx) ts[idx+1]!
        cleanUp t NX
where
  clean_inner (cs : Array ByteArray) (ts : Array (CTrie α)) (bs : List ByteArray) (Ts : List (CTrie α)) : Nat → List ByteArray × List (CTrie α)
    | 0 => (bs,Ts)
    | n+1 =>
        let X := ts[n]!
        match X with
        | .leaf => clean_inner cs ts bs Ts n
        | _ => clean_inner cs ts ((cs[n]!) :: bs) (X :: Ts) n

@[inline]
def clean (t : CTrie α) : CTrie α :=
  cleanUp t (unzip .nil t)


-- # Find, toList

private inductive upsert_help_type where
  | hit (pos : Nat) (len : Nat)
  | ins (pos : Nat)
deriving Inhabited, BEq, Repr

@[inline]
private def upsert_help (cs : Array ByteArray) (i : Nat) (s : ByteArray) (si : UInt8) : upsert_help_type :=
  let rec go : Nat → upsert_help_type
    | 0 => .ins 0
    | n+1 =>
        let c := (cs[n]!)
        let j := ByteArray.getLongestMatch_wOffset i s c
        if j == 0
        then
          if si < c.get! 0
          then go n
          else .ins (n+1)
        else .hit n j
  go cs.size


def find?.go (s : ByteArray) (i : Nat) : CTrie α → Option α
    | .leaf => .none
    | .fruit v => v
    | .lnode1 c t =>
          if i = s.size
          then .none
          else
            let j := ByteArray.getLongestMatch_wOffset i s c
            if j == c.size
            then find?.go s (i+j) t
            else .none
    | .fnode1 v c t =>
          if i = s.size
          then v
          else
            let j := ByteArray.getLongestMatch_wOffset i s c
            if j == c.size
            then find?.go s (i+j) t
            else .none
    | .lnode cs ts =>
          if i = s.size
          then .none
          else
            match CTrie.upsert_help cs i s (s.get! i) with
            | .ins _ => .none
            | .hit idx len =>
                  if len == (cs[idx]!).size
                  then find?.go s (i+len) (ts[idx]!)
                  else .none
    | .fnode v cs ts =>
          if i = s.size
          then v
          else
            match CTrie.upsert_help cs i s (s.get! i) with
            | .ins _ => .none
            | .hit idx len =>
                  if len == (cs[idx]!).size
                  then find?.go s (i+len) (ts[idx]!)
                  else .none
termination_by _ => s.size - i
decreasing_by
  · sorry
  · sorry
  · sorry -- requires that CTries have nonempty discri bytearrays at nodes ...
  · sorry




def find? (t : CTrie α) (s : ByteArray) : Option α :=
  find?.go s 0 t


example (t : CTrie α) (s : ByteArray) {a}
  (h : t.find? s = .some a)
  : t.clean.find? s = .some a := by
    revert h
    apply @CTrie.rec _
      (fun t => t.find? s = .some a → t.clean.find? s = .some a)
      (fun _ => True) (fun _ => True)
    · intro h
      dsimp [CTrie.find?] at h
      unfold CTrie.find?.go at h
      contradiction
    all_goals sorry

#check CTrie.find?.go.eq_1

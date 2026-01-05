
/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import LeanGrow.Src.Utils.Std.ByteArray
import LeanGrow.Src.Utils.Std.Array
import LeanGrow.Src.Data.Amalgames

import Lean.Meta.Basic

open Lean

-- Based on Joachim Breitners implementation in Loogle

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





-- # Upsert, insert, delete, ofList


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


inductive CTrieZip (α : Type _) where
  | nil : CTrieZip α
  | lnode1 : ByteArray → CTrieZip α → CTrieZip α
  | fnode1 : α → ByteArray → CTrieZip α → CTrieZip α
  | lnode : Array ByteArray → Array (CTrie α) → Nat → CTrieZip α → CTrieZip α
  | fnode : α → Array ByteArray → Array (CTrie α) → Nat → CTrieZip α → CTrieZip α
deriving Inhabited, Repr, BEq


private partial def ZipIt (zip : CTrie α) : CTrieZip α → CTrie α
  | .nil => zip
  | .lnode1 c nx => ZipIt (.lnode1 c zip) nx
  | .fnode1 v c nx => ZipIt (.fnode1 v c zip) nx
  | .lnode cs ts idx nx => ZipIt (.lnode cs (ts.set! idx zip)) nx
  | .fnode v cs ts idx nx => ZipIt (.fnode v cs (ts.set! idx zip)) nx


@[specialize]
private partial def upsertMimp [Monad m] (s : ByteArray)(mod : Option α → m (Option α)) (i : Nat) (zip : CTrieZip α) : CTrie α → m (CTrie α)
  | b@(.leaf) => do
      if i < s.size
      then
        match ← mod .none with
        | .some new =>
            let final := .lnode1 (s.drop i) (.fruit new)
            return ZipIt final zip
        | .none =>
            let final := b
            return ZipIt final zip
      else
        match ← mod .none with
        | .some new =>
            let final := .fruit new
            return ZipIt final zip
        | .none =>
            let final := b
            return ZipIt final zip
  | b@(.fruit v) => do
      if i < s.size
      then
        match ← mod .none with
        | .some new =>
            let final := .fnode1 v (s.drop i) (.fruit new)
            return ZipIt final zip
        | .none =>
            let final := b
            return ZipIt final zip
      else
        match ← mod v with
        | .some new =>
            let final := .fruit new
            return ZipIt final zip
        | .none =>
            let final := .leaf
            return ZipIt final zip
  | b@(.lnode1 c t) => do
      if i < s.size
      then
        let j := ByteArray.getLongestMatch_wOffset i s c
        let sum := (i+j)
        if j == c.size
        then
          upsertMimp s mod sum (.lnode1 c zip) t
        else
          match ← mod .none with
          | .some new =>
              if sum == s.size
              then
                let final := .lnode1 (c.take j) (.fnode1 new (c.drop j) t)
                return ZipIt final zip
              else
                let nc := c.drop j
                let add := s.drop sum
                let join := c.take j
                if c.get! j < s.get! sum
                then
                  let final := .lnode1 join (.lnode #[nc,add] #[t,(.fruit new)])
                  return ZipIt final zip
                else
                  let final := .lnode1 join (.lnode #[add,nc] #[(.fruit new),t])
                  return ZipIt final zip
          | .none =>
              let final := b
              return ZipIt final zip
      else
        match ← mod .none with
        | .some new =>
            let final := .fnode1 new c t
            return ZipIt final zip
        | .none =>
            let final := b
            return ZipIt final zip
  | b@(.fnode1 v c t) => do
      if i < s.size
      then
        let j := ByteArray.getLongestMatch_wOffset i s c
        let sum := (i+j)
        if j == c.size
        then
          upsertMimp s mod sum (.fnode1 v c zip) t
        else
          match ← mod .none with
          | .some new =>
              if sum == s.size
              then
                let final := .fnode1 v (c.take j) (.fnode1 new (c.drop j) t)
                return ZipIt final zip
              else
                let nc := c.drop j
                let add := s.drop sum
                let join := c.take j
                if c.get! j < s.get! sum
                then
                  let final := .fnode1 v join (.lnode #[nc,add] #[t,(.fruit new)])
                  return ZipIt final zip
                else
                  let final := .fnode1 v join (.lnode #[add,nc] #[(.fruit new),t])
                  return ZipIt final zip
          | .none =>
              let final := b
              return ZipIt final zip
      else
        match ← mod v with
        | .some new =>
            let final := .fnode1 new c t
            return ZipIt final zip
        | .none =>
            let final := .lnode1 c t
            return ZipIt final zip
  | b@(.lnode cs ts) => do
      if i < s.size
      then
        match CTrie.upsert_help cs i s (s.get! i) with
        | .ins pos =>
            match ← mod .none with
            | .some new =>
                let final := .lnode (cs.insertIdx! pos (s.drop i)) (ts.insertIdx! pos (.fruit new))
                return ZipIt final zip
            | .none =>
                let final := b
                return ZipIt final zip
        | .hit idx len =>
            let c := (cs[idx]!)
            let sum := (i+len)
            if len == c.size
            then
              let t := ts[idx]!
              upsertMimp s mod sum (.lnode cs ts idx zip) t
              --.node v cs (ts.modify idx ((go sum)))
            else
              match ← mod .none with
              | .some new =>
                  if sum == s.size
                  then
                    let final := .lnode ((cs.modify idx (fun _ => c.take len))) (ts.modify idx (fun t => .fnode1 new (c.drop len) t))
                    return ZipIt final zip
                  else
                    let nc := c.drop len
                    let add := s.drop sum
                    let join := c.take len
                    if c.get! len < s.get! sum
                    then
                      let final := .lnode ((cs.modify idx (fun _ => join))) (ts.modify idx (fun t => .lnode #[nc,add] #[t,(.fruit new)]))
                      return ZipIt final zip
                    else
                      let final := .lnode ((cs.modify idx (fun _ => join))) (ts.modify idx (fun t => .lnode #[add,nc] #[(.fruit new),t]))
                      return ZipIt final zip
              | .none =>
                  let final := b
                  return ZipIt final zip
      else
        match ← mod .none with
        | .some new =>
            let final := .fnode new cs ts
            return ZipIt final zip
        | .none =>
            let final := b
            return ZipIt final zip
  | b@(.fnode v cs ts) => do
      if i < s.size
      then
        match CTrie.upsert_help cs i s (s.get! i) with
        | .ins pos =>
            match ← mod .none with
            | .some new =>
                let final := .fnode v (cs.insertIdx! pos (s.drop i)) (ts.insertIdx! pos (.fruit new))
                return ZipIt final zip
            | .none =>
                let final := b
                return ZipIt final zip
        | .hit idx len =>
            let c := (cs[idx]!)
            let sum := (i+len)
            if len == c.size
            then
              let t := ts[idx]!
              upsertMimp s mod sum (.fnode v cs ts idx zip) t
              --.node v cs (ts.modify idx ((go sum)))
            else
              match ← mod .none with
              | .some new =>
                  if sum == s.size
                  then
                    let final := .fnode v ((cs.modify idx (fun _ => c.take len))) (ts.modify idx (fun t => .fnode1 new (c.drop len) t))
                    return ZipIt final zip
                  else
                    let nc := c.drop len
                    let add := s.drop sum
                    let join := c.take len
                    if c.get! len < s.get! sum
                    then
                      let final := .fnode v ((cs.modify idx (fun _ => join))) (ts.modify idx (fun t => .lnode #[nc,add] #[t,(.fruit new)]))
                      return ZipIt final zip
                    else
                      let final := .fnode v ((cs.modify idx (fun _ => join))) (ts.modify idx (fun t => .lnode #[add,nc] #[(.fruit new),t]))
                      return ZipIt final zip
              | .none =>
                  let final := b
                  return ZipIt final zip
      else
        match ← mod v with
        | .some new =>
            let final := .fnode new cs ts
            return ZipIt final zip
        | .none =>
            let final := .lnode cs ts
            return ZipIt final zip


@[specialize, inline]
def upsertM [Monad m] (s : ByteArray) (mod : Option α → m (Option α)) (t : CTrie α) : m (CTrie α) :=
  upsertMimp s mod 0 .nil t

@[specialize, inline]
def upsert (s : ByteArray) (mod : Option α → (Option α)) (t : CTrie α) : CTrie α :=
  Id.run <| upsertMimp s mod 0 .nil t


@[specialize]
private partial def upsertLimp (l1 : LocalContext) (l2 : LocalInstances) (s : ByteArray)
  (mod : Option α → LocalContext → LocalInstances →  MetaM (Prod3 (Option α) LocalContext LocalInstances))
  (i : Nat) (zip : CTrieZip α) : CTrie α → MetaM (Prod3 (CTrie α) LocalContext LocalInstances)
  | b@(.leaf) => do
      if i < s.size
      then
        let ⟨moded,l1,l2⟩ ← mod .none l1 l2
        match moded with
        | .some new =>
            let final := .lnode1 (s.drop i) (.fruit new)
            return ⟨ZipIt final zip,l1,l2⟩
        | .none =>
            let final := b
            return ⟨ZipIt final zip,l1,l2⟩
      else
        let ⟨moded,l1,l2⟩ ← mod .none l1 l2
        match moded with
        | .some new =>
            let final := .fruit new
            return ⟨ZipIt final zip,l1,l2⟩
        | .none =>
            let final := b
            return ⟨ZipIt final zip,l1,l2⟩
  | b@(.fruit v) => do
      if i < s.size
      then
        let ⟨moded,l1,l2⟩ ← mod .none l1 l2
        match moded with
        | .some new =>
            let final := .fnode1 v (s.drop i) (.fruit new)
            return ⟨ZipIt final zip,l1,l2⟩
        | .none =>
            let final := b
            return ⟨ZipIt final zip,l1,l2⟩
      else
        let ⟨moded,l1,l2⟩ ← mod v l1 l2
        match moded with
        | .some new =>
            let final := .fruit new
            return ⟨ZipIt final zip,l1,l2⟩
        | .none =>
            let final := .leaf
            return ⟨ZipIt final zip,l1,l2⟩
  | b@(.lnode1 c t) => do
      if i < s.size
      then
        let j := ByteArray.getLongestMatch_wOffset i s c
        let sum := (i+j)
        if j == c.size
        then
          upsertLimp l1 l2 s mod sum (.lnode1 c zip) t
        else
          let ⟨moded,l1,l2⟩ ← mod .none l1 l2
          match moded with
          | .some new =>
              if sum == s.size
              then
                let final := .lnode1 (c.take j) (.fnode1 new (c.drop j) t)
                return ⟨ZipIt final zip,l1,l2⟩
              else
                let nc := c.drop j
                let add := s.drop sum
                let join := c.take j
                if c.get! j < s.get! sum
                then
                  let final := .lnode1 join (.lnode #[nc,add] #[t,(.fruit new)])
                  return ⟨ZipIt final zip,l1,l2⟩
                else
                  let final := .lnode1 join (.lnode #[add,nc] #[(.fruit new),t])
                  return ⟨ZipIt final zip,l1,l2⟩
          | .none =>
              let final := b
              return ⟨ZipIt final zip,l1,l2⟩
      else
        let ⟨moded,l1,l2⟩ ← mod .none l1 l2
        match moded with
        | .some new =>
            let final := .fnode1 new c t
            return ⟨ZipIt final zip,l1,l2⟩
        | .none =>
            let final := b
            return ⟨ZipIt final zip,l1,l2⟩
  | b@(.fnode1 v c t) => do
      if i < s.size
      then
        let j := ByteArray.getLongestMatch_wOffset i s c
        let sum := (i+j)
        if j == c.size
        then
          upsertLimp l1 l2 s mod sum (.fnode1 v c zip) t
        else
          let ⟨moded,l1,l2⟩ ← mod .none l1 l2
          match moded with
          | .some new =>
              if sum == s.size
              then
                let final := .fnode1 v (c.take j) (.fnode1 new (c.drop j) t)
                return ⟨ZipIt final zip,l1,l2⟩
              else
                let nc := c.drop j
                let add := s.drop sum
                let join := c.take j
                if c.get! j < s.get! sum
                then
                  let final := .fnode1 v join (.lnode #[nc,add] #[t,(.fruit new)])
                  return ⟨ZipIt final zip,l1,l2⟩
                else
                  let final := .fnode1 v join (.lnode #[add,nc] #[(.fruit new),t])
                  return ⟨ZipIt final zip,l1,l2⟩
          | .none =>
              let final := b
              return ⟨ZipIt final zip,l1,l2⟩
      else
        let ⟨moded,l1,l2⟩ ← mod v l1 l2
        match moded with
        | .some new =>
            let final := .fnode1 new c t
            return ⟨ZipIt final zip,l1,l2⟩
        | .none =>
            let final := .lnode1 c t
            return ⟨ZipIt final zip,l1,l2⟩
  | b@(.lnode cs ts) => do
      if i < s.size
      then
        match CTrie.upsert_help cs i s (s.get! i) with
        | .ins pos =>
            let ⟨moded,l1,l2⟩ ← mod .none l1 l2
            match moded with
            | .some new =>
                let final := .lnode (cs.insertIdx! pos (s.drop i)) (ts.insertIdx! pos (.fruit new))
                return ⟨ZipIt final zip,l1,l2⟩
            | .none =>
                let final := b
                return ⟨ZipIt final zip,l1,l2⟩
        | .hit idx len =>
            let c := (cs[idx]!)
            let sum := (i+len)
            if len == c.size
            then
              let t := ts[idx]!
              upsertLimp l1 l2 s mod sum (.lnode cs ts idx zip) t
              --.node v cs (ts.modify idx ((go sum)))
            else
              let ⟨moded,l1,l2⟩ ← mod .none l1 l2
              match moded with
              | .some new =>
                  if sum == s.size
                  then
                    let final := .lnode ((cs.modify idx (fun _ => c.take len))) (ts.modify idx (fun t => .fnode1 new (c.drop len) t))
                    return ⟨ZipIt final zip,l1,l2⟩
                  else
                    let nc := c.drop len
                    let add := s.drop sum
                    let join := c.take len
                    if c.get! len < s.get! sum
                    then
                      let final := .lnode ((cs.modify idx (fun _ => join))) (ts.modify idx (fun t => .lnode #[nc,add] #[t,(.fruit new)]))
                      return ⟨ZipIt final zip,l1,l2⟩
                    else
                      let final := .lnode ((cs.modify idx (fun _ => join))) (ts.modify idx (fun t => .lnode #[add,nc] #[(.fruit new),t]))
                      return ⟨ZipIt final zip,l1,l2⟩
              | .none =>
                  let final := b
                  return ⟨ZipIt final zip,l1,l2⟩
      else
        let ⟨moded,l1,l2⟩ ← mod .none l1 l2
        match moded with
        | .some new =>
            let final := .fnode new cs ts
            return ⟨ZipIt final zip,l1,l2⟩
        | .none =>
            let final := b
            return ⟨ZipIt final zip,l1,l2⟩
  | b@(.fnode v cs ts) => do
      if i < s.size
      then
        match CTrie.upsert_help cs i s (s.get! i) with
        | .ins pos =>
            let ⟨moded,l1,l2⟩ ← mod .none l1 l2
            match moded with
            | .some new =>
                let final := .fnode v (cs.insertIdx! pos (s.drop i)) (ts.insertIdx! pos (.fruit new))
                return ⟨ZipIt final zip,l1,l2⟩
            | .none =>
                let final := b
                return ⟨ZipIt final zip,l1,l2⟩
        | .hit idx len =>
            let c := (cs[idx]!)
            let sum := (i+len)
            if len == c.size
            then
              let t := ts[idx]!
              upsertLimp l1 l2 s mod sum (.fnode v cs ts idx zip) t
              --.node v cs (ts.modify idx ((go sum)))
            else
              let ⟨moded,l1,l2⟩ ← mod .none l1 l2
              match moded with
              | .some new =>
                  if sum == s.size
                  then
                    let final := .fnode v ((cs.modify idx (fun _ => c.take len))) (ts.modify idx (fun t => .fnode1 new (c.drop len) t))
                    return ⟨ZipIt final zip,l1,l2⟩
                  else
                    let nc := c.drop len
                    let add := s.drop sum
                    let join := c.take len
                    if c.get! len < s.get! sum
                    then
                      let final := .fnode v ((cs.modify idx (fun _ => join))) (ts.modify idx (fun t => .lnode #[nc,add] #[t,(.fruit new)]))
                      return ⟨ZipIt final zip,l1,l2⟩
                    else
                      let final := .fnode v ((cs.modify idx (fun _ => join))) (ts.modify idx (fun t => .lnode #[add,nc] #[(.fruit new),t]))
                      return ⟨ZipIt final zip,l1,l2⟩
              | .none =>
                  let final := b
                  return ⟨ZipIt final zip,l1,l2⟩
      else
        let ⟨moded,l1,l2⟩ ← mod v l1 l2
        match moded with
        | .some new =>
            let final := .fnode new cs ts
            return ⟨ZipIt final zip,l1,l2⟩
        | .none =>
            let final := .lnode cs ts
            return ⟨ZipIt final zip,l1,l2⟩


@[specialize, inline]
def upsertL
  (l1 : LocalContext) (l2 : LocalInstances) (s : ByteArray)
  (mod : Option α → LocalContext → LocalInstances →  MetaM (Prod3 (Option α) LocalContext LocalInstances))
  (t : CTrie α) : MetaM (Prod3 (CTrie α) LocalContext LocalInstances) :=
  upsertLimp l1 l2 s mod 0 .nil t


#check Meta.withLocalDecl
#check ReaderT.adapt


@[specialize]
private partial def upsertMcpsImp [Monad m] (s : ByteArray)
  {β : Type _} [Inhabited β]
  (f : Option α → (Option α → m β) → m β)
  (k : (CTrie α) → m β)
  (i : Nat) (zip : CTrieZip α) : CTrie α → m β
  | b@(.leaf) =>
      if i < s.size
      then
        f .none <| fun
          | .some res => do
              let final := .lnode1 (s.drop i) (.fruit res)
              k <| ZipIt final zip
          | .none => do
              let final := b
              k <| ZipIt final zip
      else
        f .none <| fun
          | .some res => do
              let final := .fruit res
              k <| ZipIt final zip
          | .none => do
              let final := b
              k <| ZipIt final zip
  | b@(.fruit v) =>
      if i < s.size
      then
        f .none <| fun
          | .some res => do
              let final := .fnode1 v (s.drop i) (.fruit res)
              k <| ZipIt final zip
          | .none => do
              let final := b
              k <| ZipIt final zip
      else
        f (.some v) <| fun
          | .some res => do
              let final := .fruit res
              k <| ZipIt final zip
          | .none => do
              let final := .leaf
              k <| ZipIt final zip

  | b@(.lnode1 c t) => do
      if i < s.size
      then
        let j := ByteArray.getLongestMatch_wOffset i s c
        let sum := (i+j)
        if j == c.size
        then
          upsertMcpsImp s f k sum (.lnode1 c zip) t
        else
          if sum == s.size
          then
            f .none <| fun
              | .some new => do
                  let final := .lnode1 (c.take j) (.fnode1 new (c.drop j) t)
                  k <| ZipIt final zip
              | .none => do
                  let final := b
                  k <| ZipIt final zip
          else
            let nc := c.drop j
            let add := s.drop sum
            let join := c.take j
            if c.get! j < s.get! sum
            then
              f .none <| fun
                | .some new => do
                    let final := .lnode1 join (.lnode #[nc,add] #[t,(.fruit new)])
                    k <| ZipIt final zip
                | .none => do
                    let final := b
                    k <| ZipIt final zip
            else
              f .none <| fun
                | .some new => do
                    let final := .lnode1 join (.lnode #[add,nc] #[(.fruit new),t])
                    k <| ZipIt final zip
                | .none => do
                    let final := b
                    k <| ZipIt final zip
      else
        f .none <| fun
          | .some new => do
              let final := .fnode1 new c t
              k <| ZipIt final zip
          | .none => do
              let final := b
              k <| ZipIt final zip
  | b@(.fnode1 v c t) => do
      if i < s.size
      then
        let j := ByteArray.getLongestMatch_wOffset i s c
        let sum := (i+j)
        if j == c.size
        then
          upsertMcpsImp s f k sum (.fnode1 v c zip) t
        else
          if sum == s.size
          then
            f .none <| fun
              | .some new => do
                  let final := .fnode1 v (c.take j) (.fnode1 new (c.drop j) t)
                  k <| ZipIt final zip
              | .none => do
                  let final := b
                  k <| ZipIt final zip
          else
            let nc := c.drop j
            let add := s.drop sum
            let join := c.take j
            if c.get! j < s.get! sum
            then
              f .none <| fun
                | .some new => do
                    let final := .fnode1 v join (.lnode #[nc,add] #[t,(.fruit new)])
                    k <| ZipIt final zip
                | .none => do
                    let final := b
                    k <| ZipIt final zip
            else
              f .none <| fun
                | .some new => do
                    let final := .fnode1 v join (.lnode #[add,nc] #[(.fruit new),t])
                    k <| ZipIt final zip
                | .none => do
                    let final := b
                    k <| ZipIt final zip
      else
        f (.some v) <| fun
          | .some new => do
              let final := .fnode1 new c t
              k <| ZipIt final zip
          | .none => do
              let final := .lnode1 c t
              k <| ZipIt final zip
  | b@(.lnode cs ts) => do
      if i < s.size
      then
        match CTrie.upsert_help cs i s (s.get! i) with
        | .ins pos =>
            f .none <| fun
              | .some new => do
                  let final := .lnode (cs.insertIdx! pos (s.drop i)) (ts.insertIdx! pos (.fruit new))
                  k <| ZipIt final zip
              | .none =>
                  let final := b
                  k <| ZipIt final zip
        | .hit idx len =>
            let c := (cs[idx]!)
            let sum := (i+len)
            if len == c.size
            then
              let t := ts[idx]!
              upsertMcpsImp s f k sum (.lnode cs ts idx zip) t
            else
              if sum == s.size
              then
                f .none <| fun
                  | .some new => do
                    let final := .lnode ((cs.modify idx (fun _ => c.take len))) (ts.modify idx (fun t => .fnode1 new (c.drop len) t))
                    k <| ZipIt final zip
                  | .none => do
                    let final := b
                    k <| ZipIt final zip
              else
                let nc := c.drop len
                let add := s.drop sum
                let join := c.take len
                if c.get! len < s.get! sum
                then
                  f .none <| fun
                    | .some new => do
                      let final := .lnode ((cs.modify idx (fun _ => join))) (ts.modify idx (fun t => .lnode #[nc,add] #[t,(.fruit new)]))
                      k <| ZipIt final zip
                    | .none => do
                      let final := b
                      k <| ZipIt final zip
                else
                  f .none <| fun
                    | .some new => do
                      let final := .lnode ((cs.modify idx (fun _ => join))) (ts.modify idx (fun t => .lnode #[add,nc] #[(.fruit new),t]))
                      k <| ZipIt final zip
                    | .none => do
                      let final := b
                      k <| ZipIt final zip
      else
        f .none <| fun
          | .some new => do
            let final := .fnode new cs ts
            k <| ZipIt final zip
          | .none => do
            let final := b
            k <| ZipIt final zip
  | b@(.fnode v cs ts) => do
      if i < s.size
      then
        match CTrie.upsert_help cs i s (s.get! i) with
        | .ins pos =>
            f .none <| fun
              | .some new => do
                  let final := .fnode v (cs.insertIdx! pos (s.drop i)) (ts.insertIdx! pos (.fruit new))
                  k <| ZipIt final zip
              | .none =>
                  let final := b
                  k <| ZipIt final zip
        | .hit idx len =>
            let c := (cs[idx]!)
            let sum := (i+len)
            if len == c.size
            then
              let t := ts[idx]!
              upsertMcpsImp s f k sum (.fnode v cs ts idx zip) t
            else
              if sum == s.size
              then
                f .none <| fun
                  | .some new => do
                    let final := .fnode v ((cs.modify idx (fun _ => c.take len))) (ts.modify idx (fun t => .fnode1 new (c.drop len) t))
                    k <| ZipIt final zip
                  | .none => do
                    let final := b
                    k <| ZipIt final zip
              else
                let nc := c.drop len
                let add := s.drop sum
                let join := c.take len
                if c.get! len < s.get! sum
                then
                  f .none <| fun
                    | .some new => do
                      let final := .fnode v ((cs.modify idx (fun _ => join))) (ts.modify idx (fun t => .lnode #[nc,add] #[t,(.fruit new)]))
                      k <| ZipIt final zip
                    | .none => do
                      let final := b
                      k <| ZipIt final zip
                else
                  f .none <| fun
                    | .some new => do
                      let final := .fnode v ((cs.modify idx (fun _ => join))) (ts.modify idx (fun t => .lnode #[add,nc] #[(.fruit new),t]))
                      k <| ZipIt final zip
                    | .none => do
                      let final := b
                      k <| ZipIt final zip
      else
        f v <| fun
          | .some new => do
            let final := .fnode new cs ts
            k <| ZipIt final zip
          | .none => do
            let final := .lnode cs ts
            k <| ZipIt final zip


@[specialize, inline]
def upsertMcps [Monad m] (s : ByteArray) (t : CTrie α) {β : Type u_2}
  [Inhabited β] (f : Option α → (Option α → m β) → m β) (k : CTrie α → m β) : m β :=
  upsertMcpsImp s f k 0 .nil t

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
      | _ => cleanUp (.lnode1 c t) nx
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


@[inline]
def insert (t : CTrie α) (s : ByteArray) (val : α) : CTrie α :=
  t.upsert (s) (fun _ => .some val)

@[inline]
def delete (t : CTrie α) (s : ByteArray)  : CTrie α :=
  clean <| t.upsert s (fun _ => .none)

def ofList : ListProd String α → CTrie α
  | .nil => CTrie.empty
  | .cons s v more => CTrie.insert (CTrie.ofList more) s.toUTF8 v

def ofListKeys : List Name → CTrie Unit
  | .nil => CTrie.empty
  | .cons s more => CTrie.insert (CTrie.ofListKeys more) s.toString.toUTF8 ()



-- # Find, toList


partial def find? (t : CTrie α) (s : ByteArray) : Option α :=
  let rec go (i : Nat) : CTrie α → Option α
    | .leaf => .none
    | .fruit v => v
    | .lnode1 c t =>
          if i = s.size
          then .none
          else
            let j := ByteArray.getLongestMatch_wOffset i s c
            if j == c.size
            then go (i+j) t
            else .none
    | .fnode1 v c t =>
          if i = s.size
          then v
          else
            let j := ByteArray.getLongestMatch_wOffset i s c
            if j == c.size
            then go (i+j) t
            else .none
    | .lnode cs ts =>
          if i = s.size
          then .none
          else
            match CTrie.upsert_help cs i s (s.get! i) with
            | .ins _ => .none
            | .hit idx len =>
                  if len == (cs[idx]!).size
                  then go (i+len) (ts[idx]!)
                  else .none
    | .fnode v cs ts =>
          if i = s.size
          then v
          else
            match CTrie.upsert_help cs i s (s.get! i) with
            | .ins _ => .none
            | .hit idx len =>
                  if len == (cs[idx]!).size
                  then go (i+len) (ts[idx]!)
                  else .none
  go 0 t



@[inline]
partial def prefixMapZipAppend
  (pre : ByteArray) (ax : Array ByteArray) (cx : Array (CTrie α)) (more : ListProd ByteArray (CTrie α)) :
  ListProd ByteArray (CTrie α) :=
  let pred := (ax.map (pre ++ ·))
  let rec go (sofar : ListProd ByteArray (CTrie α)) (i : Nat) : ListProd ByteArray (CTrie α) :=
    let ent_ba := pred[i]!
    let ent_ct := cx[i]!
    if i == 0
    then .cons ent_ba ent_ct sofar
    else go (.cons ent_ba ent_ct sofar) (i-1)
  if cx.isEmpty
  then more
  else go more (cx.size - 1)



partial def toList (t : CTrie α) : ListProd String α :=
  let rec go (done : ListProd String α) : ListProd ByteArray (CTrie α) → ListProd String α
    | .nil => done
    | .cons pre nx more =>
      match nx with
      | .fruit v => go (.cons (String.fromUTF8! pre) v done) more
      | .leaf => go done more
      | .fnode1 v ax cx =>
          let next := .cons (pre ++ ax) cx more
          go (.cons (String.fromUTF8! pre) v done) next
      | .lnode1 ax cx =>
          let next := .cons (pre ++ ax) cx more
          go done next
      | .fnode v ax cx =>
          let next := prefixMapZipAppend pre ax cx more
          go (.cons (String.fromUTF8! pre) v done) next
      | .lnode ax cx =>
          let next := prefixMapZipAppend pre ax cx more
          go done next
  go .nil (.cons (⟨#[]⟩) t .nil)



-- # Map, fold


#check CTrieZipU


inductive CTrieZipM (α β: Type _) where
  | nil : CTrieZipM α β
  | leaf : CTrieZipM α β → CTrieZipM α β
  | fruit : β → CTrieZipM α β → CTrieZipM α β
  | lnode1 : ByteArray → CTrieZipM α β → CTrieZipM α β
  | fnode1 : β → ByteArray → CTrieZipM α β → CTrieZipM α β
  | lnode : Array ByteArray → Array (CTrie α) → Array (CTrie β) → Nat → CTrieZipM α β → CTrieZipM α β
  | fnode : β → Array ByteArray → Array (CTrie α) → Array (CTrie β) → Nat → CTrieZipM α β → CTrieZipM α β
deriving Inhabited, Repr, BEq


@[specialize]
partial def unzipMap {β : Type _} [Monad m] (z : CTrieZipM  α β) (f : α → m (Option β)) (t : CTrie α) : m (CTrieZipM α β) :=
  match  t with
  | .leaf => return .leaf z
  | .fruit v => do
      let v ← f (v)
      match v with
      | .some v => return .fruit (v) z
      | .none => return .leaf z
  | .lnode1 c t => unzipMap (.lnode1 c z) f t
  | .fnode1 v c t => do
      let v ← f (v)
      match v with
      | .some v => unzipMap (.fnode1 v c z) f t
      | _ => unzipMap (.lnode1 c z) f t
  | .lnode cs ts => unzipMap (.lnode cs ts (Array.replicate ts.size .leaf) 0 z) f ts[0]!
  | .fnode v cs ts => do
      let v ← f ( v)
      match v with
      | .some v => unzipMap (.fnode (v) cs ts (Array.replicate ts.size .leaf) 0 z) f ts[0]!
      | _ => unzipMap (.lnode cs ts (Array.replicate ts.size .leaf) 0 z) f ts[0]!


#check Array.forIn'Unsafe


@[specialize]
partial def mapMimpl {β : Sort _} [Monad m] (t : CTrie β) (z : CTrieZipM α β) (f : α → m (Option β)) : m (CTrie β) :=
  match z with
  | .nil => return t
  | .leaf nx => mapMimpl (.leaf) nx f
  | .fruit v nx => mapMimpl (.fruit v) nx f
  | .lnode1 c nx => mapMimpl (.lnode1 c t) nx f
  | .fnode1 v c nx => mapMimpl (.fnode1 v c t) nx f
  | .lnode cs ts Ts idx nx => do
      if idx == ts.size - 1
      then
        let Ts := Ts.set! idx t
        mapMimpl (.lnode cs Ts) nx f
      else
        let Ts := Ts.set! idx t
        let NX ← unzipMap (.lnode cs ts Ts (idx+1) nx) f ts[idx+1]!
        mapMimpl t NX f
  | .fnode v cs ts Ts idx nx => do
      if idx == ts.size - 1
      then
        let Ts := Ts.set! idx t
        mapMimpl (.fnode v cs Ts) nx f
      else
        let Ts := Ts.set! idx t
        let NX ← unzipMap (.fnode v cs ts Ts (idx+1) nx) f ts[idx+1]!
        mapMimpl t NX f
-- #exit

/-- Don't forget to `clean` if `f` performs deletions-/
@[specialize, inline]
partial def mapM {β : Sort _}  [Monad m] (t : CTrie α) (f : α → m (Option β)) : m (CTrie β) :=
  do mapMimpl .leaf (← unzipMap .nil f t) f

/-- Don't forget to `clean` if `f` performs deletions-/
@[specialize, inline]
partial def map {β : Sort _} (t : CTrie α) (f : α → Option β) : CTrie β :=
  Id.run <| mapM t f



@[specialize]
partial def unzipMcps {β γ : Type _} [Inhabited γ] [Monad m] (z : CTrieZipM  α β) (t : CTrie α)
  (f : α → (Option β → m γ) →  m γ) (k : CTrieZipM  α β → m γ) : m γ  :=
    match t with
    | .leaf => k <| .leaf z
    | .fruit v => do
        f v <| fun v =>
          match v with
          | .some v => k <| .fruit (v) z
          | .none => k <| .leaf z
    | .lnode1 c t => unzipMcps (.lnode1 c z) t f k
    | .fnode1 v c t => do
        f v <| fun v =>
          match v with
          | .some v => unzipMcps (.fnode1 v c z) t f k
          | _ => unzipMcps (.lnode1 c z) t f k
    | .lnode cs ts => unzipMcps (.lnode cs ts (Array.replicate ts.size .leaf) 0 z) ts[0]! f k
    | .fnode v cs ts => do
        f v <| fun v =>
          match v with
          | .some v => unzipMcps (.fnode (v) cs ts (Array.replicate ts.size .leaf) 0 z) ts[0]! f k
          | _ => unzipMcps (.lnode cs ts (Array.replicate ts.size .leaf) 0 z) ts[0]! f k

@[specialize]
partial def mapMcpsImpl {β : Type _} [Inhabited γ] [Monad m] (t : CTrie β) (z : CTrieZipM α β)
  (f : α → (Option β → m γ) →  m γ) (k : CTrie β → m γ) : m γ  :=
  match z with
  | .nil => k <| t
  | .leaf nx => mapMcpsImpl (.leaf) nx f k
  | .fruit v nx => mapMcpsImpl (.fruit v) nx f k
  | .lnode1 c nx => mapMcpsImpl (.lnode1 c t) nx f k
  | .fnode1 v c nx => mapMcpsImpl (.fnode1 v c t) nx f k
  | .lnode cs ts Ts idx nx => do
      if idx == ts.size - 1
      then
        let Ts := Ts.set! idx t
        mapMcpsImpl (.lnode cs Ts) nx f k
      else
        let Ts := Ts.set! idx t
        unzipMcps (.lnode cs ts Ts (idx+1) nx) ts[idx+1]! f <| fun NX =>
          mapMcpsImpl t NX f k
  | .fnode v cs ts Ts idx nx => do
      if idx == ts.size - 1
      then
        let Ts := Ts.set! idx t
        mapMcpsImpl (.fnode v cs Ts) nx f k
      else
        let Ts := Ts.set! idx t
        unzipMcps (.fnode v cs ts Ts (idx+1) nx) ts[idx+1]! f <| fun NX =>
          mapMcpsImpl t NX f k



/-- Don't forget to `clean` if `f` performs deletions-/
@[specialize, inline]
partial def mapMcps {β γ : Sort _} [Monad m] [Inhabited γ] (t : CTrie α)
  (f : α → (Option β → m γ) →  m γ) (k : CTrie β → m γ) : m γ  :=
    unzipMcps .nil t f <| fun sta =>
      mapMcpsImpl .leaf sta f k


#check Array.shrink
#check ByteArray.shrink


inductive foldT (α : Type _) where
| nil : foldT α
| node1 (sz : Nat) (nx : foldT α) : foldT α
| node (sz idx : Nat) (cs : Array ByteArray) (ts : Array (CTrie α)) (nx : foldT α) : foldT α
deriving Inhabited


mutual

@[specialize]
partial def foldMdown {β : Type _} [Monad m] (z : foldT α) (t : CTrie α) (init : β)
  (key : ByteArray) (f : ByteArray → α → β → m β) : m β :=
  match t with
  | .leaf => foldMup z init key f
  | .fruit v => do foldMup z (← f key v init) key f
  | .lnode1 c t => foldMdown (.node1 key.size z) t init (key ++ c) f
  | .fnode1 v c t => do foldMdown (.node1 key.size z) t (← f key v init) (key ++ c) f
  | .lnode cs ts => foldMdown (.node key.size 0 cs ts z) ts[0]! init (key ++ cs[0]!) f
  | .fnode v cs ts => do foldMdown (.node key.size 0 cs ts z) ts[0]! (← f key v init) (key ++ cs[0]!) f

@[specialize]
partial def foldMup {β : Type _} [Monad m] (t : foldT α) (init : β)
  (key : ByteArray) (f : ByteArray → α → β → m β) : m β :=
  match t with
  | .nil => return init
  | .node1 sz nx => foldMup nx init (key.shrink sz) f
  | .node sz idx cs ts nx =>
      if idx == cs.size - 1
      then
        foldMup nx init (key.shrink sz) f
      else
        foldMdown (.node sz (idx+1) cs ts nx) ts[idx+1]! init ((key.shrink sz) ++ cs[idx+1]!) f

end

@[specialize, inline]
partial def foldM {β : Type _} [Monad m] (t : CTrie α) (init : β) (f : ByteArray → α → β → m β) : m β :=
  foldMdown .nil t init {} f

@[specialize, inline]
partial def fold {β : Type _} (t : CTrie α) (init : β) (f : ByteArray → α → β → β) : β :=
  Id.run <| foldMdown .nil t init {} f


mutual

@[specialize]
partial def foldMcpsDown {β γ : Type _} [Inhabited γ] [Monad m] (z : foldT α) (t : CTrie α) (init : β)
  (key : ByteArray) (f : ByteArray → α → β → (β → m γ) → m γ) (k : β → m γ) : m γ :=
  match t with
  | .leaf => foldMcpsUp z init key f k
  | .fruit v => f key v init <| fun init => do foldMcpsUp z init key f k
  | .lnode1 c t => foldMcpsDown (.node1 key.size z) t init (key ++ c) f k
  | .fnode1 v c t => f key v init <| fun init => do foldMcpsDown (.node1 key.size z) t init (key ++ c) f k
  | .lnode cs ts => foldMcpsDown (.node key.size 0 cs ts z) ts[0]! init (key ++ cs[0]!) f k
  | .fnode v cs ts => f key v init <| fun init => do foldMcpsDown (.node key.size 0 cs ts z) ts[0]! init (key ++ cs[0]!) f k

@[specialize]
partial def foldMcpsUp {β γ : Type _} [Inhabited γ] [Monad m] (t : foldT α) (init : β)
  (key : ByteArray) (f : ByteArray → α → β → (β → m γ) → m γ) (k : β → m γ) : m γ :=
  match t with
  | .nil => k <| init
  | .node1 sz nx => foldMcpsUp nx init (key.shrink sz) f k
  | .node sz idx cs ts nx =>
      if idx == cs.size - 1
      then
        foldMcpsUp nx init (key.shrink sz) f k
      else
        foldMcpsDown (.node sz (idx+1) cs ts nx) ts[idx+1]! init ((key.shrink sz) ++ cs[idx+1]!) f k

end

@[specialize, inline]
partial def foldMcps {β : Type _} [Inhabited γ] [Monad m] (t : CTrie α) (init : β)
  (f : ByteArray → α → β → (β → m γ) → m γ) (k : β → m γ) : m γ :=
    foldMcpsDown .nil t init {} f k


@[specialize]
partial def foldMapMimplDown {α β γ : Type u} [Monad m] (init : γ)
  (z : CTrieZipM α β) (f : α → γ → m (γ × Option β)) (t : CTrie α) : m (γ × CTrieZipM α β) :=
  match  t with
  | .leaf => return (init, .leaf z)
  | .fruit v => do
      let (init, v) ← f (v) init
      match v with
      | .some v => return (init, .fruit (v) z)
      | .none => return (init, .leaf z)
  | .lnode1 c t => foldMapMimplDown init (.lnode1 c z) f t
  | .fnode1 v c t => do
      let (init, v) ← f (v) init
      match v with
      | .some v => foldMapMimplDown init (.fnode1 v c z) f t
      | _ => foldMapMimplDown init (.lnode1 c z) f t
  | .lnode cs ts => foldMapMimplDown init (.lnode cs ts (Array.replicate ts.size .leaf) 0 z) f ts[0]!
  | .fnode v cs ts => do
      let (init, v) ← f ( v) init
      match v with
      | .some v => foldMapMimplDown init (.fnode (v) cs ts (Array.replicate ts.size .leaf) 0 z) f ts[0]!
      | _ => foldMapMimplDown init (.lnode cs ts (Array.replicate ts.size .leaf) 0 z) f ts[0]!



@[specialize]
partial def foldMapMimplUp {α β γ : Type u} [Monad m] (init : γ)
  (t : CTrie β) (z : CTrieZipM α β) (f : α → γ → m (γ × Option β)) : m (γ × CTrie β) :=
  match z with
  | .nil => return (init, t)
  | .leaf nx => foldMapMimplUp init (.leaf) nx f
  | .fruit v nx => foldMapMimplUp init (.fruit v) nx f
  | .lnode1 c nx => foldMapMimplUp init (.lnode1 c t) nx f
  | .fnode1 v c nx => foldMapMimplUp init (.fnode1 v c t) nx f
  | .lnode cs ts Ts idx nx => do
      if idx == ts.size - 1
      then
        let Ts := Ts.set! idx t
        foldMapMimplUp init (.lnode cs Ts) nx f
      else
        let Ts := Ts.set! idx t
        let (init, NX) ← foldMapMimplDown init (.lnode cs ts Ts (idx+1) nx) f ts[idx+1]!
        foldMapMimplUp init t NX f
  | .fnode v cs ts Ts idx nx => do
      if idx == ts.size - 1
      then
        let Ts := Ts.set! idx t
        foldMapMimplUp init (.fnode v cs Ts) nx f
      else
        let Ts := Ts.set! idx t
        let (init, NX) ← foldMapMimplDown init (.fnode v cs ts Ts (idx+1) nx) f ts[idx+1]!
        foldMapMimplUp init t NX f
-- #exit

/-- Don't forget to `clean` if `f` performs deletions-/
@[specialize, inline]
partial def foldMapM {α β γ: Type u}  [Monad m] (init : γ) (t : CTrie α) (f : α → γ → m (γ × Option β)) : m (γ × CTrie β) :=
  do
    let (init,res) := (← foldMapMimplDown init .nil f t)
    foldMapMimplUp init .leaf res f

/-- Don't forget to `clean` if `f` performs deletions-/
@[specialize, inline]
partial def foldMap {α β γ: Type u} (init : γ) (t : CTrie α) (f : α → γ → (γ × Option β)) : (γ × CTrie β) :=
  Id.run <| foldMapM init t f


/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import Lean.Data.PersistentHashMap

set_option autoImplicit true

open Lean PersistentHashMap

namespace Lean.PersistentHashMap



partial def print {_ : BEq α} {_ : Hashable α} [Repr α] [Repr β] (hm : PersistentHashMap α β) : String :=
  let rec go : Node α β → String
    | .collision ks vs _ => s!" collision {repr ks} {repr vs}"
    | .entries es =>
        let gone := es.map <| fun
          | .null => " null"
          | .ref n => s!" ref ({go n})"
          | .entry k v => s!" entry {repr k} {repr v}"
        gone.foldl (fun R s => R ++ s) ""
  go hm.root


partial def updateAtCollisionNodeAux [BEq α] : CollisionNode α β → Nat → α → (β → β) → CollisionNode α β
  | n@⟨Node.collision keys vals heq, _⟩, i, k, v =>
    if h : i < keys.size then
      let k' := keys[i];
      if k == k' then
         let j : Fin vals.size := ⟨i, by rw [←heq]; assumption⟩
         let nv := v (vals[j])
         ⟨Node.collision (keys.set i k) (vals.set j nv) (by rw [Array.size_set,Array.size_set] ; exact heq), IsCollisionNode.mk _ _ _⟩
      else updateAtCollisionNodeAux n (i+1) k v
    else
      n
  | ⟨Node.entries _, h⟩, _, _, _ => nomatch h

def updateAtCollisionNode [BEq α] : CollisionNode α β → α → (β → β) → CollisionNode α β :=
  fun n k v => updateAtCollisionNodeAux n 0 k v


partial def updateAux [BEq α] [Hashable α] : Node α β → USize → USize → α → (β → β) → Node α β
  | Node.collision keys vals heq, _, depth, k, v =>
    let newNode := updateAtCollisionNode ⟨Node.collision keys vals heq, IsCollisionNode.mk _ _ _⟩ k v
    if depth >= maxDepth || getCollisionNodeSize newNode < maxCollisions then newNode.val
    else match newNode with
      | ⟨Node.entries _, h⟩ => nomatch h
      | ⟨Node.collision keys vals heq, _⟩ =>
        let rec traverse (i : Nat) (entries : Node α β) : Node α β :=
          if h : i < keys.size then
            let k := keys[i]
            have : i < vals.size := heq ▸ h
            let v := vals[i]
            let h := hash k |>.toUSize
            let h := div2Shift h (shift * (depth - 1))
            traverse (i+1) (insertAux entries h depth k v)
          else
            entries
        traverse 0 mkEmptyEntries
  | Node.entries entries, h, depth, k, v =>
    let j     := (mod2Shift h shift).toNat
    Node.entries $ entries.modify j fun entry =>
      match entry with
      | Entry.null        => entry
      | Entry.ref node    => Entry.ref $ updateAux node (div2Shift h shift) (depth+1) k v
      | Entry.entry k' v' =>
        if k == k' then Entry.entry k (v v')
        else entry

def update {_ : BEq α} {_ : Hashable α} : PersistentHashMap α β → α → (β → β) → PersistentHashMap α β
  | { root }, k, v => { root := updateAux root (hash k |>.toUSize) 1 k v }

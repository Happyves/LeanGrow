
/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import LeanGrow.Src.Data.CTrie.Basic
import LeanGrow.Src.Utils.Tracing


open Lean CTrie

set_option autoImplicit true

namespace CTrie



partial def find_max (T : CTrie Nat) : OptionProd ByteArray Nat :=
  let rec go (sofar : OptionProd ByteArray Nat) : ListProd ByteArray (CTrie Nat) → OptionProd ByteArray Nat
    | .nil => sofar
    | .cons nx1 nx2 more =>
        match nx2 with
        | .leaf => go sofar more
        | .fruit v =>
              match sofar with
              | .some _ w2 =>
                  if v > w2
                  then go (.some (nx1) v) more
                  else go sofar more
              | .none => go (.some ( nx1) v) more
        | .lnode1 a t => go sofar (.cons (nx1 ++ a) t more)
        | .fnode1 v a t =>
              match sofar with
              | .some _ w2 =>
                  if v > w2
                  then go (.some (nx1) v) (.cons (nx1 ++ a) t more)
                  else go sofar (.cons (nx1 ++ a) t more)
              | .none => go (.some (nx1) v) (.cons (nx1 ++ a) t more)
        | .lnode as ts => go sofar (prefixMapZipAppend nx1 as ts more)
        | .fnode v as ts =>
              match sofar with
              | .some _ w2 =>
                  if v > w2
                  then go (.some ( nx1) v) (prefixMapZipAppend nx1 as ts more)
                  else go sofar (prefixMapZipAppend nx1 as ts more)
              | .none => go (.some ( nx1) v) (prefixMapZipAppend nx1 as ts more)
  go .none <| .cons (⟨#[]⟩) T .nil


partial def find_maxes (T : CTrie Nat) : OptionProd (CTrie Unit) Nat :=
  let rec go (sofar : OptionProd (CTrie Unit) Nat) : ListProd ByteArray (CTrie Nat) → OptionProd (CTrie Unit) Nat
    | .nil => sofar
    | .cons nx1 nx2 more =>
        match nx2 with
        | .leaf  => go sofar more
        | .fruit v =>
              match sofar with
              | .some w1 w2 =>
                  match compare v w2 with
                  | .gt => go (.some (.lnode1 nx1 (.fruit ())) v) more
                  | .eq => go (.some (w1.upsert nx1 (fun _ => ())) v) more
                  | .lt => go sofar more
              | .none => go (.some (.lnode1 nx1 (.fruit ())) v) more
        | .lnode1 a t => go sofar (.cons (nx1 ++ a) t more)
        | .fnode1 v a t =>
              match sofar with
              | .some w1 w2 =>
                  match compare v w2 with
                  | .gt => go (.some (.lnode1 nx1 (.fruit ())) v) (.cons (nx1 ++ a) t more)
                  | .eq => go (.some (w1.upsert nx1 (fun _ => ())) v) (.cons (nx1 ++ a) t more)
                  | .lt => go sofar (.cons (nx1 ++ a) t more)
              | .none => go (.some (.lnode1 nx1 (.fruit ())) v) (.cons (nx1 ++ a) t more)
        | .lnode as ts => go sofar (prefixMapZipAppend nx1 as ts more)
        | .fnode v as ts =>
              match sofar with
              | .some w1 w2 =>
                  match compare v w2 with
                  | .gt => go (.some (.lnode1 nx1 (.fruit ())) v) (prefixMapZipAppend nx1 as ts more)
                  | .eq => go (.some (w1.upsert nx1 (fun _ => ())) v) (prefixMapZipAppend nx1 as ts more)
                  | .lt => go sofar (prefixMapZipAppend nx1 as ts more)
              | .none => go (.some (.lnode1 nx1 (.fruit ())) v) (prefixMapZipAppend nx1 as ts more)
  go .none (.cons ⟨#[]⟩ T .nil)



inductive CTrieZipI (α : Type _) where
  | nil : CTrieZipI α
  | leaf : CTrieZipI α → CTrieZipI α
  | fruit : α → CTrieZipI α → CTrieZipI α
  | lnode1 : ByteArray → CTrieZipI α → CTrieZipI α
  | fnode1 : α → ByteArray → CTrieZipI α → CTrieZipI α
  | lnode : Array ByteArray → Array (Prod4 (CTrie α) (CTrie α) Nat Nat) → Array (CTrie α) → Nat → CTrieZipI α → CTrieZipI α
  | fnode : α → Array ByteArray → Array (Prod4 (CTrie α) (CTrie α) Nat Nat) → Array (CTrie α) → Nat → CTrieZipI α → CTrieZipI α
deriving Inhabited, Repr, BEq



@[specialize]
partial def intersectImplDown (merge : α → α → α) (done : CTrieZipI α) (l r : CTrie α) (ol or : Nat) : CTrieZipI α :=
  match l, r with
  | .leaf, _ | _, .leaf => (.leaf done)
  | .fruit v,  .fruit u | .fruit v,  .fnode u .. | .fnode v ..,  .fruit u => (.fruit (merge v u) done)
  | .fruit v,  .fnode1 u .. => if or == 0 then (.fruit (merge v u) done) else (.leaf done)
  | .fnode1 v ..,  .fruit u => if ol == 0 then (.fruit (merge v u) done) else (.leaf done)
  | .fruit .., _ | _, .fruit .. => (.leaf done)
  | .lnode1 ax cx, .lnode1 ay cy | .lnode1 ax cx, .fnode1 _ ay cy | .fnode1 _ ax cx, .lnode1 ay cy =>
      let com := ByteArray.getLongestMatch_wOffsets ax ay ol or
      if ol + com == ax.size
      then
        if or + com == ay.size
        then
          intersectImplDown merge (.lnode1 (ay.drop or) done) cx cy 0 0
        else
          intersectImplDown merge (.lnode1 (ax.drop ol) done) cx r 0 (or + com)
      else
        if or + com == ay.size
        then
          intersectImplDown merge (.lnode1 (ay.drop or) done) l cy (ol + com) 0
        else
          (.leaf done)
  | .fnode1 v ax cx, .fnode1 w ay cy =>
      let com := ByteArray.getLongestMatch_wOffsets ax ay ol or
      if ol + com == ax.size
      then
        if or + com == ay.size
        then
          intersectImplDown merge (.fnode1 (merge v w) (ay.drop or) done) cx cy 0 0
        else
          intersectImplDown merge (.fnode1 (merge v w) (ax.drop ol) done) cx r 0 (or + com)
      else
        if or + com == ay.size
        then
          intersectImplDown merge (.fnode1 (merge v w) (ay.drop or) done) l cy (ol + com) 0
        else
          if or == 0 && ol == 0 then (.fruit (merge v w) done) else (.leaf done)
  | .lnode1 ax cx, .fnode _ ay cy | .fnode1 _ ax cx, .lnode ay cy | .lnode1 ax cx, .lnode ay cy =>
      match ByteArray.matchSingle_wOffset ax ol ay with
      | .none => (.leaf done)
      | .some idx =>
          let ay' := ay[idx]!
          let cy' := cy[idx]!
          let com := ByteArray.getLongestMatch_wOffsets ax ay' ol 0
          if ol + com == ax.size
          then
            if com == ay'.size
            then
              intersectImplDown merge (.lnode1 (ax.drop ol) done) cx cy' 0 0
            else
              intersectImplDown merge (.lnode1 (ax.drop ol) done) cx (.lnode1 ay' cy') 0 com
          else
            if com == ay.size
            then
              intersectImplDown merge (.lnode1 ay' done) l cy' (ol+com) 0
            else
              (.leaf done)
  | .fnode1 v ax cx, .fnode w ay cy =>
      match ByteArray.matchSingle_wOffset ax ol ay with
      | .none => if ol == 0 then (.fruit (merge v w) done) else (.leaf done)
      | .some idx =>
          let ay' := ay[idx]!
          let cy' := cy[idx]!
          let com := ByteArray.getLongestMatch_wOffsets ax ay' ol 0
          if ol + com == ax.size
          then
            if com == ay'.size
            then
              intersectImplDown merge (.fnode1 (merge v w) (ax.drop ol) done) cx cy' 0 0
            else
              intersectImplDown merge (.fnode1 (merge v w) (ax.drop ol) done) cx (.lnode1 ay' cy') 0 com
          else
            if com == ay.size
            then
              intersectImplDown merge (.fnode1 (merge v w) ay' done) l cy' (ol+com) 0
            else
              if ol == 0 then (.fruit (merge v w) done) else (.leaf done)
  | .lnode ax cx, .fnode1 _ ay cy | .fnode _ ax cx, .lnode1 ay cy | .lnode ax cx, .lnode1 ay cy =>
      match ByteArray.matchSingle_wOffset ay or ax with
      | .none => (.leaf done)
      | .some idx =>
          let ax' := ax[idx]!
          let cx' := cx[idx]!
          let com := ByteArray.getLongestMatch_wOffsets ax' ay 0 or
          if com == ax'.size
          then
            if ax'.size == ay.size
            then
              intersectImplDown merge (.lnode1 ax' done) cx' cy 0 0
            else
              intersectImplDown merge (.lnode1 ax' done) cx' r 0 (or + com)
          else
            if or + com == ay.size
            then
              intersectImplDown merge (.lnode1 (ay.drop or) done) (.lnode1 ax' cx') cy com 0
            else
              (.leaf done)
  | .fnode v ax cx, .fnode1 w ay cy =>
      match ByteArray.matchSingle_wOffset ay or ax with
      | .none => if or == 0 then (.fruit (merge v w) done) else (.leaf done)
      | .some idx =>
          let ax' := ax[idx]!
          let cx' := cx[idx]!
          let com := ByteArray.getLongestMatch_wOffsets ax' ay 0 or
          if com == ax'.size
          then
            if ax'.size == ay.size
            then
              intersectImplDown merge (.fnode1 (merge v w) ax' done) cx' cy 0 0
            else
              intersectImplDown merge (.fnode1 (merge v w) ax' done) cx' r 0 (or + com)
          else
            if or + com == ay.size
            then
              intersectImplDown merge (.fnode1 (merge v w) (ay.drop or) done) (.lnode1 ax' cx') cy com 0
            else
              if or == 0 then (.fruit (merge v w) done) else (.leaf done)
  | .lnode ax cx, .lnode ay cy | .fnode _ ax cx, .lnode ay cy | .lnode ax cx, .fnode _ ay cy =>
      let hits := (ByteArray.matchMulti ax ay)
      let gone : List ByteArray × List (Prod4 (CTrie α) (CTrie α) Nat Nat) := hits.foldl
        (fun c@(Lb,L) ⟨ai,bi,com⟩ =>
          let A := ax[ai]!
          let B := ay[bi]!
            if com == A.size
            then
              if A.size == B.size
              then
                (A :: Lb, (Prod4.mk (cx[ai]!) (cy[bi]!) 0 0) :: L)
              else
                (A :: Lb, (Prod4.mk (cx[ai]!) (.lnode1 B (cy[bi]!)) 0 com) :: L)
            else
              if com == B.size
              then
                (B :: Lb, (Prod4.mk (.lnode1 A (cx[ai]!)) (cy[bi]!) com 0) :: L)
              else
                c
          ) ([],[])
      let cs := gone.1.toArray
      let todos := gone.2.toArray
      let ts := (Array.replicate gone.1.length .leaf)
      let here := todos[0]!
      intersectImplDown merge (.lnode cs todos ts 0 done) here.1 here.2 here.3 here.4
  | .fnode v ax cx, .fnode w ay cy =>
      let hits := (ByteArray.matchMulti ax ay)
      let gone : List ByteArray × List (Prod4 (CTrie α) (CTrie α) Nat Nat) := hits.foldl
        (fun c@(Lb,L) ⟨ai,bi,com⟩ =>
          let A := ax[ai]!
          let B := ay[bi]!
            if com == A.size
            then
              if A.size == B.size
              then
                (A :: Lb, (Prod4.mk (cx[ai]!) (cy[bi]!) 0 0) :: L)
              else
                (A :: Lb, (Prod4.mk (cx[ai]!) (.lnode1 B (cy[bi]!)) 0 com) :: L)
            else
              if com == B.size
              then
                (B :: Lb, (Prod4.mk (.lnode1 A (cx[ai]!)) (cy[bi]!) com 0) :: L)
              else
                c
          ) ([],[])
      let cs := gone.1.toArray
      let todos := gone.2.toArray
      let ts := (Array.replicate gone.1.length .leaf)
      let here := todos[0]!
      intersectImplDown merge (.fnode (merge v w) cs todos ts 0 done) here.1 here.2 here.3 here.4



@[specialize]
partial def intersectImplUp (merge : α → α → α) (t : CTrie α)  : CTrieZipI α → CTrie α
  | .nil => t
  | .leaf nx => intersectImplUp merge (.leaf) nx
  | .fruit v nx => intersectImplUp merge (.fruit v) nx
  | .lnode1 c nx =>
      match t with
      | .leaf => intersectImplUp merge t nx
      | .lnode1 c' k => intersectImplUp merge (.lnode1 (c ++ c') k) nx
      | _ =>
        if c.isEmpty
        then intersectImplUp merge t nx
        else intersectImplUp merge (.lnode1 c t) nx
  | .fnode1 v c nx =>
      match t with
      | .leaf => intersectImplUp merge (.fruit v) nx
      | .lnode1 c' k => intersectImplUp merge (.fnode1 v (c ++ c') k) nx
      | _ => intersectImplUp merge (.fnode1 v c t) nx
  | .lnode cs todos ts idx nx =>
      if idx == ts.size - 1
      then
        let ts := ts.set! idx t
        let (nax,ncx) := clean_inner cs ts [] [] cs.size
        match nax, ncx with
        | [], _ => intersectImplUp merge (.leaf) nx
        | [NAX], [NCX] => intersectImplUp merge (.lnode1 NAX NCX) nx
        | _, _ => intersectImplUp merge (.lnode nax.toArray ncx.toArray) nx
      else
        let ts := ts.set! idx t
        let here := todos[idx+1]!
        let NX := intersectImplDown merge  (.lnode cs todos ts (idx+1) nx) here.1 here.2 here.3 here.4
        intersectImplUp merge t NX
  | .fnode v cs todos ts idx nx =>
      if idx == ts.size - 1
      then
        let ts := ts.set! idx t
        let (nax,ncx) := clean_inner cs ts [] [] cs.size
        match nax, ncx with
        | [], _ => intersectImplUp merge (.fruit v) nx
        | [NAX], [NCX] => intersectImplUp merge (.fnode1 v NAX NCX) nx
        | _, _ => intersectImplUp merge (.fnode v nax.toArray ncx.toArray) nx
      else
        let ts := ts.set! idx t
        let here := todos[idx+1]!
        let NX := intersectImplDown merge (.fnode v cs todos ts (idx+1) nx) here.1 here.2 here.3 here.4
        intersectImplUp merge t NX
where
  clean_inner (cs : Array ByteArray) (ts : Array (CTrie α)) (bs : List ByteArray) (Ts : List (CTrie α)) : Nat → List ByteArray × List (CTrie α)
    | 0 => (bs,Ts)
    | n+1 =>
        let X := ts[n]!
        match X with
        | .leaf => clean_inner cs ts bs Ts n
        | _ => clean_inner cs ts ((cs[n]!) :: bs) (X :: Ts) n



@[specialize]
def intersect (merge : α → α → α) (l r : CTrie α) : CTrie α :=
  intersectImplUp merge .leaf <| intersectImplDown merge .nil l r 0 0



@[specialize]
partial def foldOnCommon
  (init : β) (f : α → α → β → β) (todo : ListProd4 (CTrie α) (CTrie α) Nat Nat) : β :=
  match todo with
  | .nil => init
  | .cons l r ol or nx =>
  match l, r with
  | .leaf, _ | _, .leaf => foldOnCommon init f nx
  | .fruit v,  .fruit u | .fruit v,  .fnode u ..  | .fnode v ..,  .fruit u => foldOnCommon (f v u init) f nx
  | .fruit v,  .fnode1 u .. =>
    if or == 0 then foldOnCommon (f v u init) f nx else foldOnCommon init f nx
  | .fnode1 v ..,  .fruit u =>
    if ol == 0 then foldOnCommon (f v u init) f nx else foldOnCommon init f nx
  | .fruit .., _ | _, .fruit .. => foldOnCommon init f nx
  | .lnode1 ax cx, .lnode1 ay cy | .lnode1 ax cx, .fnode1 _ ay cy | .fnode1 _ ax cx, .lnode1 ay cy =>
      let com := ByteArray.getLongestMatch_wOffsets ax ay ol or
      if ol + com == ax.size
      then
        if or + com == ay.size
        then
          foldOnCommon init f (.cons cx cy 0 0 nx)
        else
          foldOnCommon init f (.cons cx r 0 (or + com) nx)
      else
        if or + com == ay.size
        then
          foldOnCommon init f <| .cons l cy (ol + com) 0 nx
        else
          foldOnCommon init f nx
  | .fnode1 v ax cx, .fnode1 w ay cy =>
      let com := ByteArray.getLongestMatch_wOffsets ax ay ol or
      if ol + com == ax.size
      then
        if or + com == ay.size
        then
          foldOnCommon (if ol == 0 && or == 0 then f v w init else init) f <| .cons cx cy 0 0 nx
        else
          foldOnCommon (if ol == 0 && or == 0 then f v w init else init) f <| .cons cx r 0 (or + com) nx
      else
        if or + com == ay.size
        then
          foldOnCommon (if ol == 0 && or == 0 then f v w init else init) f <| .cons l cy (ol + com) 0 nx
        else
          if ol == 0 && or == 0 then foldOnCommon (f v w init) f nx else foldOnCommon init f nx
  | .lnode1 ax cx, .fnode _ ay cy | .fnode1 _ ax cx, .lnode ay cy | .lnode1 ax cx, .lnode ay cy =>
      match ByteArray.matchSingle_wOffset ax ol ay with
      | .none => foldOnCommon init f nx
      | .some idx =>
          let ay' := ay[idx]!
          let cy' := cy[idx]!
          let com := ByteArray.getLongestMatch_wOffsets ax ay' ol 0
          if ol + com == ax.size
          then
            if com == ay'.size
            then
              foldOnCommon init f <| .cons cx cy' 0 0 nx
            else
              foldOnCommon init f <| .cons cx (.lnode1 ay' cy') 0 com nx
          else
            if com == ay'.size
            then
              foldOnCommon init f <| .cons l cy' (ol+com) 0 nx
            else
              foldOnCommon init f nx
  | .fnode1 v ax cx, .fnode w ay cy =>
      match ByteArray.matchSingle_wOffset ax ol ay with
      | .none =>
        if ol == 0 then foldOnCommon (f v w init) f nx else foldOnCommon init f nx
      | .some idx =>
          let ay' := ay[idx]!
          let cy' := cy[idx]!
          let com := ByteArray.getLongestMatch_wOffsets ax ay' ol 0
          if ol + com == ax.size
          then
            if com == ay'.size
            then
              foldOnCommon (if ol == 0 then f v w init else init) f <| .cons cx cy' 0 0 nx
            else
              foldOnCommon (if ol == 0 then f v w init else init) f <| .cons cx (.lnode1 ay' cy') 0 com nx
          else
            if com == ay'.size
            then
              foldOnCommon (if ol == 0 then f v w init else init) f <| .cons l cy' (ol+com) 0 nx
            else
              if ol == 0 then foldOnCommon (f v w init) f nx else foldOnCommon init f nx
  | .lnode ax cx, .fnode1 _ ay cy | .fnode _ ax cx, .lnode1 ay cy | .lnode ax cx, .lnode1 ay cy =>
      match ByteArray.matchSingle_wOffset ay or ax with
      | .none => foldOnCommon init f nx
      | .some idx =>
          let ax' := ax[idx]!
          let cx' := cx[idx]!
          let com := ByteArray.getLongestMatch_wOffsets ax' ay 0 or
          if com == ax'.size
          then
            if or + com == ay.size
            then
              foldOnCommon init f <| .cons cx' cy 0 0 nx
            else
              foldOnCommon init f <| .cons cx' r 0 (or + com) nx
          else
            if or + com == ay.size
            then
              foldOnCommon init f <| .cons (.lnode1 ax' cx') cy com 0 nx
            else
              foldOnCommon init f nx
  | .fnode v ax cx, .fnode1 w ay cy =>
      match ByteArray.matchSingle_wOffset ay or ax with
      | .none =>
        if or == 0 then foldOnCommon (f v w init) f nx else foldOnCommon init f nx
      | .some idx =>
          let ax' := ax[idx]!
          let cx' := cx[idx]!
          let com := ByteArray.getLongestMatch_wOffsets ax' ay 0 or
          if com == ax'.size
          then
            if or + com == ay.size
            then
              foldOnCommon (if or == 0 then f v w init else init) f <| .cons cx' cy 0 0 nx
            else
              foldOnCommon (if or == 0 then f v w init else init) f <| .cons cx' r 0 (or + com) nx
          else
            if or + com == ay.size
            then
              foldOnCommon (if or == 0 then f v w init else init) f <| .cons (.lnode1 ax' cx') cy com 0 nx
            else
              if or == 0 then foldOnCommon (f v w init) f nx else foldOnCommon init f nx
  | .lnode ax cx, .lnode ay cy | .fnode _ ax cx, .lnode ay cy | .lnode ax cx, .fnode _ ay cy =>
      let hits := (ByteArray.matchMulti ax ay)
      let gone : ListProd4 (CTrie α) (CTrie α) Nat Nat := hits.foldl
        (fun L ⟨ai,bi,com⟩ =>
          let A := ax[ai]!
          let B := ay[bi]!
            if com == A.size
            then
              if A.size == B.size
              then
                .cons (cx[ai]!) (cy[bi]!) 0 0 L
              else
                .cons (cx[ai]!) (.lnode1 B (cy[bi]!)) 0 com L
            else
              if com == B.size
              then
                .cons (.lnode1 A (cx[ai]!)) (cy[bi]!) com 0 L
              else
                L
          ) nx
      foldOnCommon init f gone
  | .fnode v ax cx, .fnode w ay cy =>
      let hits := (ByteArray.matchMulti ax ay)
      let gone : ListProd4 (CTrie α) (CTrie α) Nat Nat := hits.foldl
        (fun L ⟨ai,bi,com⟩ =>
          let A := ax[ai]!
          let B := ay[bi]!
            if com == A.size
            then
              if A.size == B.size
              then
                .cons (cx[ai]!) (cy[bi]!) 0 0 L
              else
                .cons (cx[ai]!) (.lnode1 B (cy[bi]!)) 0 com L
            else
              if com == B.size
              then
                .cons (.lnode1 A (cx[ai]!)) (cy[bi]!) com 0 L
              else
                L
          ) nx
      foldOnCommon (f v w init) f gone



@[specialize]
partial def foldOnCommon_dbg
  [Repr α] [Repr β]
  (init : β) (f : α → α → β → β) (todo : ListProd4 (CTrie α) (CTrie α) Nat Nat) : β :=
  match todo with
  | .nil => init
  | .cons l r ol or nx =>
  dbg_trace s!"State:\ninit : {repr init}\nol or : {ol} {or}\nl : {repr l}\nr : {repr r}"
  match l, r with
  | .leaf, _ | _, .leaf => foldOnCommon_dbg init f nx
  | .fruit v,  .fruit u | .fruit v,  .fnode u ..  | .fnode v ..,  .fruit u => foldOnCommon_dbg (f v u init) f nx
  | .fruit v,  .fnode1 u .. =>
    if or == 0 then foldOnCommon_dbg (f v u init) f nx else foldOnCommon_dbg init f nx
  | .fnode1 v ..,  .fruit u =>
    if ol == 0 then foldOnCommon_dbg (f v u init) f nx else foldOnCommon_dbg init f nx
  | .fruit .., _ | _, .fruit .. => foldOnCommon_dbg init f nx
  | .lnode1 ax cx, .lnode1 ay cy | .lnode1 ax cx, .fnode1 _ ay cy | .fnode1 _ ax cx, .lnode1 ay cy =>
      let com := ByteArray.getLongestMatch_wOffsets ax ay ol or
      if ol + com == ax.size
      then
        if or + com == ay.size
        then
          foldOnCommon_dbg init f (.cons cx cy 0 0 nx)
        else
          foldOnCommon_dbg init f (.cons cx r 0 (or + com) nx)
      else
        if or + com == ay.size
        then
          foldOnCommon_dbg init f <| .cons l cy (ol + com) 0 nx
        else
          foldOnCommon_dbg init f nx
  | .fnode1 v ax cx, .fnode1 w ay cy =>
      let com := ByteArray.getLongestMatch_wOffsets ax ay ol or
      if ol + com == ax.size
      then
        if or + com == ay.size
        then
          foldOnCommon_dbg (if ol == 0 && or == 0 then f v w init else init) f <| .cons cx cy 0 0 nx
        else
          foldOnCommon_dbg (if ol == 0 && or == 0 then f v w init else init) f <| .cons cx r 0 (or + com) nx
      else
        if or + com == ay.size
        then
          foldOnCommon_dbg (if ol == 0 && or == 0 then f v w init else init) f <| .cons l cy (ol + com) 0 nx
        else
          if ol == 0 && or == 0 then foldOnCommon_dbg (f v w init) f nx else foldOnCommon_dbg init f nx
  | .lnode1 ax cx, .fnode _ ay cy | .fnode1 _ ax cx, .lnode ay cy | .lnode1 ax cx, .lnode ay cy =>
      match ByteArray.matchSingle_wOffset ax ol ay with
      | .none => foldOnCommon_dbg init f nx
      | .some idx =>
          let ay' := ay[idx]!
          let cy' := cy[idx]!
          let com := ByteArray.getLongestMatch_wOffsets ax ay' ol 0
          if ol + com == ax.size
          then
            if com == ay'.size
            then
              foldOnCommon_dbg init f <| .cons cx cy' 0 0 nx
            else
              foldOnCommon_dbg init f <| .cons cx (.lnode1 ay' cy') 0 com nx
          else
            if com == ay'.size
            then
              foldOnCommon_dbg init f <| .cons l cy' (ol+com) 0 nx
            else
              foldOnCommon_dbg init f nx
  | .fnode1 v ax cx, .fnode w ay cy =>
      match ByteArray.matchSingle_wOffset ax ol ay with
      | .none =>
        if ol == 0 then foldOnCommon_dbg (f v w init) f nx else foldOnCommon_dbg init f nx
      | .some idx =>
          let ay' := ay[idx]!
          let cy' := cy[idx]!
          let com := ByteArray.getLongestMatch_wOffsets ax ay' ol 0
          if ol + com == ax.size
          then
            if com == ay'.size
            then
              foldOnCommon_dbg (if ol == 0 then f v w init else init) f <| .cons cx cy' 0 0 nx
            else
              foldOnCommon_dbg (if ol == 0 then f v w init else init) f <| .cons cx (.lnode1 ay' cy') 0 com nx
          else
            if com == ay'.size
            then
              foldOnCommon_dbg (if ol == 0 then f v w init else init) f <| .cons l cy' (ol+com) 0 nx
            else
              if ol == 0 then foldOnCommon_dbg (f v w init) f nx else foldOnCommon_dbg init f nx
  | .lnode ax cx, .fnode1 _ ay cy | .fnode _ ax cx, .lnode1 ay cy | .lnode ax cx, .lnode1 ay cy =>
      match ByteArray.matchSingle_wOffset ay or ax with
      | .none => foldOnCommon_dbg init f nx
      | .some idx =>
          let ax' := ax[idx]!
          let cx' := cx[idx]!
          let com := ByteArray.getLongestMatch_wOffsets ax' ay 0 or
          if com == ax'.size
          then
            if or + com == ay.size
            then
              foldOnCommon_dbg init f <| .cons cx' cy 0 0 nx
            else
              foldOnCommon_dbg init f <| .cons cx' r 0 (or + com) nx
          else
            if or + com == ay.size
            then
              foldOnCommon_dbg init f <| .cons (.lnode1 ax' cx') cy com 0 nx
            else
              foldOnCommon_dbg init f nx
  | .fnode v ax cx, .fnode1 w ay cy =>
      match ByteArray.matchSingle_wOffset ay or ax with
      | .none =>
        if or == 0 then foldOnCommon_dbg (f v w init) f nx else foldOnCommon_dbg init f nx
      | .some idx =>
          let ax' := ax[idx]!
          let cx' := cx[idx]!
          let com := ByteArray.getLongestMatch_wOffsets ax' ay 0 or
          if com == ax'.size
          then
            if or + com == ay.size
            then
              foldOnCommon_dbg (if or == 0 then f v w init else init) f <| .cons cx' cy 0 0 nx
            else
              foldOnCommon_dbg (if or == 0 then f v w init else init) f <| .cons cx' r 0 (or + com) nx
          else
            if or + com == ay.size
            then
              foldOnCommon_dbg (if or == 0 then f v w init else init) f <| .cons (.lnode1 ax' cx') cy com 0 nx
            else
              if or == 0 then foldOnCommon_dbg (f v w init) f nx else foldOnCommon_dbg init f nx
  | .lnode ax cx, .lnode ay cy | .fnode _ ax cx, .lnode ay cy | .lnode ax cx, .fnode _ ay cy =>
      let hits := (ByteArray.matchMulti ax ay)
      let gone : ListProd4 (CTrie α) (CTrie α) Nat Nat := hits.foldl
        (fun L ⟨ai,bi,com⟩ =>
          let A := ax[ai]!
          let B := ay[bi]!
            if com == A.size
            then
              if A.size == B.size
              then
                .cons (cx[ai]!) (cy[bi]!) 0 0 L
              else
                .cons (cx[ai]!) (.lnode1 B (cy[bi]!)) 0 com L
            else
              if com == B.size
              then
                .cons (.lnode1 A (cx[ai]!)) (cy[bi]!) com 0 L
              else
                L
          ) nx
      foldOnCommon_dbg init f gone
  | .fnode v ax cx, .fnode w ay cy =>
      let hits := (ByteArray.matchMulti ax ay)
      let gone : ListProd4 (CTrie α) (CTrie α) Nat Nat := hits.foldl
        (fun L ⟨ai,bi,com⟩ =>
          let A := ax[ai]!
          let B := ay[bi]!
            if com == A.size
            then
              if A.size == B.size
              then
                .cons (cx[ai]!) (cy[bi]!) 0 0 L
              else
                .cons (cx[ai]!) (.lnode1 B (cy[bi]!)) 0 com L
            else
              if com == B.size
              then
                .cons (.lnode1 A (cx[ai]!)) (cy[bi]!) com 0 L
              else
                L
          ) nx
      foldOnCommon_dbg (f v w init) f gone


-- #exit

@[inline]
def CountCommon  (l r : CTrie α) : Nat :=
  foldOnCommon 0 (fun _ _ n => n+1) (.cons l r 0 0 .nil)

@[inline]
def intersect_val  (l r : CTrie α) : List α :=
  foldOnCommon [] (fun v _ L => v :: L) (.cons l r 0 0 .nil)

@[inline]
def intersect_val_pairs  (l r : CTrie α) : List (α × α) :=
  foldOnCommon [] (fun v w L => (v,w) :: L) (.cons l r 0 0 .nil)

@[inline]
def intersect_val_pairs_dbg [Repr α] (l r : CTrie α) : ListProd α α :=
  foldOnCommon_dbg .nil (fun v w L => .cons v w L) (.cons l r 0 0 .nil)


@[inline]
def intersect_val_pairs' (l r : CTrie α) : ListProd α α :=
  foldOnCommon .nil (fun v w L => .cons v w L) (.cons l r 0 0 .nil)

-- #exit

@[inline]
def merge_count_initialise (t : CTrie α) : CTrie Nat :=
  t.map (fun _ => .some 1)


/-- Should make for better reset-reuse in functions.
Other CTrieZip types should follow this example ?
Actually, no ... `dbgTraceIfShared` indicates that there isn't linear use ... -/
inductive CTrieZipMe (α : Type _) where
  | nil : CTrieZipMe α
  | atom : CTrie α → CTrieZipMe α → CTrieZipMe α
  | single : CTrie α → CTrieZipMe α → CTrieZipMe α
  | multi : CTrie α → Nat → CTrieZipMe α → CTrieZipMe α
  | lnode (L R : Array ByteArray) (TL TR : Array (CTrie α)) (lCount rCount : Nat) (doneB : List ByteArray) (doneT : List (CTrie α)) : CTrieZipMe α → CTrieZipMe α
  | fnode (L R : Array ByteArray) (TL TR : Array (CTrie α)) (lCount rCount : Nat) (doneB : List ByteArray) (doneT : List (CTrie α)) : α → CTrieZipMe α → CTrieZipMe α
deriving Inhabited, Repr, BEq

inductive mergeImplMultiInitT (α : Type _) where
| done : (List ByteArray) → (List (CTrie α)) → mergeImplMultiInitT α
| inter (l r : Nat) (doneB : List ByteArray) (doneT : List (CTrie α)) (TL TR : CTrie α) : mergeImplMultiInitT α
deriving Inhabited, Repr, BEq



partial def mergeImplMultiInit  (L R : Array ByteArray) (TL TR : Array (CTrie α))
  (l r : Nat) (doneB : List ByteArray) (doneT : List (CTrie α)) : mergeImplMultiInitT α :=
    if (l < L.size)
    then
      if (r < R.size)
      then
        let a := L[l]!
        let b := R[r]!
        let com := ByteArray.getLongestMatch a b
          if com == 0
          then
            if a.get! 0 < b.get! 0
            then mergeImplMultiInit L R TL TR (l+1) r (a :: doneB) ((TL[l]!) :: doneT)
            else mergeImplMultiInit L R TL TR l (r+1) (b :: doneB) ((TR[r]!) :: doneT)
          else
            if com == a.size
            then
              if com == b.size
              then
                .inter (l+1) (r+1) (a :: doneB) doneT  (TL[l]!) (TR[r]!)
              else
                let b' := b.drop (com)
                .inter (l+1) (r+1) (a :: doneB) doneT (TL[l]!) (.lnode1 b' (TR[r]!))
            else
              if com == b.size
              then
                let a' := a.drop (com)
                .inter (l+1) (r+1) (b :: doneB) doneT (.lnode1 a' (TL[l]!)) (TR[r]!)
              else
                let join := a.take (com)
                let a' := a.drop (com)
                let b' := b.drop (com)
                if a.get! com < b.get! (com)
                then
                  mergeImplMultiInit L R TL TR (l+1) (r+1) (join :: doneB) ((.lnode #[a',b'] #[(TL[l]!),(TR[r]!)]) :: doneT)
                else
                  mergeImplMultiInit L R TL TR (l+1) (r+1) (join :: doneB) ((.lnode #[b',a'] #[(TR[r]!),(TL[l]!)]) :: doneT)
      else
        let a := L[l]!
        mergeImplMultiInit L R TL TR (l+1) r (a :: doneB) ((TL[l]!) :: doneT)
    else
      if (r < R.size)
      then
        let b := R[r]!
        mergeImplMultiInit L R TL TR l (r+1) (b :: doneB) ((TR[r]!) :: doneT)
      else
        .done doneB doneT


@[specialize]
partial def mergeImplDown
  [Monad m]  (merge : α → α → m α) (done : CTrieZipMe α) (l r : CTrie α) (ol or : Nat) : m (CTrieZipMe α) :=
  match l, r with
  | .fruit v,  .fruit u => do return (.atom (.fruit (← merge v u)) done)
  | .fruit v,  .fnode1 u c t => do return (.atom (.fnode1 (← merge v u) (c.drop or) t) done)
  | .fnode1 v c t,  .fruit u => do return (.atom (.fnode1 (← merge v u) (c.drop ol) t) done)
  | .fruit v,  .fnode u c t => do return (.atom (.fnode (← merge v u) c t) done)
  | .fnode v c t,  .fruit u => do return (.atom (.fnode (← merge v u) c t) done)
  | .fruit v,  .lnode1 c t => return (.atom (.fnode1 v (c.drop or) t) done)
  | .lnode1 c t,  .fruit v => return (.atom (.fnode1 v (c.drop ol) t) done)
  | .fruit v,  .lnode c t => return (.atom (.fnode v c t) done)
  | .lnode c t,  .fruit v => return (.atom (.fnode v c t) done)
  | .leaf,  .fnode1 u c t => do return (.atom (.fnode1 u (c.drop or) t) done)
  | .leaf,  .lnode1 c t => do return (.atom (.lnode1 (c.drop or) t) done)
  | .fnode1 u c t, .leaf => do return (.atom (.fnode1 u (c.drop ol) t) done)
  | .lnode1 c t, .leaf => do return (.atom (.lnode1 (c.drop ol) t) done)
  | .leaf, x | x, .leaf => return (.atom x done)
  | .lnode1 ax cx, .lnode1 ay cy =>
      let com := ByteArray.getLongestMatch_wOffsets ax ay ol or
      if ol + com == ax.size
      then
        if or + com == ay.size
        then
          --dbg_trace s!"sin {(ax.drop ol)}"
          mergeImplDown merge (.single (.lnode1 (ax.drop ol) .leaf) done) cx cy 0 0
        else
          --dbg_trace s!"sin {(ax.drop ol)}"
          mergeImplDown merge (.single (.lnode1 (ax.drop ol) .leaf) done) cx (.lnode1 ay cy) 0 (or + com)
      else
        if or + com == ay.size
        then
          --dbg_trace s!"sin {(ay.drop or)}"
          mergeImplDown merge (.single (.lnode1 (ay.drop or) .leaf) done) (.lnode1 ax cx) cy (ol + com) 0
        else
          let join := (ax.drop ol).take (com)
          let ax' := ax.drop (ol + com)
          let ay' := ay.drop (or + com)
          if ax.get! (ol + com) < ay.get! (or + com)
          then
            --dbg_trace s!"A join {join}"
            return .atom ((.lnode1 join (.lnode #[ax',ay'] #[cx,cy]))) done
          else
            --dbg_trace s!"A join {join}"
            return .atom (.lnode1 join (.lnode #[ay',ax'] #[cy,cx])) done
  | .lnode1 ax cx, .fnode1 v ay cy | .fnode1 v ax cx, .lnode1 ay cy =>
      let com := ByteArray.getLongestMatch_wOffsets ax ay ol or
      if ol + com == ax.size
      then
        if or + com == ay.size
        then
          --dbg_trace s!"sin {(ax.drop ol)}"
          mergeImplDown merge (.single (.fnode1 v (ax.drop ol) .leaf) done) cx cy 0 0
        else
          --dbg_trace s!"sin {(ax.drop ol)}"
          mergeImplDown merge (.single (.fnode1 v (ax.drop ol) .leaf) done) cx (.lnode1 ay cy) 0 (or + com)
      else
        if or + com == ay.size
        then
          --dbg_trace s!"sin {(ay.drop or)}"
          mergeImplDown merge (.single (.fnode1 v (ay.drop or) .leaf) done) (.lnode1 ax cx) cy (ol + com) 0
        else
          let join := (ax.drop ol).take (com)
          let ax' := ax.drop (ol + com)
          let ay' := ay.drop (or + com)
          if ax.get! (ol + com) < ay.get! (or + com)
          then
            --dbg_trace s!"A join {join}"
            return .atom (.fnode1 v join (.lnode #[ax',ay'] #[cx,cy])) done
          else
            --dbg_trace s!"A join {join}"
            return .atom (.fnode1 v join (.lnode #[ay',ax'] #[cy,cx])) done
  | .fnode1 v ax cx, .fnode1 u ay cy => do
      let com := ByteArray.getLongestMatch_wOffsets ax ay ol or
      if ol + com == ax.size
      then
        if or + com == ay.size
        then
          --dbg_trace s!"sin {(ax.drop ol)}"
          mergeImplDown merge (.single (.fnode1 (← merge v u) (ax.drop ol) .leaf) done) cx cy 0 0
        else
          --dbg_trace s!"sin {(ax.drop ol)}"
          mergeImplDown merge (.single (.fnode1 (← merge v u) (ax.drop ol) .leaf) done) cx (.lnode1 ay cy) 0 (or + com)
      else
        if or + com == ay.size
        then
          --dbg_trace s!"sin {(ay.drop or)}"
          mergeImplDown merge (.single (.fnode1 (← merge v u) (ay.drop or) .leaf) done) (.lnode1 ax cx) cy (ol + com) 0
        else
          let join := (ax.drop ol).take (com)
          let ax' := ax.drop (ol + com)
          let ay' := ay.drop (or + com)
          if ax.get! (ol + com) < ay.get! (or + com)
          then
            --dbg_trace s!"A join {join}"
            return .atom (.fnode1 (← merge v u) join (.lnode #[ax',ay'] #[cx,cy])) done
          else
            --dbg_trace s!"A join {join}"
            return .atom (.fnode1 (← merge v u) join (.lnode #[ay',ax'] #[cy,cx])) done
  | .lnode1 ax cx, .lnode ay cy =>
      match ByteArray.matchSingleHits_wOffset ax ol ay with
      | .ins idx =>
        --dbg_trace s!"ins 1 {(ay.insertIdx! idx (ax.drop ol))}"
        return .atom (.lnode (ay.insertIdx! idx (ax.drop ol)) (cy.insertIdx! idx cx)) done
      | .hit idx com => do
          let ay' := ay[idx]!
          let cy' := cy[idx]!
          if ol + com == ax.size
          then
            if com == ay'.size
            then
              --dbg_trace s!"mutli {ay}"
              mergeImplDown merge (.multi (.lnode ay cy) idx done) cx cy' 0 0
              -- return .node (← mini_merge x y) ay (cy.set! idx sofar)
            else
              --dbg_trace s!"multi 1 {(ay.set! idx (ax.drop ol))}"
              mergeImplDown merge (.multi (.lnode (ay.set! idx (ax.drop ol)) cy) idx done) cx (.lnode1 ay' cy') 0 com
              -- return .node (← mini_merge x y) (ay.set! idx (ax.drop ol)) (cy.set! idx sofar)
          else
            if com == ay'.size
            then
              --dbg_trace s!"mutli {ay}"
              mergeImplDown merge (.multi (.lnode ay cy) idx done) l cy' (ol + com) 0
              -- return .node (← mini_merge x y) ay (cy.set! idx sofar)
            else
              let join := (ax.drop ol).take (com)
              let ax' := ax.drop (ol + com)
              let ay'' := ay'.drop (com)
              if ax.get! (ol + com) < ay'.get! (com)
              then
                --dbg_trace s!"A {(ay.set! idx join)}"
                return .atom (.lnode (ay.set! idx join) (cy.set! idx (.lnode #[ax',ay''] #[cx,cy']))) done
              else
                --dbg_trace s!"A {(ay.set! idx join)}"
                return .atom (.lnode  (ay.set! idx join) (cy.set! idx (.lnode #[ay'',ax'] #[cy',cx]))) done
  | .lnode ay cy, .lnode1 ax cx =>
      match ByteArray.matchSingleHits_wOffset ax or ay with
      | .ins idx =>
        --dbg_trace s!"ins 1 {(ay.insertIdx! idx (ax.drop or))}"
        return .atom (.lnode (ay.insertIdx! idx (ax.drop or)) (cy.insertIdx! idx cx)) done
      | .hit idx com => do
          let ay' := ay[idx]!
          let cy' := cy[idx]!
          if or + com == ax.size
          then
            if com == ay'.size
            then
              --dbg_trace s!"mutli {ay}"
              mergeImplDown merge (.multi (.lnode ay cy) idx done) cx cy' 0 0
              -- return .node (← mini_merge x y) ay (cy.set! idx sofar)
            else
              --dbg_trace s!"multi 1 {(ay.set! idx (ax.drop or))}"
              mergeImplDown merge (.multi (.lnode (ay.set! idx (ax.drop or)) cy) idx done) cx (.lnode1 ay' cy') 0 com
              -- return .node (← mini_merge x y) (ay.set! idx (ax.drop ol)) (cy.set! idx sofar)
          else
            if com == ay'.size
            then
              --dbg_trace s!"mutli {ay}"
              mergeImplDown merge (.multi (.lnode ay cy) idx done) r cy' (or + com) 0
              -- return .node (← mini_merge x y) ay (cy.set! idx sofar)
            else
              let join := (ax.drop or).take (com)
              let ax' := ax.drop (or + com)
              let ay'' := ay'.drop (com)
              if ax.get! (or + com) < ay'.get! (com)
              then
                --dbg_trace s!"A {(ay.set! idx join)}"
                return .atom (.lnode (ay.set! idx join) (cy.set! idx (.lnode #[ax',ay''] #[cx,cy']))) done
              else
                --dbg_trace s!"A {(ay.set! idx join)}"
                return .atom (.lnode  (ay.set! idx join) (cy.set! idx (.lnode #[ay'',ax'] #[cy',cx]))) done
  | .lnode1 ax cx, .fnode v ay cy | .fnode1 v ax cx, .lnode ay cy =>
      match ByteArray.matchSingleHits_wOffset ax ol ay with
      | .ins idx =>
        --dbg_trace s!"ins 1 {(ay.insertIdx! idx (ax.drop ol))}"
        return .atom (.fnode v (ay.insertIdx! idx (ax.drop ol)) (cy.insertIdx! idx cx)) done
      | .hit idx com => do
          let ay' := ay[idx]!
          let cy' := cy[idx]!
          if ol + com == ax.size
          then
            if com == ay'.size
            then
              --dbg_trace s!"mutli {ay}"
              mergeImplDown merge (.multi (.fnode v ay cy) idx done) cx cy' 0 0
              -- return .node (← mini_merge x y) ay (cy.set! idx sofar)
            else
              --dbg_trace s!"multi 1 {(ay.set! idx (ax.drop ol))}"
              mergeImplDown merge (.multi (.fnode v (ay.set! idx (ax.drop ol)) cy) idx done) cx (.lnode1 ay' cy') 0 com
              -- return .node (← mini_merge x y) (ay.set! idx (ax.drop ol)) (cy.set! idx sofar)
          else
            if com == ay'.size
            then
              --dbg_trace s!"mutli {ay}"
              mergeImplDown merge (.multi (.fnode v ay cy) idx done) l cy' (ol + com) 0
              -- return .node (← mini_merge x y) ay (cy.set! idx sofar)
            else
              let join := (ax.drop ol).take (com)
              let ax' := ax.drop (ol + com)
              let ay'' := ay'.drop (com)
              if ax.get! (ol + com) < ay'.get! (com)
              then
                --dbg_trace s!"A {(ay.set! idx join)}"
                return .atom (.fnode v (ay.set! idx join) (cy.set! idx (.lnode #[ax',ay''] #[cx,cy']))) done
              else
                --dbg_trace s!"A {(ay.set! idx join)}"
                return .atom (.fnode v  (ay.set! idx join) (cy.set! idx (.lnode #[ay'',ax'] #[cy',cx]))) done
  | .fnode v ay cy, .lnode1 ax cx | .lnode ay cy, .fnode1 v ax cx =>
      match ByteArray.matchSingleHits_wOffset ax or ay with
      | .ins idx =>
        --dbg_trace s!"ins 1 {(ay.insertIdx! idx (ax.drop or))}"
        return .atom (.fnode v (ay.insertIdx! idx (ax.drop or)) (cy.insertIdx! idx cx)) done
      | .hit idx com => do
          let ay' := ay[idx]!
          let cy' := cy[idx]!
          if or+ com == ax.size
          then
            if com == ay'.size
            then
              --dbg_trace s!"mutli {ay}"
              mergeImplDown merge (.multi (.fnode v ay cy) idx done) cx cy' 0 0
              -- return .node (← mini_merge x y) ay (cy.set! idx sofar)
            else
              --dbg_trace s!"multi 1 {(ay.set! idx (ax.drop or))}"
              mergeImplDown merge (.multi (.fnode v (ay.set! idx (ax.drop or)) cy) idx done) cx (.lnode1 ay' cy') 0 com
              -- return .node (← mini_merge x y) (ay.set! idx (ax.drop ol)) (cy.set! idx sofar)
          else
            if com == ay'.size
            then
              --dbg_trace s!"mutli {ay}"
              mergeImplDown merge (.multi (.fnode v ay cy) idx done) r cy' (or + com) 0
              -- return .node (← mini_merge x y) ay (cy.set! idx sofar)
            else
              let join := (ax.drop or).take (com)
              let ax' := ax.drop (or + com)
              let ay'' := ay'.drop (com)
              if ax.get! (or + com) < ay'.get! (com)
              then
                --dbg_trace s!"A {(ay.set! idx join)}"
                return .atom (.fnode v (ay.set! idx join) (cy.set! idx (.lnode #[ax',ay''] #[cx,cy']))) done
              else
                --dbg_trace s!"A {(ay.set! idx join)}"
                return .atom (.fnode v  (ay.set! idx join) (cy.set! idx (.lnode #[ay'',ax'] #[cy',cx]))) done
  | .fnode1 v ax cx, .fnode u ay cy => do
      match ByteArray.matchSingleHits_wOffset ax ol ay with
      | .ins idx =>
        --dbg_trace s!"ins 1 {(ay.insertIdx! idx (ax.drop ol))}"
        return .atom (.fnode (← merge v u) (ay.insertIdx! idx (ax.drop ol)) (cy.insertIdx! idx cx)) done
      | .hit idx com => do
          let ay' := ay[idx]!
          let cy' := cy[idx]!
          if ol + com == ax.size
          then
            if com == ay'.size
            then
              --dbg_trace s!"mutli {ay}"
              mergeImplDown merge (.multi (.fnode (← merge v u) ay cy) idx done) cx cy' 0 0
              -- return .node (← mini_merge x y) ay (cy.set! idx sofar)
            else
              --dbg_trace s!"multi 1 {(ay.set! idx (ax.drop ol))}"
              mergeImplDown merge (.multi (.fnode (← merge v u) (ay.set! idx (ax.drop ol)) cy) idx done) cx (.lnode1 ay' cy') 0 com
              -- return .node (← mini_merge x y) (ay.set! idx (ax.drop ol)) (cy.set! idx sofar)
          else
            if com == ay'.size
            then
              --dbg_trace s!"mutli {ay}"
              mergeImplDown merge (.multi (.fnode (← merge v u) ay cy) idx done) l cy' (ol + com) 0
              -- return .node (← mini_merge x y) ay (cy.set! idx sofar)
            else
              let join := (ax.drop ol).take (com)
              let ax' := ax.drop (ol + com)
              let ay'' := ay'.drop (com)
              if ax.get! (ol + com) < ay'.get! (com)
              then
                --dbg_trace s!"A {(ay.set! idx join)}"
                return .atom (.fnode (← merge v u) (ay.set! idx join) (cy.set! idx (.lnode #[ax',ay''] #[cx,cy']))) done
              else
                --dbg_trace s!"A {(ay.set! idx join)}"
                return .atom (.fnode (← merge v u)  (ay.set! idx join) (cy.set! idx (.lnode #[ay'',ax'] #[cy',cx]))) done
  | .fnode v ay cy, .fnode1 u ax cx => do
      match ByteArray.matchSingleHits_wOffset ax or ay with
      | .ins idx =>
        --dbg_trace s!"ins 1 {(ay.insertIdx! idx (ax.drop or))}"
        return .atom (.fnode (← merge v u) (ay.insertIdx! idx (ax.drop or)) (cy.insertIdx! idx cx)) done
      | .hit idx com => do
          let ay' := ay[idx]!
          let cy' := cy[idx]!
          if or + com == ax.size
          then
            if com == ay'.size
            then
              --dbg_trace s!"mutli {ay}"
              mergeImplDown merge (.multi (.fnode (← merge v u) ay cy) idx done) cx cy' 0 0
              -- return .node (← mini_merge x y) ay (cy.set! idx sofar)
            else
              --dbg_trace s!"multi 1 {(ay.set! idx (ax.drop or))}"
              mergeImplDown merge (.multi (.fnode (← merge v u) (ay.set! idx (ax.drop or)) cy) idx done) cx (.lnode1 ay' cy') 0 com
              -- return .node (← mini_merge x y) (ay.set! idx (ax.drop ol)) (cy.set! idx sofar)
          else
            if com == ay'.size
            then
              --dbg_trace s!"mutli {ay}"
              mergeImplDown merge (.multi (.fnode (← merge v u) ay cy) idx done) r cy' (or + com) 0
              -- return .node (← mini_merge x y) ay (cy.set! idx sofar)
            else
              let join := (ax.drop or).take (com)
              let ax' := ax.drop (or + com)
              let ay'' := ay'.drop (com)
              if ax.get! (or + com) < ay'.get! (com)
              then
                --dbg_trace s!"A {(ay.set! idx join)}"
                return .atom (.fnode (← merge v u) (ay.set! idx join) (cy.set! idx (.lnode #[ax',ay''] #[cx,cy']))) done
              else
                --dbg_trace s!"A {(ay.set! idx join)}"
                return .atom (.fnode (← merge v u)  (ay.set! idx join) (cy.set! idx (.lnode #[ay'',ax'] #[cy',cx]))) done
  | .lnode ax cx, .lnode ay cy =>
      match mergeImplMultiInit ax ay cx cy 0 0 [] [] with
      | .done as ts =>
          --dbg_trace s!"up M {as}"
          return .atom (.lnode (as.reverse.toArray) (ts.reverse.toArray)) done
      | .inter l r doneB doneT TL TR =>
          --dbg_trace s!"up D {doneB}"
          mergeImplDown merge (.lnode ax ay cx cy l r doneB doneT done) TL TR 0 0
  | .fnode v ax cx, .lnode ay cy | .lnode ax cx, .fnode v ay cy =>
      match mergeImplMultiInit ax ay cx cy 0 0 [] [] with
      | .done as ts =>
          --dbg_trace s!"up M {as}"
          return .atom (.fnode v (as.reverse.toArray) (ts.reverse.toArray)) done
      | .inter l r doneB doneT TL TR =>
          --dbg_trace s!"up D {doneB}"
          mergeImplDown merge (.fnode ax ay cx cy l r doneB doneT v done) TL TR 0 0
  | .fnode v ax cx, .fnode u ay cy => do
      match mergeImplMultiInit ax ay cx cy 0 0 [] [] with
      | .done as ts =>
          --dbg_trace s!"up M {as}"
          return .atom (.fnode (← merge v u) (as.reverse.toArray) (ts.reverse.toArray)) done
      | .inter l r doneB doneT TL TR =>
          --dbg_trace s!"up D {doneB}"
          mergeImplDown merge (.fnode ax ay cx cy l r doneB doneT (← merge v u) done) TL TR 0 0

-- #exit

@[specialize]
partial def mergeImplUp
  [Monad m]  (merge : α → α → m α) (t : CTrie α) (z : CTrieZipMe α) : m (CTrie α) :=
  match z with
  | .nil => return t
  | .atom t nx => mergeImplUp merge (t) nx
  | .single T nx =>
      match T with
      | .lnode1 b _ =>
        --dbg_trace s!"up 1 {b}"
        mergeImplUp merge (.lnode1 b t) nx
      | .fnode1 v b _ =>
        --dbg_trace s!"up 1 {b}"
        mergeImplUp merge (.fnode1 v b t) nx
      | _ => panic! "[mergeImplUp] 1"
  | .multi T idx nx =>
      match T with
      | .lnode b ts =>
        --dbg_trace s!"up m {idx} {b}"
        mergeImplUp merge (.lnode b (ts.set! idx t)) nx
      | .fnode v b ts =>
        --dbg_trace s!"up m {idx} {b}"
        mergeImplUp merge (.fnode v b (ts.set! idx t)) nx
      | _ => panic! "[mergeImplUp] 2"
  | .lnode L R TL TR lC rC doneB doneT nx =>
      let doneT := t :: doneT
      match mergeImplMultiInit L R TL TR lC rC doneB doneT with
      | .done as ts =>
          --dbg_trace s!"up M {as}"
          mergeImplUp merge (.lnode (as.reverse.toArray) (ts.reverse.toArray)) nx
      | .inter l r doneB doneT tdL tdR => do
          --dbg_trace s!"up D {doneB}"
          let mgd ← mergeImplDown merge (.lnode L R TL TR l r doneB doneT nx) tdL tdR 0 0
          mergeImplUp merge .leaf mgd
  | .fnode L R TL TR lC rC doneB doneT v nx =>
      let doneT := t :: doneT
      match mergeImplMultiInit L R TL TR lC rC doneB doneT with
      | .done as ts =>
          --dbg_trace s!"up M {as}"
          mergeImplUp merge (.fnode v (as.reverse.toArray) (ts.reverse.toArray)) nx
      | .inter l r doneB doneT tdL tdR => do
          --dbg_trace s!"up D {doneB}"
          let mgd ← mergeImplDown merge (.fnode L R TL TR l r doneB doneT v nx) tdL tdR 0 0
          mergeImplUp merge .leaf mgd

-- #exit

@[specialize, inline]
def mergeM  [Monad m]  (merge : α → α → m α) (l r : CTrie α) : m (CTrie α) :=
  do
  --dbg_trace s!"L : {repr <| l.map (fun _ => .some ())}"
  --dbg_trace s!"R : {repr <| r.map (fun _ => .some ())}"
  let res ← mergeImplUp merge .leaf <| ← mergeImplDown merge .nil l r 0 0
  --dbg_trace s!"res : {repr <| res.map (fun _ => .some ())}"
  return clean res

@[specialize, inline]
def merge  (merge : α → α → α) (l r : CTrie α) : (CTrie α) :=
  --dbg_trace s!"L : {repr <| l.map (fun _ => .some ())}"
  --dbg_trace s!"R : {repr <| r.map (fun _ => .some ())}"
  let res := Id.run <| do mergeImplUp merge .leaf <| ← mergeImplDown merge .nil l r 0 0
  --dbg_trace s!"res : {repr <| res.map (fun _ => .some ())}"
  clean res

@[inline]
def merge_count (l r : CTrie Nat) : CTrie Nat :=
  merge (fun x y => x + y) l r



inductive CTrieZipD (α : Type _) where
  | nil : CTrieZipD α
  | atom : CTrie α → CTrieZipD α → CTrieZipD α
  | single : CTrie α → CTrieZipD α → CTrieZipD α
  | multi : CTrie α → Nat → CTrieZipD α → CTrieZipD α
  | lnode (L R : Array ByteArray) (TL TR : Array (CTrie α)) (lCount rCount : Nat) : CTrieZipD α → CTrieZipD α
  | fnode (L R : Array ByteArray) (TL TR : Array (CTrie α)) (lCount rCount : Nat) : α → CTrieZipD α → CTrieZipD α
deriving Inhabited, Repr, BEq


inductive differenceImplMultiT (α : Type _) where
| done (L : Array ByteArray) (TL : Array (CTrie α)) : differenceImplMultiT α
| inter (l r : Nat) (L R : Array ByteArray) (TL TR : Array (CTrie α)) (tL tR : CTrie α) (ol or : Nat) : differenceImplMultiT α
deriving Inhabited, Repr, BEq


partial def differenceImplMulti  (L R : Array ByteArray) (TL TR : Array (CTrie α))
  (l r : Nat)  : differenceImplMultiT α :=
    if (l < L.size) && (r < R.size)
    then
      let a := L[l]!
      let b := R[r]!
      let com := ByteArray.getLongestMatch a b
        if com == 0
        then
          if a.get! 0 < b.get! 0
          then differenceImplMulti L R TL TR (l+1) r
          else differenceImplMulti L R TL TR l (r+1)
        else
          if com == a.size
          then
            if com == b.size
            then
              .inter (l+1) (r+1) L R  TL TR (TL[l]!) (TR[r]!) 0 0
            else
              .inter (l+1) (r+1) L R  TL TR (TL[l]!) (.lnode1 b (TR[r]!)) 0 com
          else
            if com == b.size
            then
              .inter (l+1) (r+1) L R  TL TR (.lnode1 a (TL[l]!)) (TR[r]!) com 0
            else
              differenceImplMulti L R TL TR (l+1) (r+1)
    else
      .done L TL


partial def differenceImplDown [BEq α] (done : CTrieZipD α) (l r : CTrie α) (ol or : Nat) : CTrieZipD α :=
  match l with
  | .leaf  =>
      (.atom l done)
  | .fruit v =>
      match r with
      | .fruit u | .fnode u .. =>
          if u == v then (.atom .leaf done) else (.atom l done)
      | .fnode1 u .. =>
          if or == 0 && u == v then (.atom .leaf done) else (.atom l done)
      | _ =>
          (.atom l done)
  | .lnode1 ax cx =>
      match r with
      | .lnode1 ay cy | .fnode1 _ ay cy =>
          let com := ByteArray.getLongestMatch_wOffsets ax ay ol or
          if ol + com == ax.size
          then
            if or + com == ay.size
            then
              differenceImplDown (.single (.lnode1 (ax.drop ol) .leaf) done) cx cy 0 0
            else
              differenceImplDown (.single (.lnode1 (ax.drop ol) .leaf) done) cx r 0 (or + com)
          else
            if or + com == ay.size
            then
              differenceImplDown (.single (.lnode1 (ay.drop or) .leaf) done) l cy (ol + com) 0
            else
              (.atom (.lnode1 (ax.drop ol) cx) done)
      | .lnode ay cy | .fnode _ ay cy =>
          match ByteArray.matchSingle_wOffset ax ol ay with
          | .none => (.atom (.lnode1 (ax.drop ol) cx) done)
          | .some idx =>
              let ay' := ay[idx]!
              let cy' := cy[idx]!
              let com := ByteArray.getLongestMatch_wOffsets ax ay' ol or
              if ol + com == ax.size
              then
                if com == ay'.size
                then
                  differenceImplDown (.single (.lnode1 (ax.drop ol) .leaf) done) cx cy' 0 0
                else
                  differenceImplDown (.single (.lnode1 (ax.drop ol) .leaf) done) cx r 0 com
              else
                if com == ay'.size
                then
                  differenceImplDown (.single (.lnode1 ay' .leaf) done) l cy' (ol + com) 0
                else
                  (.atom (.lnode1 (ax.drop ol) cx) done)
      | _ =>
          (.atom (.lnode1 (ax.drop ol) cx) done)
  | .fnode1 v ax cx =>
      let rec @[inline] S (ay : ByteArray) (cy : CTrie α) (e : Thunk Bool) :=
        let com := ByteArray.getLongestMatch_wOffsets ax ay ol or
        if ol + com == ax.size
        then
          if or + com == ay.size
          then
            differenceImplDown
              (.single (if ol == 0 && e.get then .fnode1 v (ax.drop ol) .leaf else .lnode1 (ax.drop ol) .leaf) done)
              cx cy 0 0
          else
            differenceImplDown
              (.single (if ol == 0 && e.get then .fnode1 v (ax.drop ol) .leaf else .lnode1 (ax.drop ol) .leaf) done)
              cx (.lnode1 ay cy) 0 (or + com)
        else
          if or + com == ay.size
          then
            differenceImplDown
              (.single (if ol == 0 && e.get then .fnode1 v (ay.drop or) .leaf else .lnode1 (ay.drop or) .leaf) done)
              l cy (ol + com) 0
          else
            (.atom (if ol == 0 then l else .lnode1 (ax.drop ol) cx) done)
      let rec @[inline] M (ay : Array ByteArray) (cy : Array (CTrie α)) (e : Thunk Bool) :=
        match ByteArray.matchSingle_wOffset ax ol ay with
        | .none => (.atom (if ol == 0 then l else .lnode1 (ax.drop ol) cx) done)
        | .some idx =>
            let ay' := ay[idx]!
            let cy' := cy[idx]!
            let com := ByteArray.getLongestMatch_wOffsets ax ay' ol or
            if ol + com == ax.size
            then
              if com == ay'.size
              then
                differenceImplDown
                  (.single (if ol == 0 && e.get then .fnode1 v (ax.drop ol) .leaf else .lnode1 (ax.drop ol) .leaf) done)
                  cx cy' 0 0
              else
                differenceImplDown
                  (.single (if ol == 0 && e.get then .fnode1 v (ax.drop ol) .leaf else .lnode1 (ax.drop ol) .leaf) done)
                  cx (.lnode1 ay' cy') 0 com
            else
              if com == ay'.size
              then
                differenceImplDown
                  (.single ((if ol == 0 && e.get then .fnode1 v ay' .leaf else .lnode1 ay' .leaf)) done)
                  l cy' (ol + com) 0
              else
                (.atom (if ol == 0 then l else .lnode1 (ax.drop ol) cx) done)
      match r with
      | .lnode1 ay cy => S ay cy (.mk (fun _ => true))
      | .fnode1 u ay cy => S ay cy (.mk (fun _ => u != v && or == 0))
      | .lnode ay cy => M ay cy (.mk (fun _ => true))
      | .fnode u ay cy => M ay cy (.mk (fun _ => u != v))
      | .leaf =>
          (.atom (if ol == 0 then l else .lnode1 (ax.drop ol) cx) done)
      | .fruit u =>
          if ol == 0 then (if v == u then .atom (.lnode1 ax cx) done else .atom l done) else (.atom (.lnode1 (ax.drop ol) cx) done)
  | .lnode ax cx =>
      match r with
      | .lnode1 ay cy | .fnode1 _ ay cy =>
          match ByteArray.matchSingle_wOffset ay or ax with
          | .none => (.atom l done)
          | .some idx =>
                let ax' := ax[idx]!
                let cx' := cx[idx]!
                let com := ByteArray.getLongestMatch_wOffsets ax' ay 0 or
                if com == ax'.size
                then
                  if or + com == ay.size
                  then
                    differenceImplDown (.multi l idx done) cx' cy 0 0
                  else
                    differenceImplDown (.multi l idx done) cx' (.lnode1 ay cy) 0 (or + com)
                else
                  if or + com == ay.size
                  then
                    differenceImplDown (.multi l idx done) (.lnode1 ax' cx') cy com 0
                  else
                    (.atom l done)
      | .lnode ay cy | .fnode _ ay cy =>
          match differenceImplMulti ax ay cx cy 0 0 with
          | .done ax cx =>
            (.atom (.lnode ax cx) done)
          | .inter il ir L R TL TR tL tR ol or =>
            differenceImplDown (.lnode L R TL TR il ir done) tL tR ol or
      | _ =>
          (.atom l done)
  | .fnode v ax cx =>
      let rec @[inline] mS (ay : ByteArray) (cy : CTrie α) :=
        match ByteArray.matchSingle_wOffset ay or ax with
        | .none => (CTrieZipD.atom l done)
        | .some idx =>
              let ax' := ax[idx]!
              let cx' := cx[idx]!
              let com := ByteArray.getLongestMatch_wOffsets ax' ay 0 or
              if com == ax'.size
              then
                if or + com == ay.size
                then
                  differenceImplDown (.multi l idx done) cx' cy 0 0
                else
                  differenceImplDown (.multi l idx done) cx' (.lnode1 ay cy) 0 (or + com)
              else
                if or + com == ay.size
                then
                  differenceImplDown (.multi l idx done) (.lnode1 ax' cx') cy com 0
                else
                  (.atom l done)
      let rec @[inline] mM (ay : Array ByteArray) (cy : Array (CTrie α)) :=
        match differenceImplMulti ax ay cx cy 0 0 with
        | .done ax cx =>
          (CTrieZipD.atom (.fnode v ax cx) done)
        | .inter il ir L R TL TR tL tR ol or =>
          differenceImplDown (.fnode L R TL TR il ir v done) tL tR ol or
      match r with
      | .lnode1 ay cy => mS ay cy
      | .fnode1 u ay cy =>
          if v == u && or == 0
          then
            match ByteArray.matchSingle_wOffset ay or ax with
            | .none => (.atom (.lnode ax cx) done)
            | .some idx =>
                  let ax' := ax[idx]!
                  let cx' := cx[idx]!
                  let com := ByteArray.getLongestMatch_wOffsets ax' ay 0 or
                  if com == ax'.size
                  then
                    if or + com == ay.size
                    then
                      differenceImplDown (.multi (.lnode ax cx) idx done) cx' cy 0 0
                    else
                      differenceImplDown (.multi (.lnode ax cx) idx done) cx' (.lnode1 ay cy) 0 (or + com)
                  else
                    if or + com == ay.size
                    then
                      differenceImplDown (.multi (.lnode ax cx) idx done) (.lnode1 ax' cx') cy com 0
                    else
                      (.atom (.lnode ax cx) done)
          else
            mS ay cy
      | .lnode ay cy => mM ay cy
      | .fnode u ay cy =>
          if v == u
          then
            match differenceImplMulti ax ay cx cy 0 0 with
            | .done ax cx =>
              (CTrieZipD.atom (.lnode ax cx) done)
            | .inter il ir L R TL TR tL tR ol or =>
              differenceImplDown (.lnode L R TL TR il ir done) tL tR ol or
          else
            mM ay cy
      | .leaf =>
          (.atom l done)
      | .fruit u =>
          if v == u then (.atom (.lnode ax cx) done) else (.atom l done)



partial def differenceImplUp [BEq α] (t : CTrie α)  : CTrieZipD α → CTrie α
  | .nil => t
  | .atom t nx => differenceImplUp t nx
  | .single T nx =>
      match T with
      | .lnode1 c _ =>
          match t with
          | .leaf => differenceImplUp t nx
          | .lnode1 c' k => differenceImplUp (.lnode1 (c ++ c') k) nx
          | _ =>
            if c.isEmpty
            then differenceImplUp t nx
            else differenceImplUp (.lnode1 c t) nx
      | .fnode1 v c _ =>
          match t with
          | .leaf => differenceImplUp (.fruit v) nx
          | .lnode1 c' k => differenceImplUp (.fnode1 v (c ++ c') k) nx
          | _ => differenceImplUp (.fnode1 v c t) nx
      | _ => panic! "[differenceImplUp] 1"
  | .multi T idx nx =>
      match T with
      | .lnode b ts =>
          let ts := (ts.set! idx t)
          let (nax,ncx) := clean_inner b ts [] [] b.size
          match nax, ncx with
          | [], _ => differenceImplUp (.leaf) nx
          | [NAX], [NCX] => differenceImplUp (.lnode1 NAX NCX) nx
          | _, _ => differenceImplUp (.lnode nax.toArray ncx.toArray) nx
      | .fnode v b ts =>
          let ts := (ts.set! idx t)
          let (nax,ncx) := clean_inner b ts [] [] b.size
          match nax, ncx with
          | [], _ => differenceImplUp (.fruit v) nx
          | [NAX], [NCX] => differenceImplUp (.fnode1 v NAX NCX) nx
          | _, _ => differenceImplUp (.fnode v nax.toArray ncx.toArray) nx
      | _ => panic! "[differenceImplUp] 2"
  | .lnode L R TL TR il ir nx =>
      let TL := TL.set! (il - 1) t
      match differenceImplMulti L R TL TR il ir with
      | .done cs ts =>
        let (nax,ncx) := clean_inner cs ts [] [] cs.size
        match nax, ncx with
        | [], _ => differenceImplUp (.leaf) nx
        | [NAX], [NCX] => differenceImplUp (.lnode1 NAX NCX) nx
        | _, _ => differenceImplUp (.lnode nax.toArray ncx.toArray) nx
      | .inter il ir L R TL TR tL tR ol or =>
        let dfd := differenceImplDown (.lnode L R TL TR il ir nx) tL tR ol or
        differenceImplUp .leaf dfd
  | .fnode L R TL TR il ir v nx =>
      let TL := TL.set! (il - 1) t
      match differenceImplMulti L R TL TR il ir with
      | .done cs ts =>
        let (nax,ncx) := clean_inner cs ts [] [] cs.size
        match nax, ncx with
        | [], _ => differenceImplUp (.fruit v) nx
        | [NAX], [NCX] => differenceImplUp (.fnode1 v NAX NCX) nx
        | _, _ => differenceImplUp (.fnode v nax.toArray ncx.toArray) nx
      | .inter il ir L R TL TR tL tR ol or =>
        let dfd := differenceImplDown (.fnode L R TL TR il ir v nx) tL tR ol or
        differenceImplUp .leaf dfd
where
  clean_inner (cs : Array ByteArray) (ts : Array (CTrie α)) (bs : List ByteArray) (Ts : List (CTrie α)) : Nat → List ByteArray × List (CTrie α)
    | 0 => (bs,Ts)
    | n+1 =>
        let X := ts[n]!
        match X with
        | .leaf => clean_inner cs ts bs Ts n
        | _ => clean_inner cs ts ((cs[n]!) :: bs) (X :: Ts) n

@[inline]
def difference [BEq α] (l r : CTrie α) : CTrie α :=
  differenceImplUp .leaf <| differenceImplDown .nil l r 0 0

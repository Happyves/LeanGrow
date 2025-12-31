
/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import Lean.ResolveName

open Lean

def Lean.Name.size (n : Name) : Nat :=
  let rec go (c : Nat) : Name → Nat
    | .anonymous => c
    | .str m _ | .num m _ => go (c+1) m
  go 0 n


def Lean.Name.unreserve (env : Environment) : Name → Name
  | n@(.anonymous) | n@(.num _ _) => n
  | n@(.str m last) =>
    if isReservedName env n
    then (.str (.str m "lgr") last)
    else n


def Lean.Name.toUnderscoreString : Name → String
  | .anonymous => ""
  | .num n N => n.toUnderscoreString ++ "_" ++ s!"{N}"
  | .str n s => n.toUnderscoreString ++ "_" ++ s

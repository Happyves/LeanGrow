
/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/


import LeanGrow.Src.Data.Index.InstanceOrderedList


@[inline, specialize I]
-- metion of `I` required !!!
def general (Impl : Type) (I : IndexColl Impl) (x : Impl) : Bool :=
  I.size x == 42

set_option trace.compiler.ir.result true in
def specific (x : UInt32Array) : Bool := general UInt32Array idx_UInt32Array x


@[inline, specialize I]
def recursive (Impl : Type) (I : IndexColl Impl) (x : Impl) : Bool :=
  let rec @[specialize I] go : Nat → Bool
    | 0 => true
    | n+1 => if I.size x == 42 then go n else false
  go 42

set_option trace.compiler.ir.result true in
def specificRec (x : UInt32Array) : Bool := recursive UInt32Array idx_UInt32Array x
-- Seemingly unecessray code-gen, but does carry out specialization


@[inline, specialize I]
def withFold (Impl : Type) (I : IndexColl Impl) (x : Impl) : Bool :=
  I.foldl x false (fun a b => (a == 42) || b)


set_option trace.compiler.ir.result true in
def specWithFold (x : UInt32Array) : Bool := withFold UInt32Array idx_UInt32Array x
-- has specialized the function in foldl

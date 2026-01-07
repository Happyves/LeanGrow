
/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import LeanGrow.Src.Data.SetTrie.Specialize
import LeanGrow.Src.Utils.LeanGrow.TestTools


open Lean Meta


def PaInG.ofListS (l1 : LocalContext) (l2 : LocalInstances)
  (l : List (Nat × Expr)) (T : PaInG UInt32Array) :=
  PaInG.ofList l1 l2 l T .empty (fun x => UInt32Array.single x.toUInt32) (fun x y => y.oInsert x.toUInt32)

#check 1

def SetTriePG.ofListS [Inhabited α] [Repr α] (l : ListProd (PaInG UInt32Array) α) :=
  SetTriePG.ofList UInt32Array.inter UInt32Array.union UInt32Array.diff .empty UInt32Array.isEmpty UInt32Array.size l


#check 1

/--
- Expects 4 objects a b c d
- makes 3 sets : ab ac d
- labels : 37 42 666
-/
def test_1 : Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array DepCache → Array (FVarId × List FVarId) → MetaM Unit
  | _,_, _,_, _, _, _, _, _, _, Objs, _, _ => do
    let a := Objs[0]!
    let b := Objs[1]!
    let c := Objs[2]!
    let d := Objs[3]!
    let .mk set1 l1 l2 ← PaInG.ofListS (← getLCtx) (← getLocalInstances) [(0,a),(1,b)] .dead
    let .mk set2 l1 l2 ← PaInG.ofListS l1 l2 [(0,a),(2,c)] .dead
    let .mk set3 l1 l2 ← PaInG.ofListS l1 l2 [(3,d)] .dead
    let st := SetTriePG.ofListS <| ListProd.ofListOfProd [(set1,37),(set2,42),(set3,666)]
    let pst ← st.pp 0
      (fun x => x.ppS l1 l2 [] 0)
      (fun x => return toString x)
    IO.println pst


#check 1


With context g(n : Nat) u(x : Fin n : Fin.mk 0 sorry) t(0 : 0 : m : Nat) and objects (n + m = 42), (n * m = 37), (x = x), (x.val - n = m) run test_1

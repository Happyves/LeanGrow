

import LeanGrow.Src.Core.Embedding.UnifyBEFT
import LeanGrow.Src.Core.Embedding.UnifyFEBT

import LeanGrow.Src.Core.Embedding.TestTools_QueryStd


open Lean Meta


def uniBEwFTMainS :=
  PaInG.uniBEwFTMain
    UInt32Array.isEmpty UInt32Array.inter UInt32Array.union UInt32Array.diff UInt32Array.empty

#check 1


def uniFEwBTMainS :=
  PaInG.uniFEwBTMain
    UInt32Array.isEmpty UInt32Array.inter UInt32Array.union UInt32Array.diff UInt32Array.empty


#check 1


def testSandbox_uniBEwFT : Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array DepCache → Array (FVarId × List FVarId) → MetaM Unit
  | guT, gu, tT, t, lT, l, wsT, ws, ewsT, ews, Ts, deps, wdeps => do
      let que ← withTransparency .reducible <| reduce (skipTypes := false) Ts[0]!
      let mut Q := PaInG.dead
      let mut idx := 0
      IO.println s!"\nBuilding ltx"
      for T in guT do
        let T ← withTransparency .reducible <| reduce (skipTypes := false) T
        IO.println s!"Adding with idx {idx} type {← ppExpr T}"
        let .mk res l1 l2 ← Q.insert (← getLCtx) (← getLocalInstances) T idx
          UInt32Array.empty (fun x => UInt32Array.single x.toUInt32) (fun x y => y.oInsert x.toUInt32)
        Q := res
        idx := idx + 1
      let .mk status inds res _ _ ← uniBEwFTMainS (← getLCtx) (← getLocalInstances)
        (Q.getIndicesS) 2 que Q
      IO.println s!"Status {status}\nInds {inds}"
      for (is,ue,ul) in res.toListOfProd do
        IO.println s!"\nMatch ltx inds {is}"
        IO.println s!"Levels"
        for (i,p,l) in ul.toListOfProd do
          IO.println s!"idx {i} pos {p} : {l}"
        IO.println s!"Tnodes"
        for (i,p,e) in ue.toListOfProd do
          IO.println s!"idx {i} pos {p} : {← ppExpr e}"
      IO.println s!"Query : {← ppExpr que}"
      IO.println s!"Searching:\n{← Q.ppS (← getLCtx) (← getLocalInstances) [] 0}\n"

#check 1



def testSandbox_uniFEwBT : Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array DepCache → Array (FVarId × List FVarId) → MetaM Unit
  | guT, gu, tT, t, lT, l, wsT, ws, ewsT, ews, Ts, deps, wdeps => do
      let que ← withTransparency .reducible <| reduce (skipTypes := false) Ts[0]!
      let mut Q := PaInG.dead
      let mut idx := 0
      IO.println s!"\nBuilding goals"
      for T in tT do
        let T ← withTransparency .reducible <| reduce (skipTypes := false) T
        IO.println s!"Adding with idx {idx} type {← ppExpr T}"
        let .mk res l1 l2 ← Q.insert (← getLCtx) (← getLocalInstances) T idx
          UInt32Array.empty (fun x => UInt32Array.single x.toUInt32) (fun x y => y.oInsert x.toUInt32)
        Q := res
        idx := idx + 1
      let .mk status inds res _ _ ← uniFEwBTMainS (← getLCtx) (← getLocalInstances)
        (Q.getIndicesS) 2 que Q
      IO.println s!"Status {status}\nInds {inds}"
      for (is,ue,ul) in res.toListOfProd do
        IO.println s!"\nMatch ltx inds {is}"
        IO.println s!"Levels"
        for (i,p,l) in ul.toListOfProd do
          IO.println s!"idx {i} pos {p} : {l}"
        IO.println s!"Tnodes"
        for (i,p,e) in ue.toListOfProd do
          IO.println s!"idx {i} pos {p} : {← ppExpr e}"
      IO.println s!"\nQuery : {← ppExpr que}"
      IO.println s!"Searching:\n{← Q.ppS (← getLCtx) (← getLocalInstances) [] 0}\n"

#check 1


-- With context g(n : Nat) g(h : n+1 = 42) and objects (n.succ = 42) run testSandbox_uniBEwFT

-- With context g(n : Nat) g(h : n.succ = 42) and objects (n + 1 = 42) run testSandbox_uniBEwFT

-- With context g(n : Nat) g(h : n+1 = 42) t(0 : 0 : m : Nat) and objects (m.succ = 42) run testSandbox_uniBEwFT

-- With context g(n : Nat) g(h : n+1 = 42) t(0 : 0 : m : Nat) and objects (m = 42) run testSandbox_uniBEwFT

-- With context g(n : Nat) g(h : n+1 = 42) t(0 : 0 : m1 : Nat) t(2 : 3 : m2 : Nat) and objects (m1 = m2) run testSandbox_uniBEwFT


-- With context g(n : Nat) t(0 : 0 : m : Nat) t(0 : 1 : h : m.succ = 42) and objects (n.succ = 42) run testSandbox_uniFEwBT

-- With context g(n : Nat) t(0 : 0 : m : Nat) t(0 : 1 : h : m.succ = 42) and objects (n + 1 = 42) run testSandbox_uniFEwBT

-- With context g(n : Nat) t(0 : 0 : m : Nat) t(0 : 1 : h : m + 1 = 42) and objects (n.succ = 42) run testSandbox_uniFEwBT

-- With context g(n : Nat) t(0 : 0 : m : Nat) t(0 : 1 : h : m = 42) and objects (n.succ = 42) run testSandbox_uniFEwBT

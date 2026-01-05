
import LeanGrow.Src.Data.PathIndexG.Insert
import LeanGrow.Src.Data.PathIndexG.Operations
import LeanGrow.Src.Utils.LeanGrow.TestTools


open Lean Meta


def testMerge : Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array DepCache → Array (FVarId × List FVarId) → MetaM Unit
  | _,Gnodes, _,_, _, _, _, _, _, _, Objs, _, _ => do
      let mut L := []
      let mut R := []
      let mut i := 0
      let spl := Objs.size / 2
      for O in Objs do
        if i < spl
        then
          L := (i,O) :: L
        else
          R := (i,O) :: R
        i := i+1
      let ⟨Tl,l1,l2⟩ ← PaInG.ofList (← getLCtx) (← getLocalInstances) L .dead UInt32Array.empty (fun x => UInt32Array.single x.toUInt32)
        (fun x y => UInt32Array.oInsert y x.toUInt32)
      let ⟨Tr,l1,l2⟩ ← PaInG.ofList l1 l2 R .dead UInt32Array.empty (fun x => UInt32Array.single x.toUInt32)
        (fun x y => UInt32Array.oInsert y x.toUInt32)
      withReader (fun ctx => {ctx with lctx := l1, localInstances := l2}) do
        let built := (Tl.buildCore [] 0 id UInt32Array.inter UInt32Array.isEmpty).toListOfProd
        let built := ← built.mapM (fun (x,y) => return (← ppExpr x, y))
        IO.println s!"T left:\n{built}"
        let built := (Tr.buildCore [] 0 id UInt32Array.inter UInt32Array.isEmpty).toListOfProd
        let built := ← built.mapM (fun (x,y) => return (← ppExpr x, y))
        IO.println s!"T right:\n{built}"
        let Tm := PaInG.merge UInt32Array.union .empty Tl Tr
        let built := (Tm.buildCore [] 0 id UInt32Array.inter UInt32Array.isEmpty).toListOfProd
        let built := ← built.mapM (fun (x,y) => return (← ppExpr x, y))
        IO.println s!"T merged:\n{built}"

#check 1

With context g(n : Nat) g(m : Nat) and objects (n+m), (n-m), (n*m), (m+n), (fun x : Nat => ∀ y : Nat, x = y), (fun x : Nat => ∀ y : Nat, x = y+1) run testMerge

#check 1

With context g(n : Nat) g(x : Fin n) t(0 : 0 : y : Nat × Nat) and objects (y.1 = 42), (x.val = x.val + y.2), (1=1), (y.2 = 42), (x.val = x.val + 37), (1=1) run testMerge

#check 2

def testMapInds : Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array DepCache → Array (FVarId × List FVarId) → MetaM Unit
  | _,Gnodes, _,_, _, _, _, _, _, _, Objs, _, _ => do
      let mut L := []
      let mut i := 0
      for O in Objs do
        L := (i,O) :: L
        i := i+1
      let ⟨T,l1,l2⟩ ← PaInG.ofList (← getLCtx) (← getLocalInstances) L .dead UInt32Array.empty (fun x => UInt32Array.single x.toUInt32)
        (fun x y => UInt32Array.oInsert y x.toUInt32)
      withReader (fun ctx => {ctx with lctx := l1, localInstances := l2}) do
        let T := T.mapInds (UInt32Array.shiftAdd · 42) .empty
        let built := (T.buildCore [] 0 id UInt32Array.inter UInt32Array.isEmpty).toListOfProd
        let built := ← built.mapM (fun (x,y) => return (← ppExpr x, y))
        IO.println s!"T:\n{built}"

#check 1

With context g(n : Nat) g(m : Nat) and objects (n+m), (n-m), (n*m), (m+n), (fun x : Nat => ∀ y : Nat, x = y), (fun x : Nat => ∀ y : Nat, x = y+1) run testMapInds

def testDelete : Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array DepCache → Array (FVarId × List FVarId) → MetaM Unit
  | _,Gnodes, _,_, _, _, _, _, _, _, Objs, _, _ => do
      let mut L := []
      let mut i := 0
      for O in Objs do
        L := (i,O) :: L
        i := i+1
      let ⟨T,l1,l2⟩ ← PaInG.ofList (← getLCtx) (← getLocalInstances) L .dead UInt32Array.empty (fun x => UInt32Array.single x.toUInt32)
        (fun x y => UInt32Array.oInsert y x.toUInt32)
      withReader (fun ctx => {ctx with lctx := l1, localInstances := l2}) do
        let T := T.deleteOfInds (.mk #[0,2,4]) UInt32Array.diff .empty UInt32Array.isEmpty
        let built := (T.buildCore [] 0 id UInt32Array.inter UInt32Array.isEmpty).toListOfProd
        let built := ← built.mapM (fun (x,y) => return (← ppExpr x, y))
        IO.println s!"T:\n{built}"

#check 1

With context g(n : Nat) g(m : Nat) and objects (n+m), (n-m), (n*m), (m+n), (fun x : Nat => ∀ y : Nat, x = y), (fun x : Nat => ∀ y : Nat, x = y+1) run testDelete

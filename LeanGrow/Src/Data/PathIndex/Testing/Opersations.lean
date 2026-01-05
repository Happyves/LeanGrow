
import LeanGrowBeta.Data.PathIndex.Insert
import LeanGrowBeta.Data.PathIndex.Operations
import LeanGrowBeta.Utils.LeanGrow.TestTools


open Lean Meta


def testMerge : Array Expr → Array Expr → Array Expr → Array Expr → MetaM Unit
  | Gnodes, Unodes, Tnodes, Objs => do
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
      let ⟨Tl,l1,l2⟩ ← PaIn.ofList (← getLCtx) (← getLocalInstances) L .dead [] (fun x => [x])
        List.orderedInsertOrLeave
      let ⟨Tr,l1,l2⟩ ← PaIn.ofList l1 l2 R .dead [] (fun x => [x])
        List.orderedInsertOrLeave
      withReader (fun ctx => {ctx with lctx := l1, localInstances := l2}) do
        let built := (Tl.buildCore [] 0 id List.orderedIntersect List.isEmpty).toListOfProd
        let built := ← built.mapM (fun (x,y) => return (← ppExpr x, y))
        IO.println s!"T left:\n{built}"
        let built := (Tr.buildCore [] 0 id List.orderedIntersect List.isEmpty).toListOfProd
        let built := ← built.mapM (fun (x,y) => return (← ppExpr x, y))
        IO.println s!"T right:\n{built}"
        let Tm := PaIn.merge List.orderedUnion [] Tl Tr
        let built := (Tm.buildCore [] 0 id List.orderedIntersect List.isEmpty).toListOfProd
        let built := ← built.mapM (fun (x,y) => return (← ppExpr x, y))
        IO.println s!"T merged:\n{built}"

#check 1

With gnodes (n : Nat) (m : Nat) and unodes and tnodes and objects (n+m), (n-m), (n*m), (m+n), (fun x : Nat => ∀ y : Nat, x = y), (fun x : Nat => ∀ y : Nat, x = y+1) run testMerge

#check 1

With gnodes (n : Nat) (x : Fin n) and unodes and tnodes (y : Nat × Nat) and objects (y.1 = 42), (x.val = x.val + y.2), (1=1), (y.2 = 42), (x.val = x.val + 37), (1=1) run testMerge

#check 2

def testMapInds : Array Expr → Array Expr → Array Expr → Array Expr → MetaM Unit
  | Gnodes, Unodes, Tnodes, Objs => do
      let mut L := []
      let mut i := 0
      for O in Objs do
        L := (i,O) :: L
        i := i+1
      let ⟨T,l1,l2⟩ ← PaIn.ofList (← getLCtx) (← getLocalInstances) L .dead [] (fun x => [x])
        List.orderedInsertOrLeave
      withReader (fun ctx => {ctx with lctx := l1, localInstances := l2}) do
        let T := T.mapInds (List.map (· + 42)) []
        let built := (T.buildCore [] 0 id List.orderedIntersect List.isEmpty).toListOfProd
        let built := ← built.mapM (fun (x,y) => return (← ppExpr x, y))
        IO.println s!"T:\n{built}"

#check 1

With gnodes (n : Nat) (m : Nat) and unodes and tnodes and objects (n+m), (n-m), (n*m), (m+n), (fun x : Nat => ∀ y : Nat, x = y), (fun x : Nat => ∀ y : Nat, x = y+1) run testMapInds

def testDelete : Array Expr → Array Expr → Array Expr → Array Expr → MetaM Unit
  | Gnodes, Unodes, Tnodes, Objs => do
      let mut L := []
      let mut i := 0
      for O in Objs do
        L := (i,O) :: L
        i := i+1
      let ⟨T,l1,l2⟩ ← PaIn.ofList (← getLCtx) (← getLocalInstances) L .dead [] (fun x => [x])
        List.orderedInsertOrLeave
      withReader (fun ctx => {ctx with lctx := l1, localInstances := l2}) do
        let T := T.deleteOfInds [0,2,4] List.orderedDiff [] List.isEmpty
        let built := (T.buildCore [] 0 id List.orderedIntersect List.isEmpty).toListOfProd
        let built := ← built.mapM (fun (x,y) => return (← ppExpr x, y))
        IO.println s!"T:\n{built}"

#check 1

With gnodes (n : Nat) (m : Nat) and unodes and tnodes and objects (n+m), (n-m), (n*m), (m+n), (fun x : Nat => ∀ y : Nat, x = y), (fun x : Nat => ∀ y : Nat, x = y+1) run testDelete

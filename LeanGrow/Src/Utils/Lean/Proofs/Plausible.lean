

import Plausible

import Lean

open Plausible


#check Lean.evalConst

#check Lean.Compiler.LCNF.Code


#check Lean.IR.Decl

#check Lean.addAndCompile


#check Lean.Compiler.LCNF.ToLCNF.toLCNF


#check Lean.Compiler.LCNF.compile

def testFun (x : Nat) : Nat :=
  (x+1) * x


open Lean

def test0 (n : Name := `testFun) : CoreM Unit := do
  let res ← Lean.Compiler.LCNF.compile #[n]
  IO.println <| toString res[0]!

-- #eval test0


def test1 (n : Name := `testFun) : CoreM Unit := do
  let res ← Lean.Compiler.LCNF.compile #[n]
  for d in res do
    IO.println <| toString d

-- #eval test1



def testinFun (x : Nat) : Nat :=
  42 + testFun x

-- #eval test1 `testinFun


set_option trace.compiler.ir.result false

#check Lean.IR.compile

#check Lean.IR.findEnvDecl

def testIRget (n : Name) : CoreM Unit := do
  let env ← getEnv
  let .some de := Lean.IR.findEnvDecl env n | throwError "aahh"
    IO.println <| toString de


#eval testIRget `testinFun



#exit


#check Lean.IR.Expr

#print IR.VarId
#print IR.Index

structure MemoState where
  stack : Nat
  heap : Array (IR.VarId × Nat)
deriving Inhabited

instance : Repr MemoState where
  reprPrec s _ := s!"stack {s.stack} heap {s.heap.toList}"

def Lean.IR.Expr.memoWatch (var : IR.VarId) (s : MemoState) : IR.Expr → MemoState
  | .ctor _ _ => {s with heap := s.heap.push (var, 1)}
  | .fap _ as | .ap _ as => {s with stack := s.stack + as.size}
  | _ => s


def Lean.IR.FnBody.memoWatch (s : MemoState) : IR.FnBody → MemoState
  | .vdecl var _ e nx => nx.memoWatch (e.memoWatch var s)
  | .inc var c _ _ nx =>
      match s.heap.findIdx? (fun (v,_) => v == var) with
      | .none => panic! "inc on unknown var ..."


import LeanGrow.F.Data.CExpr.API
import LeanGrow.F.Data.CExpr.ReduceInfer.Magic
import LeanGrow.F.Utils.Trie.CTrie
import LeanGrow.F.Data.CExpr.ReduceInfer.ConstInfo
import LeanGrow.F.Data.CExpr.ReduceInfer.BetaZeta


open Lean

#check 1

-- maybe use use ByteArray encoding of names from the start ?
def cInferConstType (cstData : CTrie CstInfo) (c : Name) (us : List Level) : CExpr :=
  match cstData.find? (c.toString) with
  | .some info => info.type.instantiateLevelParams info.levelParams us
  | _ => .failed

def cInferAppType (bvarCtx : List CExpr) (f : CExpr) (args : List CExpr) : CExpr :=
  let fType := cexprInferType bvarCtx f -- will need fixin
  let rec go (sofar : CExpr) : List CExpr → CExpr
    | [] => sofar
    | a :: as =>
        match sofar with
        | .forallE _ _ b _ => go (CExpr.instanciate a b) as
        | _ =>
            match (cexprWhnf sofar) with -- will need fixin
            | .forallE _ _ b _ => go (CExpr.instanciate a b) as
            | _ => .failed
  go fType args

def cInferProjType (bvarCtx : List CExpr) (cstData : CTrie CstInfo) (structName : Name) (idx : Nat) (e : CExpr) : CExpr :=
  let rec go (sofar : CExpr) : Nat → CExpr
    | 0 => sofar
    | n+1 =>
        match sofar with
        | .forallE _ _ b _ => go (CExpr.instanciate (.proj structName (idx - 1 - n) e) b) n
        | _ =>
            match (cexprWhnf sofar) with
            | .forallE _ _ b _ => go (CExpr.instanciate (.proj structName (idx - 1 - n) e) b) n
            | _ => .failed
  let strucType := cexprWhnf (cexprInferType bvarCtx e)
  let (h,ps) := CExpr.getApp strucType
  match h with
  | .const _ lvls =>
      match cstData.find? structName.toString with
      | .some (.struc _ _ ctor) =>
            let ctorType := cInferAppType bvarCtx (.const ctor lvls) ps
            let toProj := cexprWhnf (go ctorType idx)
            match toProj with
            | .forallE _ t _ _ => t
            |  _ => .failed
      | _ => .failed
  | _ => .failed


def cInferLambdaType (bvarCtx : List CExpr) (e : CExpr) : CExpr × List CExpr :=
  let rec go (prepend : List CExpr) : CExpr → CExpr × List CExpr
    | .lam n t b i =>
        let (res, bvs) := go (t :: prepend) b
        (.forallE n t res i, bvs)
    | e => (e, prepend)
  go bvarCtx e

#check (fun n : Nat => (fun x : Fin n => x))

#exit

-- note : when adding environements for constantInfo and lnode and gnode types,
-- we should also change the types in LeanGrow.F.Data.CExpr.ReduceInfer.Magic
@[export lean_my_infer_type]
def cexprInferTypeImp (bvarCtx : List CExpr) (ce : CExpr) : CExpr := sorry

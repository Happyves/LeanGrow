
import LeanGrow.DAGembed
import LeanGrow.ProcessDecl
import LeanGrow.ProcessLocalCtx
import LeanGrow.Blacklisting
import Mathlib

open Lean



def scoring_by_module (env : Environment) (scores : List (Name × Nat)) : Array (Option Nat) :=
  let modules := env.header.moduleNames
  Id.run do
    let mut out := Array.mkArray modules.size (.none : Option Nat)
    let mut idx := 0
    for n in modules do
      let .some (_,s) := scores.find? (fun x => x.1.isPrefixOf n) | pure ()
      out := out.set! idx s
      idx := idx + 1
    return out

-- only last name that is prefix of mudule matters
def test_scores : List (Name × Nat) :=
  [(`Mathlib.Data.Finset, 20), (`Mathlib.Data.Fin, 20), (`Mathlib.Data.Nat, 10), (`Mathlib.Combinatorics, 50), (`Mathlib.Combinatorics.SetFamily, 70), (`Mathlib.Order, 10), (`Init.Core, 5), (`Init.Data, 5)]


#check matcher

#check NodeCst

#check SizedDAG


def DAG.findNode [BEq β] (D : DAG α β) (k : β) : Option (DAGnode α β) :=
  List.find? (fun N => N.name == k) D

partial def DAGnode.getLevel [BEq β] (D : DAG α β) (N : DAGnode α β) : Nat :=
  match N.parents with
  | [] => 0
  | ps =>
      let ls := (ps.map (DAG.findNode D)).reduceOption.map (DAGnode.getLevel D)
      let max := Id.run do
          let mut out := 0
          for l in ls do
            if l > out
            then
              out := l
          return out
      max+1

--def DAG.getLevels [BEq β] (D : DAG α β) : RBNode Nat (fun _ => Nat) :=

instance : Inhabited (Nat × RBNode Nat (fun _ => Nat)) where default := (0,{})

partial def DAGnode.getLevel' (D : DAG α Nat) (sofar : RBNode Nat (fun _ => Nat)) (N : DAGnode α Nat) : (Nat × RBNode Nat (fun _ => Nat)) :=
  let H := sofar.find instOrdNat.compare N.name
  match H with
  | .some v => (v, sofar)
  | .none =>
      match N.parents with
      | [] => (0, sofar.insert instOrdNat.compare N.name 0)
      | ps => Id.run do
          let mut max := 0
          let mut store := sofar
          for p in ps do
            let l? := store.find instOrdNat.compare p
            match l? with
            | .some l => if l > max then max := l
            | _ =>
                let .some np := DAG.findNode D p | pure ()
                let (nl,ns) := DAGnode.getLevel' D store np
                store := ns
                if nl > max then max := nl
          return (max+1, (store.insert instOrdNat.compare N.name (max+1)))


def DAG.getLevelz (D : DAG α Nat)  : (RBNode Nat (fun _ => Nat)) :=
  List.foldl (fun memo N => (DAGnode.getLevel' D memo N).2) {} D


def test_dag : DAG Unit Nat := [⟨1,(),[2,3]⟩,⟨2,(),[4]⟩,⟨3,(),[4]⟩,⟨4,(),[]⟩]

def Lean.RBNode.toList (t : RBNode α (fun _ => β)) : List (α × β ) := t.revFold (fun ps k v => (k, v)::ps) []

#eval (DAG.getLevelz test_dag).toList


def embed_to_expr (embed : Array (Option NodeCst)) --(impInfo : List miniBind)
  (size : Nat) (dict : PersistentHashMap ℕ FVarId) (info : ConstantInfo) : MetaM Expr := do
  let proArg ← ((List.range size).foldl (fun l i => (embed.getD i .none) :: l) []).mapM
      (fun x => match x with
                | .none => return .some (← Meta.mkFreshExprMVar .none)
                | .some (.ofCst e) =>
                      match (CExpr.toExpr e) with
                      | .none => return .none
                      | .some ex => return .some ex
                | .some (.ofNode im) => return .some (Expr.fvar (dict.find! im))
      )
  dbg_trace s!"Ready for Printing ; proArgg: {proArg}"
  --let args : List Expr := ((List.map₂ (proArg) impInfo (fun x i => match i with | .inst => .none | _ => x)).reduceOption).reverse
  -- TODO : replace instances with mvars, without fucking up, which is gonna be hard
  let args : List Expr := ((proArg).reduceOption).reverse
  return mkAppN (.const info.name (info.levelParams.map Level.param)) args.toArray

def score_embed_by_applis_depths (embed : Array (Option NodeCst)) (depths : (RBNode Nat (fun _ => Nat))) (cst_score : Nat) (trafo_depth : Nat → Nat) (combine_scores : List Nat → Nat) : Nat :=
  let res := Id.run do
    let mut out := []
    for a in embed do
      match a with
      | .some (.ofCst _) => out := cst_score :: out
      | .some (.ofNode i) =>
          let .some d := depths.find instOrdNat.compare i | pure ()
          out := (trafo_depth d) :: out
      | .none => pure ()
    return out
  combine_scores res


#check PersistentHashMap.insert
#check PersistentHashMap.find?


def score_embed_by_applis_scores (embed : Array (Option NodeCst)) (scores : PersistentHashMap FVarId Nat ) (dict : PersistentHashMap ℕ FVarId)
  (cst_score : Nat) (trafo_score : Nat → Nat) (combine_scores : List Nat → Nat) : Nat :=
  let res := Id.run do
    let mut out := []
    for a in embed do
      match a with
      | .some (.ofCst _) => out := cst_score :: out
      | .some (.ofNode i) =>
          let .some id := dict.find? i | pure ()
          let .some d := scores.find? id | pure ()
          out := (trafo_score d) :: out
      | .none => pure ()
    return out
  combine_scores res


def getIffHead (thm_type : Expr) : Option (Expr × Expr) :=
  let H := Expr.getForallBody thm_type
  let (h,as) := Expr.getAppFnArgs H
  if h = `Iff
  then
    .some (as[0]!, as[1]!)
  else
    .none

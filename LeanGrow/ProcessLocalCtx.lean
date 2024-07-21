
import LeanGrow.CExpr
import LeanGrow.DAGstruct
import Mathlib

open Lean




def get_Ltx_names (ctx : LocalContext) : List Name :=
  let cctx := ctx.decls.toList.tail.reduceOption.map LocalDecl.type
  (cctx.map Expr.getConstNames).join

elab "testing_get_names_ltx" : tactic => do
  let ltx ← getLCtx
  IO.println (get_Ltx_names ltx)


example (n m p : Nat) (h : Odd (n+m)) (h2 : Even n) (h3 : (fun x : Even n => p) h2 = 42) : True :=
  by
  testing_get_names_ltx
  trivial

--#exit


-- # Local Context to DAG representation


/-
Notes:

- Maybe this procedure is useless. If we can embed via (CExpr × Expr), sending CExpr.nodes to Expr.fvar directly ?

- Types from the local context may not be in a normal form ??? Or are they ? This might cause problems when matching on syntactive equality

-/

--#exit

structure output where
  ctype : CExpr
  parents : List Nat
  counter : Nat
  ctx : PersistentHashMap FVarId Nat
  ctx' : PersistentHashMap Nat FVarId


def orderHyps_wFvar (c : PersistentHashMap FVarId Nat) (c' : PersistentHashMap Nat FVarId) (hyps : List (Expr × miniBind)) : (DAG CExpr Nat) × (PersistentHashMap FVarId Nat) × (PersistentHashMap Nat FVarId) :=
  let rec abstractFvars_collectParents (e : Expr) (f : miniBind) (ctx : PersistentHashMap FVarId Nat) (ctx' : PersistentHashMap Nat FVarId) (count : Nat) : output:=
    let res :=
        match e with
        | .fvar i => match ctx.find? i with
                    | .none => ⟨.node count (.ofFvar i), [count], count + 1, ctx.insert i count, ctx'.insert count i⟩
                    | .some x => ⟨.node x (.ofFvar i), [x], count , ctx, ctx'⟩
        | .app l r => let L := abstractFvars_collectParents l .default ctx ctx' count ;
                      let R := abstractFvars_collectParents r .default L.ctx L.ctx' L.counter;
                      ⟨.app L.ctype R.ctype, L.parents ++ R.parents, R.counter, R.ctx, R.ctx'⟩
        | .lam n l r B => let L := abstractFvars_collectParents l .default ctx ctx' count ;
                          let R := abstractFvars_collectParents r .default L.ctx L.ctx' L.counter;
                          ⟨.lam n L.ctype R.ctype B, L.parents ++ R.parents, R.counter, R.ctx, R.ctx'⟩
        | .forallE n l r B => let L := abstractFvars_collectParents l .default ctx ctx' count ;
                              let R := abstractFvars_collectParents r .default L.ctx L.ctx' L.counter;
                              ⟨.forallE n L.ctype R.ctype B, L.parents ++ R.parents, R.counter, R.ctx, R.ctx'⟩
        | .mdata _ e => abstractFvars_collectParents e .default ctx ctx' count
        | .proj n i e => let r := abstractFvars_collectParents e .default ctx ctx' count ; {r with ctype := .proj n i r.ctype}
        | x => ⟨x.toCExpr, [], count, ctx, ctx'⟩
    match f with
    | .inst => {res with ctype := .wrapInst res.ctype}
    | _ => res

  let rec go (l : List (Expr × miniBind)) (ctx : PersistentHashMap FVarId Nat) (ctx' : PersistentHashMap Nat FVarId) (count : Nat) (hmm : Nat) : (DAG CExpr Nat) × (PersistentHashMap FVarId Nat) × (PersistentHashMap Nat FVarId) :=
    match l with
    | [] => ([], ctx, ctx')
    | h :: rest =>
          let ⟨res, deps, new_count , new_ctx , new_ctx'⟩ := abstractFvars_collectParents h.1 h.2 ctx ctx' (count)
          let sofar := go rest new_ctx new_ctx' (new_count) (hmm + 1)
          let deps_fix := List.dedup deps
          (⟨hmm, res, deps_fix⟩ :: sofar.1 , sofar.2)
  go hyps c c' 0 1


--#exit

/-- dag nodes from 1 to size-/
def orderHyps_fromLocalCtx (ctx : LocalContext) : (SizedDAG CExpr Nat) × (PersistentHashMap FVarId Nat) × (PersistentHashMap Nat FVarId) :=
  let init_ctx := ctx.foldl
      (fun (c : (PersistentHashMap Nat FVarId × Nat)) d => (c.1.insert c.2 d.fvarId ,c.2 +1))
      ({}, 0)
  let init_ctx' := ctx.foldl
      (fun (c : (PersistentHashMap FVarId Nat × Nat)) d => (c.1.insert d.fvarId c.2 ,c.2 +1))
      ({}, 0)
  let cctx := ctx.decls.toList.tail
  let mkHyps (cctx : List (Option LocalDecl)) : List Expr :=
    cctx.reduceOption.map LocalDecl.type
    -- tail cause fist part of local context is impl info ???
  let hyps := mkHyps cctx
  let (dag, c, c') := orderHyps_wFvar init_ctx'.1 init_ctx.1 (hyps.map (fun e => (e, .default)))
  (⟨cctx.length, dag ⟩, c, c')


--#exit

elab "testin" : tactic => do
  let g ← Elab.Tactic.getMainGoal
  g.withContext do
    let ctx ← getLCtx
    let spice := orderHyps_fromLocalCtx ctx
    --logInfo m!"{ctx.decls.toList.reduceOption.map LocalDecl.userName}"
    IO.println s!"{instToStringFormat.toString (repr spice.1)}"

elab "testin_2" : tactic => do
  let g ← Elab.Tactic.getMainGoal
  g.withContext do
    let ctx ← getLCtx
    let spice := DAG.find_sinks (orderHyps_fromLocalCtx ctx).1 true --(((DAG.find_sinks (orderHyps_fromLocalCtx ctx).1).map DAGnode.data).map CExpr.getConstNames).join.map Name.toString
    --logInfo m!"{ctx.decls.toList.reduceOption.map LocalDecl.userName}"
    IO.println s!"{instToStringFormat.toString (repr spice)}"

example (n m p : Nat) (h : Odd (n+m)) (h2 : Even n) (h3 : (fun x : Even n => p) h2 = 42) : True :=
  by
  testin
  trivial


example (n m p : Nat) (h : Odd (n+m)) (h2 : Even n) (h3 : (fun x : Even n => p) h2 = 42) : True :=
  by
  testin_2
  trivial

example (l : List ℕ) (a : ℕ) (h : a ∈ l) : True :=
  by
  testin_2
  trivial



-- # Concluding notes

-- merge dag and name extraction so that we traverse local decls only once
-- or not, no idea if the compiler optimisees one or if there's even a difference ...

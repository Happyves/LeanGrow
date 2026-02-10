
/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import LeanGrowBeta.Search.IntroTree.Types
import LeanGrowBeta.Search.BackTree.Types
import LeanGrowBeta.Search.API.UnifClaches


open Lean Meta



/-

**Crutial notes**
- We have to try intro on propagated goals, because we may not have introed
  binders that had tnodes in their types, which may now have been replaced
  with an assignement, allowing for intro. (we'll have to check that we don't
  loop between intros and propagation)

-/


#check Expr.onAllSubtermsWiWorkerCpsSkipTravState

def Lean.Level.propagate
  (l1 : LocalContext) (l2 : LocalInstances)
  (u : Level) (affected : Bool) (la : ListProd3 Nat Nat Level)
  : MetaM (Prod4 Level Bool LocalContext LocalInstances) := do
  let ⟨r,b,l1,l2⟩ ← u.onAllSubtermsWiWorkerCpsSkipTravState l1 l2 affected (fun l affected l1 l2 => do
    match l with
    | .param (.num (.num _ bI) pI) =>
        match la.find? (fun b p _ => b == bI && p == pI) with
        | .some _ _ e => return ⟨(.error e), true,l1,l2⟩
        | _ => return ⟨(.ok l), affected,l1,l2⟩
    | _ => return ⟨(.ok l), affected,l1,l2⟩)
  match r with
  | .ok r | .error r => return ⟨r,b,l1,l2⟩

def Lean.Expr.propagate
  (l1 : LocalContext) (l2 : LocalInstances)
  (e : Expr) (ta : ListProd3 Nat Nat Expr) (la : ListProd3 Nat Nat Level)
  : MetaM (Prod4 Expr Bool LocalContext LocalInstances) := do
  e.onAllSubtermsWiWorkerCpsSkipTravState l1 l2 false (fun e _ affected l1 l2 => do
    match e with
    | .fvar ⟨.num (.num _ bI) pI⟩ =>
        match ta.find? (fun b p _ => b == bI && p == pI) with
        | .some _ _ e => return ⟨(.error e), true,l1,l2⟩
        | _ => return ⟨(.ok e), affected,l1,l2⟩
    | .sort u => do
        let ⟨u,affected ,l1,l2⟩ ← u.propagate l1 l2 affected la
        return ⟨(.error (Expr.sort u)), affected,l1,l2⟩
    | .const n us => do
      let ⟨ls,affected ,l1,l2⟩ ← us.foldlM (fun ⟨ls, affected,l1,l2⟩ u => do
        let ⟨u,affected ,l1,l2⟩ ← u.propagate l1 l2 affected la
        return ⟨u :: ls, affected,l1,l2⟩) (⟨[], affected,l1,l2⟩ : Prod4 _ _ _ _)
      return ⟨(.error (Expr.const n ls.reverse)), affected,l1,l2⟩
    | x => return ⟨(.ok x),affected,l1,l2⟩
    )



#check ListProd3.find?

#check whnfR





partial def BackTree.propagateForBackAssembly
  (l1 : LocalContext) (l2 : LocalInstances)
  (id_gen_goal : Nat) (unif_claches : ListProd Nat (List Nat)) (bt : BackTree)
  (propaGs: ListProd Nat Expr) (goalSpawn : Array (OptionProd Nat Nat))
  (ta : ListProd3 Nat Nat Expr) (unif_id : List Nat)
  : MetaM (Prod4 Nat (ListProd Nat Expr) BackTree (Array (OptionProd Nat Nat))) :=
  -- trace set Tracing.Flags.none in
  let goalPropaCase (id_gen_goal : Nat) (propaGs: ListProd Nat Expr) (goalSpawn : Array (OptionProd Nat Nat))
    (go : Nat → ListProd Nat Expr → Array (OptionProd Nat Nat) →  BackTree → MetaM (Prod5 BackTree Nat (ListProd Nat Expr) (List Nat) (Array (OptionProd Nat Nat) )))
    (pass goal_id : Nat) (type : Expr) (bdirs gdirs : List Nat) (args : List BackTree)
    (x : BackTree) (prefixB : Nat → Nat → Expr → List Nat → List Nat → List BackTree → BackTree) :
    MetaM (Prod5 BackTree Nat (ListProd Nat Expr) (List Nat)  (Array (OptionProd Nat Nat))) := do
      let ⟨newtype, affected,l1,l2⟩ ← type.propagate l1 l2 ta .nil
      if !affected
      then
        mtrace on .zero with s!"[propagateForBackAssembly] type is unaffected {← ppExpr type}"
        return ⟨x, id_gen_goal, propaGs, [],goalSpawn⟩
      else
        mtrace on .zero with s!"[propagateForBackAssembly] type is affected {← ppExpr type}"
        let ⟨args,id_gen_goal,propaGs,nGs,goalSpawn⟩ ← args.foldlM (fun ⟨args,id_gen_goal,propaGs,nGs,goalSpawn⟩ bt => do
          let ⟨a,id_gen_goal,propaGs,nnGs,goalSpawn⟩ ← go  id_gen_goal propaGs goalSpawn bt
          mtrace on .zero with s!"[propagateForBackAssembly] id_gen_goal : {id_gen_goal}"
          mtrace on .zero with s!"[propagateForBackAssembly] a : {← a.pp 0}"
          mtrace on .zero with s!"[propagateForBackAssembly] propaGs : {← propaGs.foldlM ListProd.nil (fun x y z => return .cons x (← ppExpr y) z)}"
          mtrace on .zero with s!"[propagateForBackAssembly] nnGs : {nnGs}"
          return ⟨a :: args, id_gen_goal,propaGs, nnGs ++ nGs,goalSpawn⟩) (⟨[],id_gen_goal,propaGs,[],goalSpawn⟩ : Prod5 (List BackTree) Nat (ListProd Nat Expr) (List Nat) (Array (OptionProd Nat Nat)))
        let newBr := BackTree.ofPropa pass unif_id id_gen_goal newtype [] [] []
        let redtype ← WhnfR newtype l1 l2
          -- ↑ Should perform β and ι, but not always δ
        mtrace on .zero with s!"[propagateForBackAssembly] redtype : {redtype}"
        if redtype == newtype
        then
          let res := prefixB pass goal_id type bdirs (gdirs ++ [id_gen_goal]) (newBr :: args)
          return ⟨res, id_gen_goal + 1, .cons (id_gen_goal) newtype propaGs, nGs ++ ([id_gen_goal]), goalSpawn.push (goalSpawn[id_gen_goal]!)⟩
        else
          let newBr2 := BackTree.ofPropa pass unif_id (id_gen_goal + 1) redtype [] [] []
          let res := prefixB pass goal_id type bdirs (gdirs.append [id_gen_goal, (id_gen_goal + 1)]) (newBr :: newBr2 :: args)
          return ⟨res, (id_gen_goal + 2), .cons (id_gen_goal + 1) redtype (.cons (id_gen_goal) newtype propaGs), nGs.append [id_gen_goal, (id_gen_goal + 1)], goalSpawn.pushN (goalSpawn[id_gen_goal]!) 2⟩
  let rec go (id_gen_goal : Nat) (propaGs: ListProd Nat Expr) (goalSpawn : Array (OptionProd Nat Nat))
    : BackTree → MetaM (Prod5 BackTree Nat (ListProd Nat Expr) (List Nat) (Array (OptionProd Nat Nat)))
    | x@(.fail ..) | x@(.ofUni ..) => return ⟨x,id_gen_goal,propaGs,[],goalSpawn⟩
    | x@(.ofGoal pass goal_id type bdirs gdirs args) =>
        goalPropaCase id_gen_goal propaGs goalSpawn go pass goal_id type bdirs gdirs args x (.ofGoal)
    | x@(.ofPropa pass u_id goal_id type bdirs gdirs args) => do
        if unifClashOfMemoMulti u_id unif_id unif_claches
        then
          mtrace on .zero with s!"[propagateForBackAssembly] clash of u_id {u_id} and unif_id {unif_id}, stopp propagation"
          return ⟨x,id_gen_goal,propaGs,[],goalSpawn⟩
        else
          goalPropaCase id_gen_goal propaGs goalSpawn go pass goal_id type bdirs gdirs args x (.ofPropa · u_id)
    | (.ofBack pass back_id mdata thm bdirs gdirs args) => do
        let mut id_gen_goal := id_gen_goal
        let mut propaGs := propaGs
        let mut nGs := []
        let mut gdirs := gdirs
        let mut args := args
        let mut gS := goalSpawn
        for i in [:args.size] do
          let bt := args[i]!
          let ⟨nbt,nst,npropaGs,nnGs,ngoalSpawn⟩ ← go id_gen_goal propaGs gS bt
          mtrace on .zero with s!"[propagateForBackAssembly] id_gen_goal : {id_gen_goal}"
          mtrace on .zero with s!"[propagateForBackAssembly] nbt : {← nbt.pp 0}"
          mtrace on .zero with s!"[propagateForBackAssembly] propaGs : {← propaGs.foldlM ListProd.nil (fun x y z => return .cons x (← ppExpr y) z)}"
          mtrace on .zero with s!"[propagateForBackAssembly] nnGs : {nnGs}"
          args := args.set! i nbt
          gdirs := gdirs.modify i (fun ds => ds ++ nnGs)
          nGs := nGs ++ nnGs
          propaGs := npropaGs
          id_gen_goal := nst
          gS := ngoalSpawn
        let res := BackTree.ofBack pass back_id mdata thm bdirs gdirs args
        return ⟨res,id_gen_goal,propaGs,nGs,gS⟩
    | (.ofIntro pass back_id gnIdxAndTy bdirs gdirs args) => do
        -- treated like an unaffected ofGoal/ofPropa
        let ⟨args,id_gen_goal,propaGs,nGs,goalSpawn⟩ ← args.foldlM (fun ⟨args,id_gen_goal,propaGs,nGs,goalSpawn⟩ bt => do
          let ⟨a,id_gen_goal,propaGs,nnGs,goalSpawn⟩ ← go id_gen_goal propaGs goalSpawn bt
          mtrace on .zero with s!"[propagateForBackAssembly] id_gen_goal : {id_gen_goal}"
          mtrace on .zero with s!"[propagateForBackAssembly] a : {← a.pp 0}"
          mtrace on .zero with s!"[propagateForBackAssembly] propaGs : {← propaGs.foldlM ListProd.nil (fun x y z => return .cons x (← ppExpr y) z)}"
          mtrace on .zero with s!"[propagateForBackAssembly] nnGs : {nnGs}"
          return ⟨a :: args, id_gen_goal, propaGs, nGs++ nnGs, goalSpawn⟩)
          (⟨[],id_gen_goal,propaGs,[], goalSpawn⟩ : Prod5 (List BackTree) Nat (ListProd Nat Expr) (List Nat) (Array (OptionProd Nat Nat)))
        return ⟨.ofIntro pass back_id gnIdxAndTy bdirs (gdirs ++ nGs) args, id_gen_goal, propaGs, nGs, goalSpawn⟩
  do
  mtrace on .one with s!"[propagateForBackAssembly] bt start : {← bt.pp 0}"
  let ⟨bt,id_gen_goal,propaGs,_, goalSpawn⟩ ← go id_gen_goal propaGs goalSpawn bt
  mtrace on .one with s!"[propagateForBackAssembly] bt stop : {← bt.pp 0}"
  return ⟨id_gen_goal, propaGs, bt, goalSpawn⟩



partial def BackTree.addUnis (pass : Nat) (bt : BackTree)
  (unif_id : List Nat) (ta : ListProd3 Nat Nat Expr)
  : BackTree :=
  trace set TracingFlags.none in
  -- trace on .one with s!"[BackTree.addUnis] call on pass {pass} unif_id {unif_id} bt {← bt.pp 0}" in
  let affectedBids := ta.foldl [] (fun x _ _ R => R.orderedInsertOrLeave x)
  trace on .zero with s!"[BackTree.addUnis] affectedBids : {affectedBids}" in
  let rec go : BackTree → BackTree
    | x@(.fail ..) | x@(.ofUni ..) =>  x
    | x@(.ofGoal _ j t bdirs gdirs ts) =>
        if (bdirs.orderedIntersect affectedBids).isEmpty
        then x
        else .ofGoal pass j t bdirs gdirs (ts.mapTRR go)
    | x@(.ofPropa _ i j t bdirs gdirs ts) =>
        if (bdirs.orderedIntersect affectedBids).isEmpty
        then x
        else .ofPropa pass i j t bdirs gdirs (ts.mapTRR go)
    | x@(.ofIntro _ j bvs bdirs gdirs ts) =>
        match ta.find? (fun x y _ => x == j && y == 0) with
        | .none =>
            if (bdirs.orderedIntersect affectedBids).isEmpty
            then x
            else .ofIntro pass j bvs bdirs gdirs (ts.mapTRR go)
        | .some _ _ val =>
            let new : BackTree := .ofUni pass unif_id val
            if (bdirs.orderedIntersect affectedBids).isEmpty
            then .ofIntro pass j bvs bdirs gdirs (new :: ts)
            else .ofIntro pass j bvs bdirs gdirs (new :: (ts.mapTRR go))
    | x@(.ofBack _ i md n bdirs gdirs ts) => Id.run do
        let mut ts := ts
        let mut affected := false
        for j in [:ts.size] do
          match ta.find? (fun x y _ => x == i && y == j) with
          | .none =>
              if !((bdirs[j]!.orderedIntersect affectedBids).isEmpty)
              then
                affected := true
                ts := ts.modify j go
          | .some _ _ val =>
              affected := true
              let new : BackTree := .ofUni pass unif_id val
              if !((bdirs[j]!.orderedIntersect affectedBids).isEmpty)
              then
                ts := ts.modify j go
              -- indetation matters, do ↓ in all cases
              ts := ts.modify j (fun t =>
                match t with
                | .ofGoal _ a b c d ks => .ofGoal pass a b c d (new :: ks)
                | _ => panic s!"[BackTree.addUnis] ill formed tree, expected ofGoal"
                )
        if affected
        then return .ofBack pass i md n bdirs gdirs ts
        else return x
  go bt

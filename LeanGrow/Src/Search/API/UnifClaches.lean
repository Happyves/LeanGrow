
/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import LeanGrow.Src.Utils.Std.List
import LeanGrow.Src.Data.Amalgames
import LeanGrow.Src.Search.Types


open Lean Meta


def unifClashOfMemo (u v : Nat) (unif_claches : ListProd Nat (List Nat)) : Bool :=
  let rec help (u v : Nat) : ListProd Nat (List Nat) → Bool
    | .nil => false
    | .cons x L more =>
        match compare u x with
        | .gt => help u v more
        | .lt => false
        | .eq => L.orderedContains v
  if u < v then help u v unif_claches else help v u unif_claches


def unifClashOfComp
  (l1 : LocalContext) (l2 : LocalInstances)
  (unif_assign : Array ((ListProd3 Nat Nat Expr) × (ListProd3 Nat Nat Level)))
  (ta : ListProd3 Nat Nat Expr) (la : ListProd3 Nat Nat Level) ( u : Nat)
  : MetaM Bool :=
  do
  mtracing
  let rec @[specialize] clash? {α : Sort _} (eq : α → α → MetaM Bool) (ref : ListProd3 Nat Nat α) : ListProd3 Nat Nat α → MetaM Bool
    | .nil => return false
    | .cons i j e more => do
        let rec @[specialize] inner : ListProd3 Nat Nat α → MetaM Bool
          | .nil => return false
          | .cons I J E More => do
              if i == I && j == J
              then
                mtrace on .zero with s!"[unifClashOfComp] matching index pair {i} {j}"
                if ← eq e E
                then
                  mtrace on .zero with s!"[unifClashOfComp] eq"
                  inner More
                else
                  mtrace on .zero with s!"[unifClashOfComp] not eq"
                  return true
              else inner More
        if ← inner ref
        then return true
        else clash? eq ref more
  let clashE := clash? (fun x y => do return (← defEqWiMv x y l1 l2).isSome)
  let clashL := clash? (fun x y => do return (← defEqWiMv (.sort x) (.sort y) l1 l2).isSome)
  let vs := unif_assign[u]!
  if ← clashE vs.1 ta
  then return true
  else
    clashL vs.2 la




partial def unifClashOfMemoMulti (u v : List Nat) (unif_claches : ListProd Nat (List Nat)) : Bool :=
  let rec help (u v : Nat) : ListProd Nat (List Nat) → (Bool × ListProd Nat (List Nat))
    | x@(.nil) => (false,x)
    | .cons x L more =>
        match compare u x with
        | .gt => help u v more
        | .lt => (false, more)
        | .eq => (L.orderedContains v, more)
  let rec go (unif_claches : ListProd Nat (List Nat)) : List Nat → List Nat → Bool
    | [], _ => false
    | _, [] => false
    | A@(ah :: aT) , B@(bh :: bT) =>
        if ah ≤ bh
        then
          if ah == bh
          then go unif_claches aT bT
          else
            let (cl?, unif_claches) := help ah bh unif_claches
            if cl?
            then true
            else go unif_claches aT B
        else
          let (cl?, unif_claches) := help bh ah unif_claches
          if cl?
          then true
          else go unif_claches A bT
  (go unif_claches u v)



def addUnifClashToMemo (u v : Nat) (unif_claches : ListProd Nat (List Nat)) : ListProd Nat (List Nat) :=
  let rec help (u v : Nat) : ListProd Nat (List Nat) → ListProd Nat (List Nat)
    | x@(.nil) => .cons u [v] x
    | y@(.cons x L more) =>
        match compare u x with
        | .gt => .cons x L (help u v more)
        | .lt => .cons u [v] y
        | .eq =>
            let L := L.orderedInsertOrLeave v
          .cons x L more
  if u < v then help u v unif_claches else help v u unif_claches

#eval compare 1 2
#eval compare 2 1


/--
**Important** ta and la may contain tnodes : these should be mvarified, and we should make
sure theat they're always in context after they're added, and always clear their assignement
-/
def computeNewClashesCore
  (l1 : LocalContext) (l2 : LocalInstances)
  (unif_claches : ListProd Nat (List Nat))
  (unif_assign : Array ((ListProd3 Nat Nat Expr) × (ListProd3 Nat Nat Level)))
  (new_uni_id : Nat) (ta : ListProd3 Nat Nat Expr) (la : ListProd3 Nat Nat Level)
  : MetaM (ListProd Nat (List Nat)) :=
  do
  mtracing
  let rec @[specialize] clash? {α : Sort _} (eq : α → α → MetaM Bool) (ref : ListProd3 Nat Nat α) : ListProd3 Nat Nat α → MetaM Bool
    | .nil => return false
    | .cons i j e more => do
        let rec @[specialize] inner : ListProd3 Nat Nat α → MetaM Bool
          | .nil => return false
          | .cons I J E More => do
              if i == I && j == J
              then
                mtrace on .zero with s!"[computeNewClashesCore] matching index pair {i} {j}"
                if ← eq e E
                then
                  mtrace on .zero with s!"[computeNewClashesCore] eq"
                  inner More
                else
                  mtrace on .zero with s!"[computeNewClashesCore] not eq"
                  return true
              else inner More
        if ← inner ref
        then return true
        else clash? eq ref more
  let clashE := clash? (fun x y => do return (← defEqWiMv x y l1 l2).isSome)
  let clashL := clash? (fun x y => do return (← defEqWiMv (.sort x) (.sort y) l1 l2).isSome)
  let rec main (i nxUid : Nat) (nxCs : List Nat) (todo : ListProd Nat (List Nat)) : MetaM (ListProd Nat (List Nat)) := do
    if i < unif_assign.size
    then
      mtrace on .zero with s!"[computeNewClashesCore] i {i} nxUid {nxUid}"
      if i < nxUid
      then
        let as := unif_assign[i]!
        if (← clashE as.1 ta) || (← clashL as.2 la)
        then
          mtrace on .zero with s!"[computeNewClashesCore] clash"
          let res ← main (i+1) nxUid nxCs todo
          return .cons i [new_uni_id] res -- uni ids added in increasing order, hence i < new_uni_id
        else
          mtrace on .zero with s!"[computeNewClashesCore] no clash"
          main (i+1) nxUid nxCs todo
      else
        let as := unif_assign[i]!
        if (← clashE as.1 ta) || (← clashL as.2 la)
        then
          mtrace on .zero with s!"[computeNewClashesCore] clash"
          match todo with
          | .nil =>
            let res ← main (i+1) unif_assign.size [] todo
            return .cons nxUid (nxCs ++ [new_uni_id]) res
          | .cons nU nC nTodo =>
            let res ← main (i+1) nU nC nTodo
            return .cons nxUid (nxCs ++ [new_uni_id]) res
        else
          mtrace on .zero with s!"[computeNewClashesCore] no clash"
          main (i+1) nxUid nxCs todo
    else
      return .nil
  do
  clearMvarAssignments
  mtrace on .zero with s!"[computeNewClashesCore] call to incorporate new_uni_id {new_uni_id} with assignements"
  ta.foldlM () (fun i j T _ => do mtrace on .zero with s!"[introWiLtxMain] indices {i} {j} type {← ppExpr T}" ; pure ())
  la.foldlM () (fun i j T _ => do mtrace on .zero with s!"[introWiLtxMain] indices {i} {j} type {repr T}" ; pure ())
  match unif_claches with
  | .nil => main 0 unif_assign.size [] unif_claches
  | .cons nxUid nxCs todo => main 0 nxUid nxCs todo




/--
**Important** ta and la may contain tnodes : these should be mvarified, and we should make
sure theat they're always in context after they're added, and always clear their assignement
-/
def computeNewClashesMain {IndexColType : Type _}
  (l1 : LocalContext) (l2 : LocalInstances)
  (st : SearchState IndexColType)
  (ta : ListProd3 Nat Nat Expr) (la : ListProd3 Nat Nat Level)
  : MetaM (SearchState IndexColType) := do
  let new ← computeNewClashesCore l1 l2 st.unif_claches st.unif_assign st.id_gen_uni ta la
  return {st with unif_claches:= new, unif_assign := st.unif_assign.push (ta, la), id_gen_uni := st.id_gen_uni + 1}

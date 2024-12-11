
import Lean
import LeanGrow.F.Utils.Expr.ConstNames
import LeanGrow.F.Utils.Trie.Sorted
import Mathlib.Data.List.Basic

open Lean

/-
- fold over (← getEnv).constants
- maintain CTrie Nat where vals are hight
- maintain stack of thms to consider, starting with singlton the thm considered
- consider stack top : if in Trie, skip, else ↓ (can occur if appeared in proof of two separate thms used in main proof)
- get constants of proofs, filter those that are thms
- if names not in Trie, add them on stack, recurse
- else, get their hight, find max hight, set as current hight
- once stack empty, add entry to Trie which is maintained hight + 1 at key the initial thm

-/


def ConstantInfo.isThmOrAx : ConstantInfo → Bool
  | .thmInfo _ | .axiomInfo _ => true
  | _ => false

def ConstantInfo.valueD (defo : Expr) : ConstantInfo → Expr
  | .defnInfo {value := r, ..} => r
  | .thmInfo  {value := r, ..} => r
  | _                         => defo




private partial def step (env : Environment)
  (heights : CTrie Nat) (argNum : List Nat) (hc : List Nat) (stack : List Name) : CTrie Nat :=
    let updateMax (H : Nat) : List Nat → List Nat
      | [] => []
      | h :: more => (max h H) :: more
    let UpdateMax (H : Nat) : List Nat → List Nat
      | [] => []
      | [h] => [(max h H)]
      | h₁ :: h₂ :: more => (max h₂ (max h₁ H)) :: more
    let dec : List Nat → Bool × List Nat
      | [] => (false,[])
      | c :: more => if c = 0 then (true, more) else (false, (c - 1) :: more)
    let rec split (hs : List Nat) (todos : List Name) : List Name → (List Nat × List Name)
      | [] => (hs,todos)
      | n :: more =>
          match heights.sorted_find? n.toString with
          | .some H => split (H :: hs) todos more
          | .none => split hs (n :: todos) more
    dbg_trace s!"\n\nargNum : {argNum}\nhc : {hc}\nstack : {stack}\ntrie : {CTrie.toList heights}"
    match stack with
    | [] => heights
    | nx :: more =>
        match heights.sorted_find? nx.toString with
        | .some H =>
            let (done?,nArgNum) := dec argNum
            if done?
            then
              match more with
              | s :: next =>
                  let nMxs := UpdateMax H hc
                  step env (heights.sorted_insert s.toString (nMxs.headD 0)) nArgNum nMxs.tail next
              | [] => {}
            else
              step env heights nArgNum (updateMax H hc) more
        | .none =>
            match (env.constants.find! nx).value? with
            | .none => -- axiom
                let (done?,nArgNum) := dec argNum
                if done?
                then
                  match more with
                  | s :: next =>
                      let nMxs := UpdateMax 1 hc
                      step env ((heights.sorted_insert nx.toString 0).sorted_insert s.toString (nMxs.headD 0)) nArgNum nMxs.tail next
                  | [] => {}
                else
                  step env (heights.sorted_insert nx.toString 0) nArgNum (updateMax 0 hc) more
            | .some V =>
                  let csts :=  (Expr.getConstNamesF V).dedup.filter (fun x => ConstantInfo.isThmOrAx (env.constants.find! x))
                  let (hs, todos) := split [] [] csts
                  let H? := hs.maximum?
                  match H?, todos with
                  | .some H, _ :: _ => step env heights ((todos.length - 1) :: argNum) (0 :: H :: hc) (todos ++ stack)
                  | .none, _ :: _ => step env heights ((todos.length - 1) :: argNum) (0 :: 0 :: hc) (todos ++ stack)
                  | .some H, [] =>
                        let (done?,nArgNum) := dec argNum
                        if done?
                        then
                          match more with
                          | s :: next =>
                              let nMxs := UpdateMax (H+1) hc
                              step env ((heights.sorted_insert nx.toString H).sorted_insert s.toString (nMxs.headD 0)) nArgNum nMxs.tail next
                          | [] => {}
                        else
                          step env (heights.sorted_insert nx.toString (H+1)) nArgNum (updateMax (H+1) hc) more
                  | .none, [] => -- axiom
                        let (done?,nArgNum) := dec argNum
                        if done?
                        then
                          match more with
                          | s :: next =>
                              let nMxs := UpdateMax 1 hc
                              step env ((heights.sorted_insert nx.toString 0).sorted_insert s.toString (nMxs.headD 0)) nArgNum nMxs.tail next
                          | [] => {}
                        else
                          step env (heights.sorted_insert nx.toString 0) nArgNum (updateMax 0 hc) more

#check List.append_assoc

#check Nat.add_comm

private def test : CoreM Unit := do
  let res := step (← getEnv) {} [] [] [`List.append_assoc] --[`Nat.mul_le_mul]
  IO.print (CTrie.toList res)

-- #eval test


def build_height_weights (env : Environment) (N : Name) : CTrie Nat :=
  let modules := env.header.moduleNames.map (N.isPrefixOf ·)
  env.constants.map₁.fold (fun T n info =>
    if modules[env.const2ModIdx[n].get! (α := Nat)]!
    then
      if ConstantInfo.isThmOrAx info
      then step env T [] [] [n]
      else T
    else T
    ) {}

private def test2 : CoreM Unit := do
  IO.print (CTrie.toList (build_height_weights (← getEnv) `Mathlib.Data.List))

-- #eval test2

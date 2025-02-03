
import LeanGrow.F.Data.CExpr.ReduceInferMuggle.Control

open Lean Meta


private def dumbUnfoldDefinition? (fctx : FixCtx) (e : CExpr) : Option CExpr :=
  match e with
  | .app _ _ =>
      let (f,as) := CExpr.getApp e
      match f with
      | .const n lvl =>
          match fctx.cstData.find? n.toString with
          | .some (.wVal us _ v) => .some (CExpr.mkApp (CExpr.instantiateLevelParams v us lvl) as) -- we don't beta since this is done by whnf core ??
          | _ => .none
      | _ => .none
  | _ => .none


#check Meta.reduceNative?
#check reduceNat?
-- we don't use ↑, though we should
partial def CExpr.whnfDelta (fctx : FixCtx) (e : CExpr) : CExpr :=
  let red := CExpr.whnf fctx e
  match dumbUnfoldDefinition? fctx red with
  | .none => e
  | .some new => CExpr.whnfDelta fctx new

def CExpr.whnfDeltaOnce (fctx : FixCtx) (e : CExpr) : CExpr :=
  let red := CExpr.whnf fctx e
  match dumbUnfoldDefinition? fctx red with
  | .none => e
  | .some new => CExpr.whnf fctx new

def CExpr.whnfDeltaOnce' (fctx : FixCtx) (e : CExpr) : CExpr :=
  match dumbUnfoldDefinition? fctx e with
  | .none => e
  | .some new => CExpr.whnf fctx new

partial def cexprReduce (fctx : FixCtx) (e : CExpr) : CExpr :=
  let T := CExpr.whnf fctx (CExpr.inferType fctx e)
  match T with
  | .sort .zero => e
  | _ =>
    let E := CExpr.whnfDelta fctx e
    match E with
    | .app f a => .app (cexprReduce fctx  f) (cexprReduce fctx  a)
    | .lam n t b i => .lam n t (cexprReduce fctx b) i
      -- ↑↓ massive bug potential here, since there may be loose bvars ! Not an issue in ReduceInferSmart
    | .forallE n t b i => .forallE n t (cexprReduce fctx  b) i
    | .proj n i a => .proj n i (cexprReduce fctx  a)
    | x => x



def List.productWith (f : α → β → γ) (l : List α) (L : List β) : List γ :=
  let rec iter (w : α) (done : List γ) : List β → List γ
    | [] => done
    | x :: xs => iter w ((f w x) :: done) xs
  (l.map (iter · [] L)).join

#eval List.productWith (fun a b => a+b) [1,2] [3,4]


def List.productWith' (f : α → β → γ) (l : List α) (L : List β) : List γ :=
  let rec iter (done : List γ) : List α → List β → List γ
    | [],[] => done
    | [], _ :: r => iter done l r
    | x :: xs, y :: ys => iter ((f x y) :: done) xs (y :: ys)
    | _,_ => done
  iter [] l L

#eval List.productWith' (fun a b => a+b) [1,2] [3,4]


--#exit

def List.MYpwFilter (R : α → α → Prop) [DecidableRel R] (l : List α) : List α :=
  l.foldr (fun x IH => if ∀ y ∈ IH, R x y then x :: IH else IH) []

def List.MYdedup [BEq α] (l : List α) : List α :=
  l.MYpwFilter (· != ·)


def List.MYdedupF [BEq α] (l : List α) : List α :=
  let rec go (done : List α) : List α → List α
    | [] => done
    | x :: xs => if done.contains x then go done xs else go (x :: done) xs
  go [] l

partial def cexprReduceShallow (fctx : FixCtx) (fuel : Nat) (e : CExpr) : List CExpr :=
  if fuel = 0
  then [e]
  else
  let T := CExpr.whnf fctx (CExpr.inferType fctx  e)
  --let TT := CExpr.whnf fctx  (CExpr.inferType fctx (T))
  -- wih T, causes stack overflow
  -- don't know if this is due to not having a bvar context, and would be solved by ReduceSmart
  -- or whether this is an error in the implementation of infer/whnf ...
  -- or because somewhere in the search, we don't add gnodes correctly ...
  -- or because the muggle version is jsut horribly implemented and causes overflows ...
  -- The technical debt here is unbearable
  -- one more reason to use Lean's versions
    match T with -- T is a proof
    | .sort .zero => [e]
    | _ =>
      let red := CExpr.whnf fctx  e
      let del := CExpr.whnfDeltaOnce' fctx red
      match del with
      | .app f a =>
        let F := cexprReduceShallow fctx  (fuel - 1) f
        let A := cexprReduceShallow fctx  (fuel - 1) a
        let combi := (List.productWith' (fun x y => CExpr.app x y) F A) --.map (CExpr.whnf fctx ) -- do we ?
        (red :: del :: combi).MYdedupF
      | .lam n t b i =>
        let res := ((cexprReduceShallow fctx  (fuel - 1) b).map (CExpr.lam n t · i))
        (red :: del :: res).MYdedupF
      | .forallE n t b i =>
        let res := ((cexprReduceShallow fctx (fuel - 1) b).map (CExpr.forallE n t · i))
        (red :: del :: res).MYdedupF
      | .proj n i a =>
        let res := ((cexprReduceShallow fctx (fuel - 1) a).map (CExpr.proj n i ·))
        (red :: del :: res).MYdedupF
      | x => [x]

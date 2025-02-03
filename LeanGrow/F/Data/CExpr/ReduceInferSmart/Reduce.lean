
import LeanGrow.F.Data.CExpr.ReduceInferSmart.Top

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
partial def cexprWhnfDelta (fctx : FixCtx) (bvarCtx : List CExpr) (e : CExpr) : CExpr :=
  let red := cexprWhnf fctx bvarCtx e
  match dumbUnfoldDefinition? fctx red with
  | .none => e
  | .some new => cexprWhnfDelta fctx bvarCtx new

def cexprWhnfDeltaOnce (fctx : FixCtx) (bvarCtx : List CExpr) (e : CExpr) : CExpr :=
  let red := cexprWhnf fctx bvarCtx e
  match dumbUnfoldDefinition? fctx red with
  | .none => e
  | .some new => cexprWhnf fctx bvarCtx new


def cexprWhnfDeltaOnce' (fctx : FixCtx) (bvarCtx : List CExpr) (e : CExpr) : CExpr :=
  match dumbUnfoldDefinition? fctx e with
  | .none => e
  | .some new => cexprWhnf fctx bvarCtx new


partial def cexprReduce (fctx : FixCtx) (bvarCtx : List CExpr) (e : CExpr) : CExpr :=
  let T := cexprWhnf fctx bvarCtx (cexprInferType fctx bvarCtx e)
  match T with
  | .sort .zero => e
  | _ =>
    let E := cexprWhnfDelta fctx bvarCtx e
    match E with
    | .app f a => .app (cexprReduce fctx bvarCtx f) (cexprReduce fctx bvarCtx a)
    | .lam n t b i => .lam n t (cexprReduce fctx (t :: bvarCtx) b) i
    | .forallE n t b i => .forallE n t (cexprReduce fctx (t :: bvarCtx) b) i
    | .proj n i a => .proj n i (cexprReduce fctx bvarCtx a)
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



def List.MYpwFilter (R : α → α → Prop) [DecidableRel R] (l : List α) : List α :=
  l.foldr (fun x IH => if ∀ y ∈ IH, R x y then x :: IH else IH) []

def List.MYdedup [BEq α] (l : List α) : List α :=
  l.MYpwFilter (· != ·)

def List.MYdedupF [BEq α] (l : List α) : List α :=
  let rec go (done : List α) : List α → List α
    | [] => done
    | x :: xs => if done.contains x then go done xs else go (x :: done) xs
  go [] l


--#exit


partial def cexprReduceShallow (fctx : FixCtx) (bvarCtx : List CExpr) (fuel : Nat) (e : CExpr) : List CExpr :=
  if fuel = 0
  then [e]
  else
  let T := cexprWhnf fctx bvarCtx (cexprInferType fctx bvarCtx (cexprInferType fctx bvarCtx e))
  -- refer to the massive issues described in the muggle version
    match T with
    | .sort .zero => [e]
    | _ =>
      let red := cexprWhnf fctx bvarCtx e
      let del := cexprWhnfDeltaOnce' fctx bvarCtx red
      match del with
      | .app f a =>
        let F := cexprReduceShallow fctx bvarCtx (fuel - 1) f
        let A := cexprReduceShallow fctx bvarCtx (fuel - 1) a
        let combi := (List.productWith' (fun x y => CExpr.app x y) F A) --.map (cexprWhnf fctx bvarCtx) -- do we ?
        (red :: del :: combi).MYdedupF
      | .lam n t b i =>
        let res := ((cexprReduceShallow fctx (t :: bvarCtx) (fuel - 1) b).map (CExpr.lam n t · i))
        (red :: del :: res).MYdedupF
      | .forallE n t b i =>
        let res := ((cexprReduceShallow fctx (t :: bvarCtx) (fuel - 1) b).map (CExpr.forallE n t · i))
        (red :: del :: res).MYdedupF
      | .proj n i a =>
        let res := ((cexprReduceShallow fctx (bvarCtx) (fuel - 1) a).map (CExpr.proj n i ·))
        (red :: del :: res).MYdedupF
      | x => [x]

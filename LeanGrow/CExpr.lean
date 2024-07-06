
import Lean

open Lean

inductive OriginalData where
| ofBvar : Nat → OriginalData
| ofFvar (fvarId : FVarId)
deriving Inhabited, BEq, Repr

inductive CExpr where
| node : Nat → OriginalData → CExpr
| bvar : Nat → CExpr
| sort : Level → CExpr
| const : Name → List Level → CExpr
| app : CExpr → CExpr → CExpr
| lam : Name → CExpr → CExpr → BinderInfo → CExpr
| forallE : Name → CExpr → CExpr → BinderInfo → CExpr
| letE : Name → CExpr → CExpr → CExpr → Bool → CExpr
| lit : Literal → CExpr
| proj : Name → Nat → CExpr → CExpr
| wrapInst : CExpr → CExpr
| failed : CExpr
deriving Inhabited, BEq, Repr


def CExpr.toStringImp : CExpr → String
| .node i d => s!"CExpr.node {i} {instToStringFormat.toString (repr d)}"
| .bvar i =>  s!"CExpr.bvar {i} "
| .sort l => s!"CExpr.sort {l} "
| .const n ll => s!"CExpr.const {n} {ll}"
| .app f a => s!"(CExpr.app {f.toStringImp} {a.toStringImp})"
| .lam _ t b _ => s!"CExpr.lam {t.toStringImp} {b.toStringImp}"
| .forallE _ t b _ => s!"CExpr.forallE {t.toStringImp} {b.toStringImp}"
| .letE _ t v b _ => s!"CExpr.letE {t.toStringImp} {v.toStringImp} {b.toStringImp}"
| .lit l => s!"CExpr.lit {instToStringFormat.toString (repr l)}"
| .proj t i b => s!"CExpr.proj {t} {i} {b.toStringImp}"
| .wrapInst e => s!"CExpr.wrapInst {CExpr.toStringImp e}"
| .failed => "CExpr.failed"

instance : ToString CExpr where
  toString := CExpr.toStringImp

#synth ToString CExpr

def Lean.Expr.toCExpr : Expr → CExpr
| .bvar i => .bvar i
| .fvar _ => .failed
| .mvar _ => .failed
| .sort l => .sort l
| .const n ll => .const n ll
| .app f a => .app (Expr.toCExpr f) (Expr.toCExpr a)
| .lam n t b i => .lam n (Expr.toCExpr t) (Expr.toCExpr b) i
| .forallE n t b i => .forallE n (Expr.toCExpr t) (Expr.toCExpr b) i
| .letE n t v b i => .letE n (Expr.toCExpr t) (Expr.toCExpr v) (Expr.toCExpr b) i
| .lit l => .lit l
| .proj t i b => .proj t i (Expr.toCExpr b)
| .mdata _ e => (Expr.toCExpr e)


def HashMap.merge [BEq α] [Hashable α] (a b : HashMap α β) : HashMap α β :=
      a.fold (init := b) fun r k v => r.insert k v

--#exit


def match_helper (l r : Option (List (Nat × NodeCst))) : Option (List (Nat × NodeCst)) :=
 match l, r with
 | .some x, .some y => .some (x ++ y)
 | .some x, .none => .some x
 | .none , .some y => .some y
 | _, _ => .none


inductive NodeCst where
| ofNode (i : Nat)
| ofCst (c : CExpr)
deriving Inhabited, Repr, BEq


instance : ToString NodeCst where
      toString := fun c => match c with
                           | .ofNode i => s!"node {i}"
                           | .ofCst c => CExpr.toStringImp c
--#exit

def CExpr.hasNodes : CExpr → Bool
| .node _ _ => true
| .app f a => (CExpr.hasNodes f) && (CExpr.hasNodes a)
| .lam _ t b _ => (CExpr.hasNodes t) && (CExpr.hasNodes b)
| .forallE _ t b _ => (CExpr.hasNodes t) && (CExpr.hasNodes b)
| .letE _ t v b _ => (CExpr.hasNodes t) && (CExpr.hasNodes b) && (CExpr.hasNodes v)
| .proj _ _ b => (CExpr.hasNodes b)
| .wrapInst e => (CExpr.hasNodes e)
| _ => false



/-- proposes parent assignement (no assignement of node itself)-/
def CExpr.MatchAssign (l r : CExpr) : Option (List (Nat × NodeCst)) :=
  match l, r with
  | .node i _ , .node j _ => .some [(i, .ofNode j)]
  | .node i _ , e => if e.hasNodes then .none else .some [(i, .ofCst e)] -- scary of circular stuff ... to investigate...
  | .bvar i , .bvar j =>  if i == j then .some [] else .none
  | .sort _, .sort _ => .some [] -- if l == l' then .some [] else .none -- raised issues as params in lib not the same as file
  | .const n ll, .const n' ll' => if (n == n') && (ll == ll') then .some [] else .none
  | .app f a, .app f' a' =>
        let of := CExpr.MatchAssign  f f' ;
        let oa := CExpr.MatchAssign  a a' ;
        match_helper of oa
  | .lam _ t b _, .lam _ t' b' _ =>
        let of := CExpr.MatchAssign  t t' ;
        let oa := CExpr.MatchAssign  b b' ;
        match_helper of oa
  | .forallE _ t b _, .forallE _ t' b' _ =>
        let of := CExpr.MatchAssign  t t' ;
        let oa := CExpr.MatchAssign  b b' ;
        match_helper of oa
  | .letE _ t v b _, .letE _ t' v' b' _ =>
        let ot := CExpr.MatchAssign  t t' ;
        let ov := CExpr.MatchAssign  v v' ;
        let ob := CExpr.MatchAssign  b b' ;
        match_helper (match_helper ot ov) ob
  | .lit l, .lit l' => if l == l' then .some [] else .none
  | .proj t i b, proj t' i' b' => if (t == t') && (i == i') then CExpr.MatchAssign b b' else .none
  | _ , _ => .none




inductive miniBind where
| default | impl --| inst


def naiveGetHyps (ty : Expr) : (List (Expr × miniBind)) :=
  match ty with
  | .forallE _ h b i =>
        let H := (naiveGetHyps b)
        match i with
        | .default => (h, .default)  :: H
        --| .instImplicit => (h :: H, .inst :: I)
        | _ => (h , .impl) :: H
  | .mdata  _ e => naiveGetHyps e
  | _ => []



def CExpr.toExpr : CExpr → Option Expr
| .node _ _ => .none
| .bvar i => .some (.bvar i)
| .sort l => .some (.sort l)
| .const n ll => .some (.const n ll)
| .app f a =>
      match CExpr.toExpr f, CExpr.toExpr a with
      | .some f', .some a' => .some (.app f' a')
      | _ , _ => .none
| .lam n t b B =>
      match CExpr.toExpr t, CExpr.toExpr b with
      | .some t', .some b' => .some (.lam n t' b' B)
      | _ , _ => .none
| .forallE n t b B =>
      match CExpr.toExpr t, CExpr.toExpr b with
      | .some t', .some b' => .some (.forallE n t' b' B)
      | _ , _ => .none
| .letE n t v b B =>
      match CExpr.toExpr t, CExpr.toExpr v, CExpr.toExpr b with
      | .some t', .some v', .some b' => .some (.letE n t' v' b' B)
      | _ , _, _ => .none
| .lit l => .some (.lit l)
| .proj t i b => (.proj t i) <$> (CExpr.toExpr b)
| .wrapInst e => (CExpr.toExpr e)
| .failed => .none



def Expr.getConstNames : Expr → List Name
| .const n _ => [n]
| .app l r => (Expr.getConstNames l) ++ (Expr.getConstNames r)
| .lam _ l r _ => (Expr.getConstNames l) ++ (Expr.getConstNames r)
| .forallE _ l r _ => (Expr.getConstNames l) ++ (Expr.getConstNames r)
| .letE _ t l r _ => (Expr.getConstNames t) ++(Expr.getConstNames l) ++ (Expr.getConstNames r)
| .mdata _ e => (Expr.getConstNames e)
| .proj n _ e => n :: (Expr.getConstNames e)
| _ => []

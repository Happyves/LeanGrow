
import Lean

open Lean

inductive OriginalData where
| ofBvar : Nat → OriginalData
| ofFvar (fvarId : FVarId) : OriginalData
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
| .failed => "CExpr.failed"

instance : ToString CExpr where
  toString := CExpr.toStringImp


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


def match_helper (l r : Option (List (Nat ×Nat))) : Option (List (Nat ×Nat)) :=
 match l, r with
 | .some x, .some y => .some (x ++ y)
 | .some x, .none => .some x
 | .none , .some y => .some y
 | _, _ => .none

/-- proposes parent assignement (no assignement of node itself)-/
def CExpr.MatchAssign (l r : CExpr) : Option (List (Nat × Nat)) :=
  match l, r with
  | .node i _ , .node j _ => .some [(i, j)]
  | .bvar i , .bvar j =>  if i == j then .some [] else .none
  | .sort l, .sort l' => .some [] -- if l == l' then .some [] else .none
  | .const n ll, .const n' ll' => dbg_trace s!"Sanity" ; if (n == n') && (ll == ll') then .some [] else .none
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


def Expr.getConstNames : Expr → List Name
| .const n _ => [n]
| .app l r => (Expr.getConstNames l) ++ (Expr.getConstNames r)
| .lam _ l r _ => (Expr.getConstNames l) ++ (Expr.getConstNames r)
| .forallE _ l r _ => (Expr.getConstNames l) ++ (Expr.getConstNames r)
| .letE _ t l r _ => (Expr.getConstNames t) ++(Expr.getConstNames l) ++ (Expr.getConstNames r)
| .mdata _ e => (Expr.getConstNames e)
| .proj n _ e => n :: (Expr.getConstNames e)
| _ => []

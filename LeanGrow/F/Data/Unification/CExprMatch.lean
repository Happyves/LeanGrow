
import LeanGrow.F.Data.CExpr.API
import Lean.Data.HashMap

open Lean


def HashMap.merge [BEq α] [Hashable α] (a b : HashMap α β) : HashMap α β :=
      a.fold (init := b) fun r k v => r.insert k v


inductive NodeCst where
| ofNode (i : Nat)
| ofCst (c : CExpr)
deriving Inhabited, Repr, BEq


def match_helper (l r : Option (List (Nat × NodeCst))) : Option (List (Nat × NodeCst)) :=
      match l, r with
      | .some x, .some y => .some (x ++ y)
      | _, _ => .none

-- /-- proposes parent assignement (no assignement of node itself)-/
-- def CExpr.MatchAssign (l r : CExpr) : Option (List (Nat × NodeCst)) :=
--   match l, r with
--   | .node i _ , .node j _ => .some [(i, .ofNode j)]
--   | .node i _ , e => if e.hasNodes then .none else .some [(i, .ofCst e)]
--   | .bvar i , .bvar j =>  if i == j then .some [] else .none
--   | .sort _, .sort _ => .some [] -- if l == l' then .some [] else .none -- raised issues as params in lib not the same as file
--   | .const n _, .const n' _ => if (n == n') --&& (ll == ll')
--                                   then .some [] else .none
--   | .app f a, .app f' a' =>
--         let of := CExpr.MatchAssign  f f' ;
--         let oa := CExpr.MatchAssign  a a' ;
--         match_helper of oa
--   | .lam _ t b _, .lam _ t' b' _ =>
--         let of := CExpr.MatchAssign  t t' ;
--         let oa := CExpr.MatchAssign  b b' ;
--         match_helper of oa
--   | .forallE _ t b _, .forallE _ t' b' _ =>
--         let of := CExpr.MatchAssign  t t' ;
--         let oa := CExpr.MatchAssign  b b' ;
--         match_helper of oa
--   | .letE _ t v b _, .letE _ t' v' b' _ =>
--         let ot := CExpr.MatchAssign  t t' ;
--         let ov := CExpr.MatchAssign  v v' ;
--         let ob := CExpr.MatchAssign  b b' ;
--         match_helper (match_helper ot ov) ob
--   | .lit l, .lit l' => if l == l' then .some [] else .none
--   | .proj t i b, proj t' i' b' => if (t == t') && (i == i') then CExpr.MatchAssign b b' else .none
--   | _ , _ => .none



def Array.assignOrFail [BEq α] (A? : Option (Array (Option α))) (i : Nat) (val : α) : Option (Array (Option α)) :=
      match A? with
      | .some A =>
            match A.get! i with
            | .none => .some (A.set! i val)
            | .some wal => if wal == val then .some A else .none
      | _ => .none



partial def CExpr.MatchAssignAF (l r : CExpr) : Option (Array (Option NodeCst)) :=
      let R := CExpr.getNodesMaxIdxF l
      match R with
      | .some S =>
            let Aout := Array.mkArray (S+1) .none
            let rec go : List (CExpr × CExpr) → Option (Array (Option NodeCst))
            | [] => .some Aout
            | nx :: L =>
                  match nx with
                  | (.node i _ , .node j _) => Array.assignOrFail (go L) i (.ofNode j)
                  | (.node i _ , e) => Array.assignOrFail (go L) i (.ofCst e)
                  | (.bvar i , .bvar j) =>  if i == j then go L else .none
                  | (.sort _, .sort _) => go L
                  | (.const n _, .const n' _) => if (n == n') then go L else .none
                  | (.app f a, .app f' a') => go ((f,f') :: (a,a') :: L)
                  | (.lam _ t b _, .lam _ t' b' _) => go ((t,t') :: (b,b') :: L)
                  | (.forallE _ t b _, .forallE _ t' b' _) => go ((t,t') :: (b,b') :: L)
                  | (.letE _ t v b _, .letE _ t' v' b' _) => go ((t,t') :: (v,v') :: (b,b') :: L)
                  | (.lit l, .lit l') => if l == l' then go L else .none
                  | (.proj t i b, proj t' i' b') => if (t == t') && (i == i') then go ((b, b') :: L) else .none
                  | (_ , _) => .none
            go [(l,r)]
      | _ => .none


import LeanGrow.F.Data.RExprTests.RExpr

open Lean





def match_helper (l r : Option (List (Nat × NodeExpr))) : Option (List (Nat × NodeExpr)) :=
      match l, r with
      | .some x, .some y => .some (x ++ y)
      | _, _ => .none



def List.assignOrFail [BEq α] (A? : Option (List (Nat × α))) (i : Nat) (val : α) : Option (List (Nat × α)) :=
      match A? with
      | .some A =>
            match A.find? (fun x => (Prod.fst x) == i) with
            | .some wal => if wal.2 == val then .some A else .none
            | _ => .some ((i,val) :: A)
      | _ => .none


partial def RExpr.MatchAssignLFF (delta : Name → RExpr) (l r : RExpr) : Option (List (Nat × NodeExpr)) :=
      let rec go (go? : Bool) (Aout : Option (List (Nat × NodeExpr))) (todo : List (RExpr × RExpr)) : Option (List (Nat × NodeExpr)) :=
      if go?
      then
            match todo with
            | [] => Aout
            | nx :: L =>
                  match nx with
                  | (.lnode i .none, .lnode j t) => let Aup := List.assignOrFail Aout i (.ofLNode j t) ; go true Aup L
                  | (.lnode i .none, .gnode j) => let Aup := List.assignOrFail Aout i (.ofGNode j) ; go true Aup L
                  | (.lnode i .none, e) => let Aup := List.assignOrFail Aout i (.ofRExpr e) ; go true Aup L
                  | (.bvar i , .bvar j) => go (i == j) Aout L
                  | (.sort _, .sort _) => go true Aout L
                  | (.axm n _, .axm n' _) =>  go (n == n')  Aout L
                  | (.ctor n _, .ctor n' _) =>  go (n.name == n'.name)  Aout L
                  | (.indt n _, .indt n' _) =>  go (n.name == n'.name)  Aout L
                  | (.quo n _, .quo n' _) =>  go (n.name == n'.name) Aout L
                  | (.deltaDef n _, .deltaDef n' _) =>
                        if n == n'
                        then go true Aout L
                        else go true Aout ((delta n, delta n'):: L)
                  | (.deltaDef n _, r) => go true Aout ((delta n, r):: L)
                  | (r, .deltaDef n _) => go true Aout ((r, delta n):: L)
                  | (.deltaFun n _, .deltaFun n' _) =>
                        if n == n'
                        then go true Aout L
                        else go true Aout ((delta n, delta n'):: L)
                  | (.deltaFun n _, r) => go true Aout ((delta n, r):: L)
                  | (r, .deltaFun n _) => go true Aout ((r, delta n):: L)
                  | (.proof v t, .proof v' t') =>
                        match go true Aout [(v,v')] with
                        | .some M => go true (.some M) L
                        | .none =>
                              match go true Aout [(t,t')] with
                              | .some M =>  go true (.some M) L
                  -- todo
                  | (.app f a, .app f' a') => go true Aout ((f,f') :: (a,a') :: L)
                  | (.lam _ t b _, .lam _ t' b' _) => go true Aout ((t,t') :: (b,b') :: L)
                  | (.forallE _ t b _, .forallE _ t' b' _) => go true Aout ((t,t') :: (b,b') :: L)
                  | (.letE _ t v b _, .letE _ t' v' b' _) => go true Aout ((t,t') :: (v,v') :: (b,b') :: L)
                  | (.lit l, .lit l') => go (l == l') Aout L
                  | (.proj t i b, .proj t' i' b') => go ((t == t') && (i == i')) Aout ((b, b') :: L)
                  | (_ , _) => .none
      else .none
      go true (.some []) [(l,r)]

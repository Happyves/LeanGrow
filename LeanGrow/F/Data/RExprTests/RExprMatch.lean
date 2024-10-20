
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



def List.get?_tail : Nat → List α → Option (α × List α)
| 0, x :: l => .some (x, l)
| n+1, _ :: l => List.get?_tail n l
| _, [] => .none



partial def RExpr.MatchAssignLFF (delta : Name → RExpr) (l r : RExpr) : Option (List (Nat × NodeExpr)) :=
      let rec go (go? : Bool) (Aout : Option (List (Nat × NodeExpr))) (todo : List ((RExpr × List RExpr) × (RExpr × List RExpr))) : Option (List (Nat × NodeExpr)) :=
      if go?
      then
            match todo with
            | [] => Aout
            | nx :: L =>
                  match nx with
                  -- unify
                  | ((.lnode i .none, _), (.lnode j t, _)) => let Aup := List.assignOrFail Aout i (.ofLNode j t) ; go true Aup L
                  | (.lnode i .none, .gnode j, _) => let Aup := List.assignOrFail Aout i (.ofGNode j) ; go true Aup L
                  | (.lnode i .none, e, _) => let Aup := List.assignOrFail Aout i (.ofRExpr e) ; go true Aup L
                  -- eq
                  | (.lit l, .lit l', _) => go (l == l') Aout L
                  | (.bvar i , .bvar j, _) => go (i == j) Aout L
                  | (.sort _, .sort _, _) => go true Aout L
                  | (.axm n _, .axm n' _, _) =>  go (n == n')  Aout L
                  | (.ctor n _, .ctor n' _, _) =>  go (n.name == n'.name)  Aout L
                  | (.indt n _, .indt n' _, _) =>  go (n.name == n'.name)  Aout L
                  | (.quo n _, .quo n' _, _) =>  go (n.name == n'.name) Aout L
                  -- nabla
                  | (.deltaFun n l, .lam _ _ (.app more (.bvar 0)) _, ctx) =>
                        go true Aout ((.deltaFun n l, more, ctx) :: L)
                  | (.lam _ _ (.app more (.bvar 0)) _, .deltaFun n l, ctx) =>
                        go true Aout ((more, .deltaFun n l, ctx) :: L)
                  | (.lam n t b l, .lam _ _ (.app more (.bvar 0)) _, ctx) =>
                        go true Aout ((.lam n t b l, more, ctx) :: L)
                  | (.lam _ _ (.app more (.bvar 0)) _, .lam n t b l, ctx) =>
                        go true Aout ((more, .lam n t b l, ctx) :: L)
                  -- delta
                  | (.deltaDef n _, .deltaDef n' _, ctx) =>
                        if n == n'
                        then go true Aout L
                        else go true Aout ((delta n, delta n', ctx):: L)
                  | (.deltaDef n _, r, ctx) => go true Aout ((delta n, r, ctx):: L)
                  | (r, .deltaDef n _, ctx) => go true Aout ((r, delta n, ctx):: L)
                  | (.deltaFun n _, .deltaFun n' _, ctx) =>
                        if n == n'
                        then go true Aout L
                        else go true Aout ((delta n, delta n', ctx):: L)
                  | (.deltaFun n _, r) => go true Aout ((delta n, r, ctx):: L)
                  | (r, .deltaFun n _) => go true Aout ((r, delta n, ctx):: L)
                  -- proof irrelevance
                  | (.proof v t, .proof v' t', ctx) =>
                        match go true Aout [(v,v', ctx)] with
                        | .some M => go true (.some M) L
                        | .none =>
                              match go true Aout [(t,t', ctx)] with
                              | .some M =>  go true (.some M) L
                              -- As can be seen in `Lean.Meta.isDefEqProofIrrel` if the props unify, the proofs are equal
                              -- and we don't have to track this so as to mention prop irrel thms when reconstructing
                              | .none => .none
                  -- regular
                  | (.app f a, .app f' a', ctx) => go true Aout ((f,f', ctx) :: (a,a', ctx) :: L)
                  | (.lam _ t b _, .lam _ t' b' _, ctx) => go true Aout ((t,t', ctx) :: (b,b', ctx) :: L)
                  | (.forallE _ t b _, .forallE _ t' b' _, ctx) => go true Aout ((t,t', ctx) :: (b,b', ctx) :: L)
                  | (.letE _ t v b _, .letE _ t' v' b' _, ctx) => go true Aout ((t,t', ctx) :: (v,v', ctx) :: (b,b', ctx) :: L)
                  | (.proj t i b, .proj t' i' b', ctx) => go ((t == t') && (i == i')) Aout ((b, b', ctx) :: L)
                  -- projection reduction
                  | (.proj n i (.struc n' f), more, ctx) => go (n == n') Aout ((f.get! i, more, ctx) :: L)
                  | (more, .proj n i (.struc n' f), ctx) => go (n == n') Aout ((more, f.get! i, ctx) :: L)
                  -- eta (shouldn't be required if we eta expand in cahce and in query, hence :)
                  | (.struc n p, .struc n' p') => go (n == n') Aout ((List.zip p (p'.map (fun x => (x, ctx)))) ++ L)
                  -- beta
                  | ((.app (.lam _ _ B _) (A), lctx), (more, rctx)) => go true Aout (((B, A :: lctx), (more, rctx)) :: L)
                  | ((more, lctx), (.app (.lam _ _ B _) (A), rctx)) => go true Aout (((more, lctx), (B, A :: rctx)) :: L)
                  | ((.bvar i, lctx) (t, rctx)) =>
                        match List.get?_tail i ltcx with
                        | .some (b,c) => go true Aout (((b,c),(t,rctx)) :: L)
                        | _ => .none
                  -- todo sym and fix ↑
                  -- no match
                  | (_ , _) => .none
      else .none
      go true (.some []) [(l,r)]


#check List.zip

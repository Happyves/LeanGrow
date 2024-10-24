
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
                  | ((.lnode i .none, _), (.gnode j, _)) => let Aup := List.assignOrFail Aout i (.ofGNode j) ; go true Aup L
                  | ((.lnode i .none, _), (e, _)) => let Aup := List.assignOrFail Aout i (.ofRExpr e) ; go true Aup L
                  -- eq
                  | ((.lit l, _), (.lit l', _)) => go (l == l') Aout L
                  | ((.bvar i, _), (.bvar j, _)) => go (i == j) Aout L
                  | ((.sort _, _), (.sort _, _)) => go true Aout L
                  | ((.axm n _, _), (.axm n' _, _)) =>  go (n == n')  Aout L
                  | ((.ctor n _, _), (.ctor n' _, _)) =>  go (n.name == n'.name)  Aout L
                  | ((.indt n _, _), (.indt n' _, _)) =>  go (n.name == n'.name)  Aout L
                  | ((.quo n _, _), (.quo n' _, _)) =>  go (n.name == n'.name) Aout L
                  -- nabla
                  | ((.deltaFun n l, lctx), .lam _ _ (.app more (.bvar 0)) _, rctx) =>
                        go true Aout (((.deltaFun n l, lctx), (more, rctx)) :: L)
                  | ((.lam _ _ (.app more (.bvar 0)) _, lctx), (.deltaFun n l, rctx)) =>
                        go true Aout (((more, lctx), (.deltaFun n l, rctx)) :: L)
                  | ((.lam n t b l, lctx), .lam _ _ (.app more (.bvar 0)) _, rctx) =>
                        go true Aout (((.lam n t b l, lctx), more, rctx) :: L)
                  | ((.lam _ _ (.app more (.bvar 0)) _, lctx), .lam n t b l, rctx) =>
                        go true Aout (((more, lctx), .lam n t b l, rctx) :: L)
                  -- delta
                  | ((.deltaDef n _, lctx), .deltaDef n' _, ctx) =>
                        if n == n'
                        then go true Aout L
                        else go true Aout (((delta n, lctx), delta n', ctx):: L)
                  | ((.deltaDef n _, lctx), r, ctx) => go true Aout (((delta n, lctx), r, ctx):: L)
                  | (r, .deltaDef n _, ctx) => go true Aout ((r, delta n, ctx):: L)
                  | ((.deltaFun n _, lctx), .deltaFun n' _, ctx) =>
                        if n == n'
                        then go true Aout L
                        else go true Aout (((delta n, lctx), delta n', ctx):: L)
                  | ((.deltaFun n _, lctx), r, ctx) => go true Aout (((delta n, lctx), r, ctx):: L)
                  | ((r, lctx), .deltaFun n _, rctx) => go true Aout (((r, lctx), delta n, rctx):: L)
                  -- proof irrelevance
                  | ((.proof v t, lctx), .proof v' t', ctx) =>
                        match go true Aout [((v, lctx),v', ctx)] with
                        | .some M => go true (.some M) L
                        | .none =>
                              match go true Aout [((t, lctx),t', ctx)] with
                              | .some M =>  go true (.some M) L
                              -- As can be seen in `Lean.Meta.isDefEqProofIrrel` if the props unify, the proofs are equal
                              -- and we don't have to track this so as to mention prop irrel thms when reconstructing
                              | .none => .none
                  -- projection reduction
                  | ((.proj n i (.struc n' f), lctx), more, ctx) => go (n == n') Aout (((f.get! i, lctx), more, ctx) :: L)
                  | (more, .proj n i (.struc n' f), ctx) => go (n == n') Aout ((more, f.get! i, ctx) :: L)
                  -- eta (shouldn't be required if we eta expand in cahce and in query, hence :)
                  | ((.struc n p, lctx), .struc n' p', ctx) => go (n == n') Aout ((List.zip (p.map (fun x => (x, lctx))) (p'.map (fun x => (x, ctx)))) ++ L)
                  -- beta
                  | ((.app (.lam _ _ B _) (A), lctx), (more, rctx)) => go true Aout (((B, A :: lctx), (more, rctx)) :: L)
                  | ((more, lctx), (.app (.lam _ _ B _) (A), rctx)) => go true Aout (((more, lctx), (B, A :: rctx)) :: L)
                  -- zeta
                  | ((.letE _ _ v b _, lctx), (more, rctx)) => go true Aout (((b, v :: lctx), (more, rctx)) :: L)
                  | ((more, lctx), (.letE _ _ v b _, rctx)) => go true Aout (((more, lctx), (b, v :: rctx)) :: L)
                  -- beta-zeta
                  | ((.bvar i, lctx), (t, rctx)) =>
                        match List.get?_tail i lctx with
                        | .some (b,c) => go true Aout (((b,c),(t,rctx)) :: L)
                        | _ => .none
                  | ((t, lctx), (.bvar i, rctx)) =>
                        match List.get?_tail i rctx with
                        | .some (b,c) => go true Aout (((t,lctx), (b,c)) :: L)
                        | _ => .none
                  -- todo

                  --iota for struct: .proj .struct should be handled by List.get!

                  -- regular (should be last else β undetected)
                  | ((.app f a, lctx), .app f' a', ctx) => go true Aout (((f, lctx),f', ctx) :: ((a, lctx),a', ctx) :: L)
                  | ((.lam _ t b _, lctx), .lam _ t' b' _, ctx) => go true Aout (((t, lctx),t', ctx) :: ((b, lctx),b', ctx) :: L)
                  | ((.forallE _ t b _, lctx), .forallE _ t' b' _, ctx) => go true Aout (((t, lctx),t', ctx) :: ((b, lctx),b', ctx) :: L)
                  | ((.proj t i b, lctx), .proj t' i' b', ctx) => go ((t == t') && (i == i')) Aout (((b, lctx), b', ctx) :: L)

                  -- no match
                  | (_ , _) => .none
      else .none
      go true (.some []) [((l, []),r, [])]


#check List.zip


/-
**Very important note**
- We should completely ζ reduce all expressions that will be turned into CExpr.
  Probably, its best to get rid of `.letE` in CExpr all together!
  The reason is that we don't have fvars, and we don't want any. ζ would have to
  be handled like δ, with extra pain... Plus, let doesn't appear that often
  in practice and the terms it substitutes aren't that big.
  *Actually*, ζ fits right into the β framework

- eta expand all structures

- only β and ι can be triggered by rewrites
-/

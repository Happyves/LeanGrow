
import LeanGrow.F.Data.CExpr.API

open Lean


def List.assignOrFail [BEq α] (A? : Option (List (Nat × α))) (i : Nat) (val : α) : Option (List (Nat × α)) :=
      match A? with
      | .some A =>
            match A.find? (fun x => (Prod.fst x) == i) with
            | .some wal => if wal.2 == val then .some A else .none
            | _ => .some ((i,val) :: A)
      | _ => .none


inductive SolNodeExpr where
| ofGNode (idx : Nat)
| ofCExpr (ce : CExpr)
deriving Inhabited, BEq, Repr


def List.assignOrFail' [BEq α] (A? : Option (List (Nat × Nat × α))) (i j : Nat) (val : α) : Option (List (Nat × Nat × α)) :=
      match A? with
      | .some A =>
            match A.find? (fun x => x.1 == i && x.2.1 == j) with
            | .some wal => if wal.2.2 == val then .some A else .none
            | _ => .some ((i,j,val) :: A)
      | _ => .none

/-- In the ouput list, fst is the gnode idx, snd is the goal (tag,idx) it unifies with-/
partial def CExpr.MatchAssignSolutions (s g : CExpr) : Option (List (Nat × Nat × SolNodeExpr)) :=
      let rec go (go? : Bool) (Aout : Option (List (Nat × Nat × SolNodeExpr))) (todo : List (CExpr × CExpr)) : Option (List (Nat × Nat × SolNodeExpr)) :=
      if go?
      then
            match todo with
            | [] => Aout
            | nx :: L =>
                  match nx with
                  | (.gnode i _, .lnode j _ (.some t)) => let Aup := List.assignOrFail' Aout t j (.ofGNode i) ; go true Aup L
                  | (e, .lnode j _ (.some t)) => let Aup := List.assignOrFail' Aout t j (.ofCExpr e) ; go true Aup L
                  | (.gnode i _, .gnode j _) => go (i == j) Aout L
                  | (.bvar i , .bvar j) => go (i == j) Aout L
                  | (.sort _, .sort _) => go true Aout L
                  | (.const n _, .const n' _) =>  go (n == n')  Aout L
                  | (.app f a, .app f' a') => go true Aout ((f,f') :: (a,a') :: L)
                  | (.lam _ t b _, .lam _ t' b' _) => go true Aout ((t,t') :: (b,b') :: L)
                  | (.forallE _ t b _, .forallE _ t' b' _) => go true Aout ((t,t') :: (b,b') :: L)
                  | (.letE _ t v b _, .letE _ t' v' b' _) => go true Aout ((t,t') :: (v,v') :: (b,b') :: L)
                  | (.lit l, .lit l') => go (l == l') Aout L
                  | (.proj t i b, .proj t' i' b') => go ((t == t') && (i == i')) Aout ((b, b') :: L)
                  | (_ , _) => .none -- in particular, we don't expect to see `.lnode j _ .none`, since goal CExpr get their lnodes tagged
      else .none
      go true (.some []) [(s,g)]

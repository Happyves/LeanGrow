
import LeanGrow.F.Data.Unification.LevelsUnify

open Lean





def match_helper (l r : Option (List (Nat × NodeExpr))) : Option (List (Nat × NodeExpr)) :=
      match l, r with
      | .some x, .some y => .some (x ++ y)
      | _, _ => .none



def Array.assignOrFail' [BEq α] (A? : Option (Array (Option α))) (i : Nat) (val : α) : Option (Array (Option α)) :=
      match A? with
      | .some A =>
            match A.get! i with
            | .none => .some (A.set! i val)
            | .some wal => if wal == val then .some A else .none
      | _ => .none



partial def CExpr.MatchAssignAF (l r : CExpr) : Option (Array (Option NodeExpr)) :=
      let R := CExpr.getGNodesMaxIdxF l
      match R with
      | .some S =>
            let Aout := Array.mkArray (S+1) .none
            let rec go : List (CExpr × CExpr) → Option (Array (Option NodeExpr))
            | [] => .some Aout
            | nx :: L =>
                  match nx with
                  | (.lnode i _ .none , .lnode j _ t) => Array.assignOrFail' (go L) i (.ofLNode j t)
                  | (.lnode i _ .none , .gnode j _) => Array.assignOrFail' (go L) i (.ofGNode j)
                  | (.lnode i _ .none , e) => Array.assignOrFail' (go L) i (.ofCExpr e)
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


partial def CExpr.MatchAssignAFF (l r : CExpr) : Option (Array (Option NodeExpr)) :=
      let R := CExpr.getGNodesMaxIdxF l
      match R with
      | .some S =>
            let rec go (Aout : Option (Array (Option NodeExpr))) : List (CExpr × CExpr) → Option (Array (Option NodeExpr))
            | [] => Aout
            | nx :: L =>
                  match nx with
                  | (.lnode i _ .none, .lnode j _ t) => let Aup := Array.assignOrFail' Aout i (.ofLNode j t) ; go Aup L
                  | (.lnode i _ .none, .gnode j _) => let Aup := Array.assignOrFail' Aout i (.ofGNode j) ; go Aup L
                  | (.lnode i _ .none, e) => let Aup := Array.assignOrFail' Aout i (.ofCExpr e) ; go Aup L
                  | (.bvar i , .bvar j) =>  if i == j then go Aout L else .none
                  | (.sort _, .sort _) => go Aout L
                  | (.const n _, .const n' _) => if (n == n') then go Aout L else .none
                  | (.app f a, .app f' a') => go Aout ((f,f') :: (a,a') :: L)
                  | (.lam _ t b _, .lam _ t' b' _) => go Aout ((t,t') :: (b,b') :: L)
                  | (.forallE _ t b _, .forallE _ t' b' _) => go Aout ((t,t') :: (b,b') :: L)
                  | (.letE _ t v b _, .letE _ t' v' b' _) => go Aout ((t,t') :: (v,v') :: (b,b') :: L)
                  | (.lit l, .lit l') => if l == l' then go Aout L else .none
                  | (.proj t i b, proj t' i' b') => if (t == t') && (i == i') then go Aout ((b, b') :: L) else .none
                  | (_ , _) => .none
            go (.some (Array.mkArray (S+1) .none)) [(l,r)]
      | _ => .none



def List.assignOrFail [BEq α] (A? : Option (List (Nat × α))) (i : Nat) (val : α) : Option (List (Nat × α)) :=
      match A? with
      | .some A =>
            match A.find? (fun x => (Prod.fst x) == i) with
            | .some wal => if wal.2 == val then .some A else .none
            | _ => .some ((i,val) :: A)
      | _ => .none


partial def CExpr.MatchAssignLFF (l r : CExpr) : Option (List (Nat × NodeExpr)) :=
      let rec go (go? : Bool) (Aout : Option (List (Nat × NodeExpr))) (todo : List (CExpr × CExpr)) : Option (List (Nat × NodeExpr)) :=
      if go?
      then
            match todo with
            | [] => Aout
            | nx :: L =>
                  match nx with
                  | (.lnode i _ .none, .lnode j _ t) => let Aup := List.assignOrFail Aout i (.ofLNode j t) ; go true Aup L
                  | (.lnode i _ .none, .gnode j _) => let Aup := List.assignOrFail Aout i (.ofGNode j) ; go true Aup L
                  | (.lnode i _ .none, e) => let Aup := List.assignOrFail Aout i (.ofCExpr e) ; go true Aup L
                  | (.bvar i , .bvar j) => go (i == j) Aout L
                  | (.sort _, .sort _) => go true Aout L
                  | (.const n _, .const n' _) =>  go (n == n')  Aout L
                  | (.app f a, .app f' a') => go true Aout ((f,f') :: (a,a') :: L)
                  | (.lam _ t b _, .lam _ t' b' _) => go true Aout ((t,t') :: (b,b') :: L)
                  | (.forallE _ t b _, .forallE _ t' b' _) => go true Aout ((t,t') :: (b,b') :: L)
                  | (.letE _ t v b _, .letE _ t' v' b' _) => go true Aout ((t,t') :: (v,v') :: (b,b') :: L)
                  | (.lit l, .lit l') => go (l == l') Aout L
                  | (.proj t i b, .proj t' i' b') => go ((t == t') && (i == i')) Aout ((b, b') :: L)
                  | (_ , _) => .none
      else .none
      go true (.some []) [(l,r)]



partial def CExpr.MatchAssignLFFC (l r : CExpr) : Option (List (Nat × CExpr)) :=
      let rec go (go? : Bool) (Aout : Option (List (Nat × CExpr))) (todo : List (CExpr × CExpr)) : Option (List (Nat × CExpr)) :=
      if go?
      then
            match todo with
            | [] => Aout
            | nx :: L =>
                  match nx with
                  | (.lnode i _ .none, e) => let Aup := List.assignOrFail Aout i e ; go true Aup L
                  | (.bvar i , .bvar j) => go (i == j) Aout L
                  | (.sort _, .sort _) => go true Aout L
                  | (.const n _, .const n' _) =>  go (n == n')  Aout L
                  | (.app f a, .app f' a') => go true Aout ((f,f') :: (a,a') :: L)
                  | (.lam _ t b _, .lam _ t' b' _) => go true Aout ((t,t') :: (b,b') :: L)
                  | (.forallE _ t b _, .forallE _ t' b' _) => go true Aout ((t,t') :: (b,b') :: L)
                  | (.letE _ t v b _, .letE _ t' v' b' _) => go true Aout ((t,t') :: (v,v') :: (b,b') :: L)
                  | (.lit l, .lit l') => go (l == l') Aout L
                  | (.proj t i b, .proj t' i' b') => go ((t == t') && (i == i')) Aout ((b, b') :: L)
                  | (_ , _) => .none
      else .none
      go true (.some []) [(l,r)]



partial def CExpr.MatchAssignLFFCU (l r : CExpr) : Option (List (Nat × CExpr) × List (Name × Level)) :=
      let rec go (go? : Bool) (Aout : Option (List (Nat × CExpr))) (Uout : Option (List (Name × Level))) (todo : List (CExpr × CExpr)) : Option (List (Nat × CExpr) × List (Name × Level)) :=
      if go?
      then
            match todo with
            | [] =>
                  match Aout, Uout with
                  | .some X, .some Y => .some (X,Y)
                  | _, _ => .none
            | nx :: L =>
                  match nx with
                  | (.lnode i _ .none, e) => let Aup := List.assignOrFail Aout i e ; go true Aup Uout L
                  | (.bvar i , .bvar j) => go (i == j) Aout Uout L
                  | (.sort a, .sort b) => let us := univsMerge Uout (univsUnify b.normalize a.normalize) ; go us.isSome Aout us L
                  | (.const n l, .const n' l') =>
                        if (n == n') -- big confusion with CExpr.MatchAssignSolutions' in UnifyForBackWUnis, as thm and query order changed, as ecidence in the use in match_goal
                        then let us := makeUniAssigns l' l ; go us.isSome Aout us L
                        else go false Aout .none L
                  | (.app f a, .app f' a') => go true Aout Uout ((f,f') :: (a,a') :: L)
                  | (.lam _ t b _, .lam _ t' b' _) => go true Aout Uout ((t,t') :: (b,b') :: L)
                  | (.forallE _ t b _, .forallE _ t' b' _) => go true Aout Uout ((t,t') :: (b,b') :: L)
                  | (.letE _ t v b _, .letE _ t' v' b' _) => go true Aout Uout ((t,t') :: (v,v') :: (b,b') :: L)
                  | (.lit l, .lit l') => go (l == l') Aout Uout L
                  | (.proj t i b, .proj t' i' b') => go ((t == t') && (i == i')) Aout Uout ((b, b') :: L)
                  | (_ , _) => .none
      else .none
      go true (.some []) (.some []) [(l,r)]




#exit
-- initial stuff ?


partial def EmbedData.MatchAssignLFF (l r : EmbedData) : Option (List (Nat × NodeExpr)) :=
      let rec go (Aout : Option (List (Nat × NodeExpr))) : List (CExpr × CExpr) → Option (List (Nat × NodeExpr))
      | [] => Aout
      | nx :: L =>
            match nx with
            | (.node i _ , .node j _) => let Aup := List.assignOrFail Aout i (.ofNode j) ; go Aup L
            | (.node i _ , e) => let Aup := List.assignOrFail Aout i (.ofCExpr e) ; go Aup L
            | (.bvar i , .bvar j) =>  if i == j then go Aout L else .none
            | (.sort _, .sort _) => go Aout L
            | (.const n _, .const n' _) => if (n == n') then go Aout L else .none
            | (.app f a, .app f' a') => go Aout ((f,f') :: (a,a') :: L)
            | (.lam _ t b _, .lam _ t' b' _) => go Aout ((t,t') :: (b,b') :: L)
            | (.forallE _ t b _, .forallE _ t' b' _) => go Aout ((t,t') :: (b,b') :: L)
            | (.letE _ t v b _, .letE _ t' v' b' _) => go Aout ((t,t') :: (v,v') :: (b,b') :: L)
            | (.lit l, .lit l') => if l == l' then go Aout L else .none
            | (.proj t i b, .proj t' i' b') => if (t == t') && (i == i') then go Aout ((b, b') :: L) else .none
            | (_ , _) => .none
      go (.some []) [(l.cexpr,r.cexpr)]



#exit

def CExpr.MatchAssign (l r : CExpr) : Option (List (Nat × NodeExpr)) :=
  match l, r with
  | .node i _ , .node j _ => .some [(i, .ofNode j)]
  | .node i _ , e => if e.hasNodes then .none else .some [(i, .ofCExpr e)]
  | .bvar i , .bvar j =>  if i == j then .some [] else .none
  | .sort _, .sort _ => .some [] -- if l == l' then .some [] else .none -- raised issues as params in lib not the same as file
  | .const n _, .const n' _ => if (n == n') --&& (ll == ll')
                                  then .some [] else .none
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

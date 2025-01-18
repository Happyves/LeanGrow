import LeanGrow.F.Data.Unification.LevelsUnify

open Lean


def List.assignOrFailLOCALuni [BEq α] (A? : Option (List (Nat × α))) (i : Nat) (val : α) : Option (List (Nat × α)) :=
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


def List.assignOrFailLOCALuni' [BEq α] (A? : Option (List (Nat × Nat × α))) (i j : Nat) (val : α) : Option (List (Nat × Nat × α)) :=
      match A? with
      | .some A =>
            match A.find? (fun x => x.1 == i && x.2.1 == j) with
            | .some wal => if wal.2.2 == val then .some A else .none
            | _ => .some ((i,j,val) :: A)
      | _ => .none

/-- In the ouput list, fst is the gnode idx, snd is the goal (tag,idx) it unifies with
Inputs: s should be from cache with lnode .nones and g is fromthe quers (matters for universes etc.)
-/
partial def CExpr.MatchAssignSolutions (s g : CExpr) : Option (List (Nat × Nat × SolNodeExpr) × List (Name × Level)) :=
      let rec go (go? : Bool) (Aout : Option (List (Nat × Nat × SolNodeExpr))) (Uout : Option (List (Name × Level))) (todo : List (CExpr × CExpr)) : Option (List (Nat × Nat × SolNodeExpr) × List (Name × Level)) :=
      if go?
      then
            match todo with
            | [] =>
                  match Aout, Uout with
                  | .some X, .some Y => .some (X,Y)
                  | _, _ => .none
            | nx :: L =>
                  match nx with
                  | (.gnode i _, .lnode j _ (.some t)) => let Aup := List.assignOrFailLOCALuni' Aout t j (.ofGNode i) ; go true Aup Uout L
                  | (e, .lnode j _ (.some t)) => let Aup := List.assignOrFailLOCALuni' Aout t j (.ofCExpr e) ; go true Aup Uout L
                  | (.gnode i _, .gnode j _) => go (i == j) Aout Uout L
                  | (.bvar i , .bvar j) => go (i == j) Aout Uout L
                  | (.sort a, .sort b) => let us := univsMerge Uout (univsUnify a.normalize b.normalize) ; go us.isSome Aout us L
                  | (.const n l, .const n' l') =>
                        if (n == n')
                        then let us := makeUniAssigns l l' ; go us.isSome Aout us L
                        else go false Aout .none L
                  | (.app f a, .app f' a') => go true Aout Uout ((f,f') :: (a,a') :: L)
                  | (.lam _ t b _, .lam _ t' b' _) => go true Aout Uout ((t,t') :: (b,b') :: L)
                  | (.forallE _ t b _, .forallE _ t' b' _) => go true Aout Uout ((t,t') :: (b,b') :: L)
                  | (.letE _ t v b _, .letE _ t' v' b' _) => go true Aout Uout ((t,t') :: (v,v') :: (b,b') :: L)
                  | (.lit l, .lit l') => go (l == l') Aout Uout L
                  | (.proj t i b, .proj t' i' b') => go ((t == t') && (i == i')) Aout Uout ((b, b') :: L)
                  | (_ , _) => .none -- in particular, we don't expect to see `.lnode j _ .none`, since goal CExpr get their lnodes tagged
      else .none
      go true (.some []) (.some []) [(s,g)]


/-- In the ouput list, fst is the gnode idx, snd is the goal (tag,idx) it unifies with
Inputs: s should be from cache with lnode .nones and g is fromthe quers (matters for universes etc.)
-/
partial def CExpr.MatchAssignSolutions' (s g : CExpr) : Option (List (Nat × Nat × CExpr) × List (Name × Level)) :=
      let rec go (go? : Bool) (Aout : Option (List (Nat × Nat × CExpr))) (Uout : Option (List (Name × Level))) (todo : List (CExpr × CExpr)) : Option (List (Nat × Nat × CExpr) × List (Name × Level)) :=
      if go?
      then
            match todo with
            | [] =>
                  match Aout, Uout with
                  | .some X, .some Y => .some (X,Y)
                  | _, _ => .none
            | nx :: L =>
                  match nx with
                  | (.gnode i o, .lnode j _ (.some t)) => let Aup := List.assignOrFailLOCALuni' Aout t j (.gnode i o) --; dbg_trace s!"MatchAssignSolutions' match g {i} and l {j}" ;
                        go true Aup Uout L
                  | (e, .lnode j _ (.some t)) => let Aup := List.assignOrFailLOCALuni' Aout t j (e) --; dbg_trace s!"MatchAssignSolutions' match l {j} and expr {repr e}" ;
                        go true Aup Uout L
                  | (.gnode i _, .gnode j _) => go (i == j) Aout Uout L
                  | (.bvar i , .bvar j) => go (i == j) Aout Uout L
                  | (.sort a, .sort b) => let us := univsMerge Uout (univsUnify a.normalize b.normalize) ; go us.isSome Aout us L
                  | (.const n l, .const n' l') =>
                        if (n == n')
                        then let us := makeUniAssigns l l' --; dbg_trace s!"Universe assignements at constant {n} : {us}";
                             go us.isSome Aout us L
                        else go false Aout .none L
                  | (.app f a, .app f' a') => go true Aout Uout ((f,f') :: (a,a') :: L)
                  | (.lam _ t b _, .lam _ t' b' _) => go true Aout Uout ((t,t') :: (b,b') :: L)
                  | (.forallE _ t b _, .forallE _ t' b' _) => go true Aout Uout ((t,t') :: (b,b') :: L)
                  | (.letE _ t v b _, .letE _ t' v' b' _) => go true Aout Uout ((t,t') :: (v,v') :: (b,b') :: L)
                  | (.lit l, .lit l') => go (l == l') Aout Uout L
                  | (.proj t i b, .proj t' i' b') => go ((t == t') && (i == i')) Aout Uout ((b, b') :: L)
                  | (_ , _) => .none -- in particular, we don't expect to see `.lnode j _ .none`, since goal CExpr get their lnodes tagged
      else .none
      go true (.some []) (.some []) [(s,g)]

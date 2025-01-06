
import LeanGrow.F.Data.CExpr.API

open Lean

def List.assignOrFailN [BEq α] (A? : Option (List (Name × α))) (i : Name) (val : α) : Option (List (Name × α)) :=
      match A? with
      | .some A =>
            match A.find? (fun x => (Prod.fst x) == i) with
            | .some wal => if wal.2 == val then .some A else .none
            | _ => .some ((i,val) :: A)
      | _ => .none


#check Level.normalize
-- again, unification isn't up to reductions here
partial def univsUnify (query thm : Level) : Option (List (Name × Level)) :=
      let rec go (go? : Bool) (Aout : Option (List (Name × Level))) (todo : List (Level × Level)) : Option (List (Name × Level)) :=
            if go?
            then
                  match todo with
                  | [] => Aout
                  | nx :: L =>
                        match nx with
                        | (.param u, l) => let Aup := List.assignOrFailN Aout u l ; go true Aup L
                        | (.zero, .zero) => go true Aout L
                        | (.succ a, .succ b) => go true Aout ((a,b) :: L)
                        | (.max a b, .max A B) => go true Aout ((a,A) :: (b,B) :: L)
                        | (.imax a b, .imax A B) => go true Aout ((a,A) :: (b,B) :: L)
                        | (_,_) => go false Aout L
            else .none
      go true (.some []) [(thm,query)]

def univsMerge (A B : Option (List (Name × Level))) : Option (List (Name × Level)) :=
      let rec main (X toAdd: List (Name × Level)) : List (Name × Level) → Option (List (Name × Level))
            | [] => .some (X ++ toAdd)
            | nx :: more =>
                  match X.find? (fun x => x.1 == nx.1) with
                  | .some (_,L) => if Level.isEquiv nx.2 L then main X toAdd more else .none
                                    -- don't know if some sort of substitution should be performed here ...
                  | .none => main X (nx :: toAdd) more
      match A, B with
      | .some a, .some b => main a [] b
      | _, _ => .none

def makeUniAssigns (query thm : List Level) : Option (List (Name × Level)) :=
      let rec go (sofar : Option (List (Name × Level))) : List Level → List Level → Option (List (Name × Level))
            | a :: as, b :: bs =>
                  let u := univsUnify a b
                  if u.isSome
                  then
                        let j := univsMerge sofar u
                        if j.isSome
                        then go j as bs
                        else .none
                  else .none
            | [],[] => sofar
            | _,_ => .none
      go (.some []) query thm

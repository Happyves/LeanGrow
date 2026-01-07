
/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/


import LeanGrow.Src.Data.PathIndexG.Build
import LeanGrow.Src.Data.PathIndexG.Indexing

open Lean Meta

variable {IdxCollType : Type _}

namespace PaInG


-- # Merge

@[specialize, inline]
def help_1
  (union : IdxCollType → IdxCollType → IdxCollType)
  {α : Sort _} (eq : α → α → Bool) (L R : ListProd IdxCollType α) : ListProd IdxCollType α :=
  let rec @[specialize] inner (linds : IdxCollType) (vl : α) (seen : Bool) (done : ListProd IdxCollType α) : ListProd IdxCollType α → ListProd IdxCollType α
    | .nil =>
        if seen then done else .cons linds vl done
    | .cons rinds vr more =>
        if seen
        then inner linds vl seen (.cons rinds vr done) more
        else
          if eq vl vr
          then inner linds vl true (.cons (union linds rinds) vl done) more
          else inner linds vl seen (.cons rinds vr done) more
  L.foldl R (fun linds vl res => inner linds vl false .nil res)

@[specialize, inline]
def help_2
  (union : IdxCollType → IdxCollType → IdxCollType)
  {α : Sort _} (eq : α → α → Bool) [Repr α] (L R : CTrie (ListProd IdxCollType α)) : CTrie (ListProd IdxCollType α):=
  let rec @[specialize] inner (linds : IdxCollType) (vl : α) (seen : Bool) (done : ListProd IdxCollType α) : ListProd IdxCollType α → ListProd IdxCollType α
    | .nil =>
        if seen then done else .cons linds vl done
    | .cons rinds vr more =>
        if seen
        then inner linds vl seen (.cons rinds vr done) more
        else
          if eq vl vr
          then inner linds vl true (.cons (union linds rinds) vl done) more
          else inner linds vl seen (.cons rinds vr done) more
  CTrie.merge (fun L R => L.foldl R (fun linds vl res => inner linds vl false .nil res)) L R

@[specialize, inline]
def help_3
  (union : IdxCollType → IdxCollType → IdxCollType)
  {α : Sort _} (eq : α → α → Bool) (merge : α → α → α) (L R : ListProd IdxCollType α) : ListProd IdxCollType α :=
  let rec @[specialize] inner (linds : IdxCollType) (vl : α) (seen : Bool) (done : ListProd IdxCollType α) : ListProd IdxCollType α → ListProd IdxCollType α
    | .nil =>
        if seen then done else .cons linds vl done
    | .cons rinds vr more =>
        if seen
        then inner linds vl seen (.cons rinds vr done) more
        else
          if eq vl vr
          then inner linds vl true (.cons (union linds rinds) (merge vl vr) done) more
          else inner linds vl seen (.cons rinds vr done) more
  L.foldl R (fun linds vl res => inner linds vl false .nil res)


inductive mergeT (IdxCollType : Type _) where
| nil
| done (_ : PaInG IdxCollType) (nx : mergeT IdxCollType)
| sig1 (nx : mergeT IdxCollType) | sig2 (nx : mergeT IdxCollType) | sig3 (nx : mergeT IdxCollType)
| apa (_ _ : PaInG IdxCollType) (nx : mergeT IdxCollType)
| laf (_ _ : PaInG IdxCollType) (nx : mergeT IdxCollType) | laa (_ _ : PaInG IdxCollType) (nx : mergeT IdxCollType)
| alf (_ _ : PaInG IdxCollType) (nx : mergeT IdxCollType) | ala (_ _ : PaInG IdxCollType) (nx : mergeT IdxCollType)
| lef (_ _ : PaInG IdxCollType) (nx : mergeT IdxCollType) | lea (_ _ : PaInG IdxCollType) (nx : mergeT IdxCollType) | lez (_ _ : PaInG IdxCollType) (nx : mergeT IdxCollType)
| projPre (_ _ : PaInG IdxCollType) (nx : mergeT IdxCollType)
| projPost (name : ByteArray) (idx : Nat) (is : IdxCollType) (nx : mergeT IdxCollType)
| proofsOf (_ _ : PaInG IdxCollType) (nx : mergeT IdxCollType)
| proofs (_ _ : PaInG IdxCollType) (nx : mergeT IdxCollType)
deriving Inhabited

#check 1

@[specialize]
partial def mergeDown
  (union : IdxCollType → IdxCollType → IdxCollType)
  (A B : PaInG IdxCollType)
  (sofar : mergeT IdxCollType) (vals : List (PaInG IdxCollType)) : (mergeT IdxCollType) × (List (PaInG IdxCollType)) :=
  match A, B with
  | .dead, .dead => (.done A sofar,vals)
  | .br .., .dead => (.done A sofar,vals)
  | .dead, .br .. => (.done B sofar, vals)
  | .br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai alf ala ali lef lea lez lei projs proofsOf proofs,
    .br tnodes' lnodes' gnodes' unodes' bvars' sorts' consts' lits' apf' apa' api' laf' laa' lai' alf' ala' ali' lef' lea' lez' lei' projs' proofsOf' proofs' =>
    let nt := help_1 union (· == ·) tnodes tnodes'
    let nl := help_2 union (· == ·) lnodes lnodes'
    let ng := help_1 union (· == ·) gnodes gnodes'
    let nu := help_1 union (· == ·) unodes unodes'
    let nb := help_1 union (· == ·) bvars bvars'
    let ns := help_1 union (· == ·) sorts sorts'
    let nc := help_2 union (· == ·) consts consts'
    let nli := help_1 union (· == ·) lits lits'
    let api := (union api api')
    let lai := (union lai lai')
    let ali := (union ali ali')
    let lei := (union lei lei')
    let proto : PaInG IdxCollType := .br nt nl ng nu nb ns nc nli
      .dead .dead api .dead .dead lai .dead .dead ali .dead .dead .dead lei
      .empty .dead .dead
    let vals := proto :: vals
    let sofar : mergeT IdxCollType := .proofs proofs proofs' (.sig3 sofar)
    let sofar : mergeT IdxCollType := .proofsOf proofsOf proofsOf' (.sig2 sofar)
    -- todo : optimize ↓
    let projs : CTrie ((ListProd IdxCollType (Nat × ((PaInG IdxCollType) × (PaInG IdxCollType))))) := projs.map (fun x => .some (x.mapTR (fun x (y,z) => (x,y,z,.dead))))
    let projs' : CTrie ((ListProd IdxCollType (Nat × ((PaInG IdxCollType) × (PaInG IdxCollType))))) := projs'.map (fun x => .some (x.mapTR (fun x (y,z) => (x,y,.dead,z))))
    let mproj := @CTrie.merge (ListProd IdxCollType (Nat × ((PaInG IdxCollType) × (PaInG IdxCollType)))) (fun l1 l2 =>
      help_3 union (fun x y => x.1 == y.1) (fun x y => (x.1,x.2.1,y.2.2)) l1 l2
      ) projs projs'
    let sofar : mergeT IdxCollType := mproj.fold sofar (fun bytA L sofar => L.foldl sofar (fun is (i,t1,t2) sofar => .projPre t1 t2 (.projPost bytA i is sofar)))
    let sofar := .sig1 sofar
    let sofar : mergeT IdxCollType := .lez lez lez' sofar
    let sofar : mergeT IdxCollType := .lea lea lea' sofar
    let sofar : mergeT IdxCollType := .lef lef lef' sofar
    let sofar : mergeT IdxCollType := .ala ala ala' sofar
    let sofar : mergeT IdxCollType := .alf alf alf' sofar
    let sofar : mergeT IdxCollType := .laa laa laa' sofar
    let sofar : mergeT IdxCollType := .laf laf laf' sofar
    let sofar : mergeT IdxCollType := .apa apa apa' sofar
    mergeDown union apf apf' sofar vals


@[specialize]
partial def mergeUp {IdxCollType : Type}
  (union : IdxCollType → IdxCollType → IdxCollType) (emptyCol : IdxCollType)
  (T : PaInG IdxCollType)
  (todo : mergeT IdxCollType) (vals : List (PaInG IdxCollType)) : PaInG IdxCollType :=
  match todo with
  | .nil => T
  | .done T nx => mergeUp union emptyCol T nx vals
  | .apa l r nx =>
      match vals with
      | [] => panic! "mergeUp"
      | .dead :: more =>
          let res := .br .nil .empty .nil .nil .nil .nil .empty .nil T .dead emptyCol .dead .dead emptyCol .dead .dead emptyCol .dead .dead .dead emptyCol .empty .dead .dead
          let (nx,vals) := mergeDown union l r nx (res :: more)
          mergeUp union emptyCol .dead nx vals
      | .br tnodes lnodes gnodes unodes bvars sorts consts lits _ apa api laf laa lai alf ala ali lef lea lez lei projs proofsOf proofs :: more =>
          let res := .br tnodes lnodes gnodes unodes bvars sorts consts lits T apa api laf laa lai alf ala ali lef lea lez lei projs proofsOf proofs
          let (nx,vals) := mergeDown union l r nx (res :: more)
          mergeUp union emptyCol .dead nx vals
  | .laf l r nx =>
      match vals with
      | [] => panic! "mergeUp"
      | .dead :: more =>
          let res := .br .nil .empty .nil .nil .nil .nil .empty .nil .dead T emptyCol .dead .dead emptyCol .dead .dead emptyCol .dead .dead .dead emptyCol .empty .dead .dead
          let (nx,vals) := mergeDown union l r nx (res :: more)
          mergeUp union emptyCol .dead nx vals
      | .br tnodes lnodes gnodes unodes bvars sorts consts lits apf _ api laf laa lai alf ala ali lef lea lez lei projs proofsOf proofs :: more =>
          let res := .br tnodes lnodes gnodes unodes bvars sorts consts lits apf T api laf laa lai alf ala ali lef lea lez lei projs proofsOf proofs
          let (nx,vals) := mergeDown union l r nx (res :: more)
          mergeUp union emptyCol .dead nx vals
  | .laa l r nx =>
      match vals with
      | [] => panic! "mergeUp"
      | .dead :: more =>
          let res := .br .nil .empty .nil .nil .nil .nil .empty .nil .dead .dead emptyCol T .dead emptyCol .dead .dead emptyCol .dead .dead .dead emptyCol .empty .dead .dead
          let (nx,vals) := mergeDown union l r nx (res :: more)
          mergeUp union emptyCol .dead nx vals
      | .br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api _ laa lai alf ala ali lef lea lez lei projs proofsOf proofs :: more =>
          let res := .br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api T laa lai alf ala ali lef lea lez lei projs proofsOf proofs
          let (nx,vals) := mergeDown union l r nx (res :: more)
          mergeUp union emptyCol .dead nx vals
  | .alf l r nx =>
      match vals with
      | [] => panic! "mergeUp"
      | .dead :: more =>
          let res := .br .nil .empty .nil .nil .nil .nil .empty .nil .dead .dead emptyCol .dead T emptyCol .dead .dead emptyCol .dead .dead .dead emptyCol .empty .dead .dead
          let (nx,vals) := mergeDown union l r nx (res :: more)
          mergeUp union emptyCol .dead nx vals
      | .br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf _ lai alf ala ali lef lea lez lei projs proofsOf proofs :: more =>
          let res := .br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf T lai alf ala ali lef lea lez lei projs proofsOf proofs
          let (nx,vals) := mergeDown union l r nx (res :: more)
          mergeUp union emptyCol .dead nx vals
  | .ala l r nx =>
      match vals with
      | [] => panic! "mergeUp"
      | .dead :: more =>
          let res := .br .nil .empty .nil .nil .nil .nil .empty .nil .dead .dead emptyCol .dead .dead emptyCol T .dead emptyCol .dead .dead .dead emptyCol .empty .dead .dead
          let (nx,vals) := mergeDown union l r nx (res :: more)
          mergeUp union emptyCol .dead nx vals
      | .br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai _ ala ali lef lea lez lei projs proofsOf proofs :: more =>
          let res := .br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai T ala ali lef lea lez lei projs proofsOf proofs
          let (nx,vals) := mergeDown union l r nx (res :: more)
          mergeUp union emptyCol .dead nx vals
  | .lef l r nx =>
      match vals with
      | [] => panic! "mergeUp"
      | .dead :: more =>
          let res := .br .nil .empty .nil .nil .nil .nil .empty .nil .dead .dead emptyCol .dead .dead emptyCol .dead T emptyCol .dead .dead .dead emptyCol .empty .dead .dead
          let (nx,vals) := mergeDown union l r nx (res :: more)
          mergeUp union emptyCol .dead nx vals
      | .br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai alf _ ali lef lea lez lei projs proofsOf proofs :: more =>
          let res := .br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai alf T ali lef lea lez lei projs proofsOf proofs
          let (nx,vals) := mergeDown union l r nx (res :: more)
          mergeUp union emptyCol .dead nx vals
  | .lea l r nx =>
      match vals with
      | [] => panic! "mergeUp"
      | .dead :: more =>
          let res := .br .nil .empty .nil .nil .nil .nil .empty .nil .dead .dead emptyCol .dead .dead emptyCol .dead .dead emptyCol T .dead .dead emptyCol .empty .dead .dead
          let (nx,vals) := mergeDown union l r nx (res :: more)
          mergeUp union emptyCol .dead nx vals
      | .br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai alf ala ali _ lea lez lei projs proofsOf proofs :: more =>
          let res := .br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai alf ala ali T lea lez lei projs proofsOf proofs
          let (nx,vals) := mergeDown union l r nx (res :: more)
          mergeUp union emptyCol .dead nx vals
  | .lez l r nx =>
      match vals with
      | [] => panic! "mergeUp"
      | .dead :: more =>
          let res := .br .nil .empty .nil .nil .nil .nil .empty .nil .dead .dead emptyCol .dead .dead emptyCol .dead .dead emptyCol .dead T .dead emptyCol .empty .dead .dead
          let (nx,vals) := mergeDown union l r nx (res :: more)
          mergeUp union emptyCol .dead nx vals
      | .br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai alf ala ali lef _ lez lei projs proofsOf proofs :: more =>
          let res := .br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai alf ala ali lef T lez lei projs proofsOf proofs
          let (nx,vals) := mergeDown union l r nx (res :: more)
          mergeUp union emptyCol .dead nx vals
  | .sig1 nx =>
      match vals with
      | [] => panic! "mergeUp"
      | .dead :: more =>
          let res := .br .nil .empty .nil .nil .nil .nil .empty .nil .dead .dead emptyCol .dead .dead emptyCol .dead .dead emptyCol .dead .dead T emptyCol .empty .dead .dead
          mergeUp union emptyCol .dead nx (res :: more)
      | .br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai alf ala ali lef lea _ lei projs proofsOf proofs :: more =>
          let res := .br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai alf ala ali lef lea T lei projs proofsOf proofs
          mergeUp union emptyCol .dead nx (res :: more)
  | .projPre l r nx =>
      let (nx,vals) := mergeDown union l r nx vals
      mergeUp union emptyCol .dead nx vals
  | .projPost name i is nx =>
      match vals with
      | [] => panic! "mergeUp"
      | .dead :: more =>
          let res := .br .nil .empty .nil .nil .nil .nil .empty .nil .dead .dead emptyCol .dead .dead emptyCol .dead .dead emptyCol .dead .dead .dead emptyCol (CTrie.empty.insert name (ListProd.cons is (i,T) .nil)) .dead .dead
          mergeUp union emptyCol .dead nx (res :: more)
      | .br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai alf ala ali lef lea lez lei projs proofsOf proofs :: more =>
          let projs := projs.upsert name (fun | .none => .some (ListProd.cons is (i,T) .nil) | .some e => .some (.cons is (i,T) e))
          let res := .br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai alf ala ali lef lea lez lei projs proofsOf proofs
          mergeUp union emptyCol .dead nx (res :: more)
  | .proofsOf l r nx =>
      let (nx,vals) := mergeDown union l r nx vals
      mergeUp union emptyCol .dead nx vals
  | .sig2 nx =>
      match vals with
      | [] => panic! "mergeUp"
      | .dead :: more =>
          let res := .br .nil .empty .nil .nil .nil .nil .empty .nil .dead .dead emptyCol .dead .dead emptyCol .dead .dead emptyCol .dead .dead .dead emptyCol .empty T .dead
          mergeUp union emptyCol .dead nx (res :: more)
      | .br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai alf ala ali lef lea lez lei projs _ proofs :: more =>
          let res := .br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai alf ala ali lef lea lez lei projs T proofs
          mergeUp union emptyCol .dead nx (res :: more)
  | .proofs l r nx =>
      let (nx,vals) := mergeDown union l r nx vals
      mergeUp union emptyCol .dead nx vals
  | .sig3 nx =>
      match vals with
      | [] => panic! "mergeUp"
      | .dead :: more =>
          let res := .br .nil .empty .nil .nil .nil .nil .empty .nil .dead .dead emptyCol .dead .dead emptyCol .dead .dead emptyCol .dead .dead .dead emptyCol .empty .dead T
          mergeUp union emptyCol res nx more
      | .br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai alf ala ali lef lea lez lei projs proofsOf _ :: more =>
          let res := .br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai alf ala ali lef lea lez lei projs proofsOf T
          mergeUp union emptyCol res nx more


/-- expects args to have disjoint index sets-/
@[specialize, inline]
partial def merge
  (union : IdxCollType → IdxCollType → IdxCollType) (emptyCol : IdxCollType)
  (A B : PaInG IdxCollType) : PaInG IdxCollType :=
  let (nx,vals) := mergeDown union A B .nil []
  mergeUp union emptyCol .dead nx vals




-- # Max

@[specialize]
def max (T : PaInG IdxCollType)
  (intersect : IdxCollType → IdxCollType → IdxCollType)
  (empty? : IdxCollType → Bool) (size : IdxCollType → Nat)
  : OptionProd IdxCollType Nat :=
    let inds := buildIndices T 0 id intersect empty?
    match inds with
    | [] => .none
    | ini :: more =>
      let rec maxq (v : IdxCollType) (m : Nat) : List IdxCollType → OptionProd IdxCollType Nat
        | [] => .some v m
        | I :: Is => let s := size I ; if s > m then maxq I s Is else maxq v m Is
      maxq ini (size ini) more



-- # Clean

inductive cleanT (IdxCollType : Type _) where
| nil
| done (_ : PaInG IdxCollType) (nx : cleanT IdxCollType)
| sig1 (nx : cleanT IdxCollType) | sig2 (nx : cleanT IdxCollType) | sig3 (nx : cleanT IdxCollType)
| apa (_ : PaInG IdxCollType) (nx : cleanT IdxCollType)
| laf (_ : PaInG IdxCollType) (nx : cleanT IdxCollType) | laa (_ : PaInG IdxCollType) (nx : cleanT IdxCollType)
| alf (_ : PaInG IdxCollType) (nx : cleanT IdxCollType) | ala (_ : PaInG IdxCollType) (nx : cleanT IdxCollType)
| lef (_ : PaInG IdxCollType) (nx : cleanT IdxCollType) | lea (_ : PaInG IdxCollType) (nx : cleanT IdxCollType) | lez (_ : PaInG IdxCollType) (nx : cleanT IdxCollType)
| projPre (_ : PaInG IdxCollType) (nx : cleanT IdxCollType)
| projPost (name : ByteArray) (idx : Nat) (is : IdxCollType) (nx : cleanT IdxCollType)
| proofsOf (_ : PaInG IdxCollType) (nx : cleanT IdxCollType)
| proofs (_ : PaInG IdxCollType) (nx : cleanT IdxCollType)
deriving Inhabited

#check CTrie.clean
#check CTrie.map



@[specialize]
partial def cleanDown (empty? : IdxCollType → Bool)
  (A : PaInG IdxCollType)
  (sofar : cleanT IdxCollType) (vals : List (PaInG IdxCollType)) : (cleanT IdxCollType) × (List (PaInG IdxCollType)) :=
  match A with
  | .dead => (.done A sofar,vals)
  | .br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai alf ala ali lef lea lez lei projs proofsOf proofs =>
    let nt := tnodes.foldl .nil (fun is c R => if empty? is then R else .cons is c R)
    let nl := (lnodes.map (fun L =>
      let L := L.foldl ListProd.nil (fun is c R => if empty? is then R else .cons is c R)
      match L with
      | .nil => .none
      | _ => .some L
      )).clean
    let ng := gnodes.foldl .nil (fun is c R => if empty? is then R else .cons is c R)
    let nu := unodes.foldl .nil (fun is c R => if empty? is then R else .cons is c R)
    let nb := bvars.foldl .nil (fun is c R => if empty? is then R else .cons is c R)
    let ns := sorts.foldl .nil (fun is c R => if empty? is then R else .cons is c R)
    let nc := (consts.map (fun L =>
      let L := L.foldl ListProd.nil (fun is c R => if empty? is then R else .cons is c R)
      match L with
      | .nil => .none
      | _ => .some L
      )).clean
    let nli := lits.foldl .nil (fun is c R => if empty? is then R else .cons is c R)
    let proto : PaInG IdxCollType := .br nt nl ng nu nb ns nc nli
      .dead .dead api .dead .dead lai .dead .dead ali .dead .dead .dead lei
      .empty .dead .dead
    let vals := proto :: vals
    let sofar : cleanT IdxCollType := .proofs proofs (.sig3 sofar)
    let sofar : cleanT IdxCollType := .proofsOf proofsOf (.sig2 sofar)
    -- in ↓ no cleaning necessary, as name will be reinserted anyway
    let sofar : cleanT IdxCollType := projs.fold sofar (fun bytA L sofar => L.foldl sofar (fun is (i,t) sofar =>
      if empty? is
      then sofar
      else .projPre t (.projPost bytA i is sofar)))
    let sofar := .sig1 sofar
    let sofar : cleanT IdxCollType := .lez lez sofar
    let sofar : cleanT IdxCollType := .lea lea sofar
    let sofar : cleanT IdxCollType := .lef lef sofar
    let sofar : cleanT IdxCollType := .ala ala sofar
    let sofar : cleanT IdxCollType := .alf alf sofar
    let sofar : cleanT IdxCollType := .laa laa sofar
    let sofar : cleanT IdxCollType := .laf laf sofar
    let sofar : cleanT IdxCollType := .apa apa sofar
    cleanDown empty? apf sofar vals


@[specialize]
partial def cleanUp {IdxCollType : Type}
  (emptyCol : IdxCollType) (empty? : IdxCollType → Bool)
  (T : PaInG IdxCollType)
  (todo : cleanT IdxCollType) (vals : List (PaInG IdxCollType)) : PaInG IdxCollType :=
  match todo with
  | .nil => T
  | .done T nx => cleanUp emptyCol empty? T nx vals
  | .apa l nx =>
      match vals with
      | [] => panic! "cleanUp"
      | .dead :: more =>
          let res := .br .nil .empty .nil .nil .nil .nil .empty .nil T .dead emptyCol .dead .dead emptyCol .dead .dead emptyCol .dead .dead .dead emptyCol .empty .dead .dead
          let (nx,vals) := cleanDown empty? l nx (res :: more)
          cleanUp emptyCol empty? .dead nx vals
      | .br tnodes lnodes gnodes unodes bvars sorts consts lits _ apa api laf laa lai alf ala ali lef lea lez lei projs proofsOf proofs :: more =>
          let res := .br tnodes lnodes gnodes unodes bvars sorts consts lits T apa api laf laa lai alf ala ali lef lea lez lei projs proofsOf proofs
          let (nx,vals) := cleanDown empty? l nx (res :: more)
          cleanUp emptyCol empty? .dead nx vals
  | .laf l nx =>
      match vals with
      | [] => panic! "cleanUp"
      | .dead :: more =>
          let res := .br .nil .empty .nil .nil .nil .nil .empty .nil .dead T emptyCol .dead .dead emptyCol .dead .dead emptyCol .dead .dead .dead emptyCol .empty .dead .dead
          let (nx,vals) := cleanDown empty? l nx (res :: more)
          cleanUp emptyCol empty? .dead nx vals
      | .br tnodes lnodes gnodes unodes bvars sorts consts lits apf _ api laf laa lai alf ala ali lef lea lez lei projs proofsOf proofs :: more =>
          let res := .br tnodes lnodes gnodes unodes bvars sorts consts lits apf T api laf laa lai alf ala ali lef lea lez lei projs proofsOf proofs
          let (nx,vals) := cleanDown empty? l nx (res :: more)
          cleanUp emptyCol empty? .dead nx vals
  | .laa l nx =>
      match vals with
      | [] => panic! "cleanUp"
      | .dead :: more =>
          let res := .br .nil .empty .nil .nil .nil .nil .empty .nil .dead .dead emptyCol T .dead emptyCol .dead .dead emptyCol .dead .dead .dead emptyCol .empty .dead .dead
          let (nx,vals) := cleanDown empty? l nx (res :: more)
          cleanUp emptyCol empty? .dead nx vals
      | .br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api _ laa lai alf ala ali lef lea lez lei projs proofsOf proofs :: more =>
          let res := .br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api T laa lai alf ala ali lef lea lez lei projs proofsOf proofs
          let (nx,vals) := cleanDown empty? l nx (res :: more)
          cleanUp emptyCol empty? .dead nx vals
  | .alf l nx =>
      match vals with
      | [] => panic! "cleanUp"
      | .dead :: more =>
          let res := .br .nil .empty .nil .nil .nil .nil .empty .nil .dead .dead emptyCol .dead T emptyCol .dead .dead emptyCol .dead .dead .dead emptyCol .empty .dead .dead
          let (nx,vals) := cleanDown empty? l nx (res :: more)
          cleanUp emptyCol empty? .dead nx vals
      | .br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf _ lai alf ala ali lef lea lez lei projs proofsOf proofs :: more =>
          let res := .br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf T lai alf ala ali lef lea lez lei projs proofsOf proofs
          let (nx,vals) := cleanDown empty? l nx (res :: more)
          cleanUp emptyCol empty? .dead nx vals
  | .ala l nx =>
      match vals with
      | [] => panic! "cleanUp"
      | .dead :: more =>
          let res := .br .nil .empty .nil .nil .nil .nil .empty .nil .dead .dead emptyCol .dead .dead emptyCol T .dead emptyCol .dead .dead .dead emptyCol .empty .dead .dead
          let (nx,vals) := cleanDown empty? l nx (res :: more)
          cleanUp emptyCol empty? .dead nx vals
      | .br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai _ ala ali lef lea lez lei projs proofsOf proofs :: more =>
          let res := .br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai T ala ali lef lea lez lei projs proofsOf proofs
          let (nx,vals) := cleanDown empty? l nx (res :: more)
          cleanUp emptyCol empty? .dead nx vals
  | .lef l nx =>
      match vals with
      | [] => panic! "cleanUp"
      | .dead :: more =>
          let res := .br .nil .empty .nil .nil .nil .nil .empty .nil .dead .dead emptyCol .dead .dead emptyCol .dead T emptyCol .dead .dead .dead emptyCol .empty .dead .dead
          let (nx,vals) := cleanDown empty? l nx (res :: more)
          cleanUp emptyCol empty? .dead nx vals
      | .br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai alf _ ali lef lea lez lei projs proofsOf proofs :: more =>
          let res := .br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai alf T ali lef lea lez lei projs proofsOf proofs
          let (nx,vals) := cleanDown empty? l nx (res :: more)
          cleanUp emptyCol empty? .dead nx vals
  | .lea l nx =>
      match vals with
      | [] => panic! "cleanUp"
      | .dead :: more =>
          let res := .br .nil .empty .nil .nil .nil .nil .empty .nil .dead .dead emptyCol .dead .dead emptyCol .dead .dead emptyCol T .dead .dead emptyCol .empty .dead .dead
          let (nx,vals) := cleanDown empty? l nx (res :: more)
          cleanUp emptyCol empty? .dead nx vals
      | .br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai alf ala ali _ lea lez lei projs proofsOf proofs :: more =>
          let res := .br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai alf ala ali T lea lez lei projs proofsOf proofs
          let (nx,vals) := cleanDown empty? l nx (res :: more)
          cleanUp emptyCol empty? .dead nx vals
  | .lez l nx =>
      match vals with
      | [] => panic! "cleanUp"
      | .dead :: more =>
          let res := .br .nil .empty .nil .nil .nil .nil .empty .nil .dead .dead emptyCol .dead .dead emptyCol .dead .dead emptyCol .dead T .dead emptyCol .empty .dead .dead
          let (nx,vals) := cleanDown empty? l nx (res :: more)
          cleanUp emptyCol empty? .dead nx vals
      | .br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai alf ala ali lef _ lez lei projs proofsOf proofs :: more =>
          let res := .br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai alf ala ali lef T lez lei projs proofsOf proofs
          let (nx,vals) := cleanDown empty? l nx (res :: more)
          cleanUp emptyCol empty? .dead nx vals
  | .sig1 nx =>
      match vals with
      | [] => panic! "cleanUp"
      | .dead :: more =>
          let res := .br .nil .empty .nil .nil .nil .nil .empty .nil .dead .dead emptyCol .dead .dead emptyCol .dead .dead emptyCol .dead .dead T emptyCol .empty .dead .dead
          cleanUp emptyCol empty? .dead nx (res :: more)
      | .br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai alf ala ali lef lea _ lei projs proofsOf proofs :: more =>
          let res := .br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai alf ala ali lef lea T lei projs proofsOf proofs
          cleanUp emptyCol empty? .dead nx (res :: more)
  | .projPre l nx =>
      let (nx,vals) := cleanDown empty? l nx vals
      cleanUp emptyCol empty? .dead nx vals
  | .projPost name i is nx =>
      match vals with
      | [] => panic! "cleanUp"
      | .dead :: more =>
          let res := .br .nil .empty .nil .nil .nil .nil .empty .nil .dead .dead emptyCol .dead .dead emptyCol .dead .dead emptyCol .dead .dead .dead emptyCol (CTrie.empty.insert name (ListProd.cons is (i,T) .nil)) .dead .dead
          cleanUp emptyCol empty? .dead nx (res :: more)
      | .br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai alf ala ali lef lea lez lei projs proofsOf proofs :: more =>
          let projs := projs.upsert name (fun | .none => .some (ListProd.cons is (i,T) .nil) | .some e => .some (.cons is (i,T) e))
          let res := .br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai alf ala ali lef lea lez lei projs proofsOf proofs
          cleanUp emptyCol empty? .dead nx (res :: more)
  | .proofsOf l nx =>
      let (nx,vals) := cleanDown empty? l nx vals
      cleanUp emptyCol empty? .dead nx vals
  | .sig2 nx =>
      match vals with
      | [] => panic! "cleanUp"
      | .dead :: more =>
          let res := .br .nil .empty .nil .nil .nil .nil .empty .nil .dead .dead emptyCol .dead .dead emptyCol .dead .dead emptyCol .dead .dead .dead emptyCol .empty T .dead
          cleanUp emptyCol empty? .dead nx (res :: more)
      | .br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai alf ala ali lef lea lez lei projs _ proofs :: more =>
          let res := .br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai alf ala ali lef lea lez lei projs T proofs
          cleanUp emptyCol empty? .dead nx (res :: more)
  | .proofs l nx =>
      let (nx,vals) := cleanDown empty? l nx vals
      cleanUp emptyCol empty? .dead nx vals
  | .sig3 nx =>
      match vals with
      | [] => panic! "cleanUp"
      | .dead :: more =>
          match T with
          | .dead =>
              cleanUp emptyCol empty? .dead nx more
          | _ =>
              let res := .br .nil .empty .nil .nil .nil .nil .empty .nil .dead .dead emptyCol .dead .dead emptyCol .dead .dead emptyCol .dead .dead .dead emptyCol .empty .dead T
              cleanUp emptyCol empty? res nx more
      | .br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai alf ala ali lef lea lez lei projs proofsOf _ :: more =>
          if tnodes.isEmpty && (match lnodes with | .leaf => true | _ => false) && gnodes.isEmpty && unodes.isEmpty && bvars.isEmpty && sorts.isEmpty &&
          (match consts with | .leaf => true | _ => false) && lits.isEmpty && (empty? api) && (empty? lai) && (empty? ali) && (empty? lei) &&
          (match projs with | .leaf => true | _ => false) && (match proofsOf with | .dead => true | _ => false)
      then
        cleanUp emptyCol empty? .dead nx more
      else
        let res := .br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai alf ala ali lef lea lez lei projs proofsOf T
        cleanUp emptyCol empty? res nx more


/-- expects args to have disjoint index sets-/
@[specialize, inline]
partial def clean
  (emptyCol : IdxCollType) (empty? : IdxCollType → Bool)
  (A : PaInG IdxCollType) : PaInG IdxCollType :=
  let (nx,vals) := cleanDown empty? A .nil []
  cleanUp emptyCol empty? .dead nx vals





-- # Delete

@[specialize, inline]
def deleteOfInds (T : PaInG IdxCollType) (inds : IdxCollType)
  (difference : IdxCollType → IdxCollType → IdxCollType)
  (emptyCol : IdxCollType) (empty? : IdxCollType → Bool)
  : PaInG IdxCollType :=
    let T := T.mapInds (difference · inds) emptyCol
    T.clean emptyCol empty?


-- # Keep

@[specialize, inline]
def keepOnlyOfInds (T : PaInG IdxCollType) (inds : IdxCollType)
  (difference union : IdxCollType → IdxCollType → IdxCollType)
  (emptyCol : IdxCollType) (empty? : IdxCollType → Bool)
  : PaInG IdxCollType :=
    let all := T.getIndices emptyCol union
    let toDel := difference all inds
    deleteOfInds T toDel difference emptyCol empty?

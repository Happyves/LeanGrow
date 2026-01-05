/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/


import LeanGrow.Src.Data.PathIndexG.API
import LeanGrow.Src.Utils.LeanGrow.Expr

open Lean Meta

variable {IdxCollType : Type _}

namespace PaInG

@[specialize]
def getIndices
  (empty : IdxCollType) (union : IdxCollType → IdxCollType → IdxCollType)
  (T : PaInG IdxCollType) : IdxCollType :=
  match T with
  | .dead => empty
  | .br tnodes lnodes gnodes unodes bvars sorts consts lits _ _ api _ _ lai _ _ ali _ _ _ lei projs proofsOf _ =>
      let is := tnodes.foldl empty (fun x _ is => union x is)
      let is := (lnodes.fold is (fun _ D is =>
                  (D.foldl is (fun x _ is => union x is))))
      let is := gnodes.foldl is (fun x _ is => union x is)
      let is := unodes.foldl is (fun x _ is => union x is)
      let is := bvars.foldl is (fun x _ is => union x is)
      let is := sorts.foldl is (fun x _ is => union x is)
      let is := (consts.fold is (fun _ D is =>
                  (D.foldl is (fun x _ is => union x is))))
      let is := lits.foldl is (fun x _ is => union x is)
      let is := union is api
      let is := union is lai
      let is := union is ali
      let is := union is lei
      let is := (projs.fold is (fun _ D is =>
                  (D.foldl is (fun x _ is => union x is))))
      let is := union is (proofsOf.getIndices empty union)
      is



def getIndicesS
  (T : PaInG UInt32Array) : UInt32Array :=
  getIndices .empty UInt32Array.union T



/-- In MetaM due to debt ; doesn't actually require any context-/
@[specialize]
partial def sharesIndicesWith
  (intersect : IdxCollType → IdxCollType → IdxCollType) (empty? : IdxCollType → Bool)
  (T : PaInG IdxCollType) (inds : IdxCollType) : MetaM Bool :=
  match T with
  | .dead => return false
  | .br tnodes lnodes gnodes unodes bvars sorts consts lits _ _ api _ _ lai _ _ ali _ _ _ lei projs proofsOf _ => do
      if !(empty? <| intersect api inds)
      then return true
      else
        if !(empty? <| intersect lai inds)
        then return true
        else
          if !(empty? <| intersect ali inds)
          then return true
          else
            if !(empty? <| intersect lei inds)
            then return true
            else
              tnodes.foldlMcps () (fun x _ s q =>
                if !(empty? <| intersect x inds)
                then return true
                else q s) <| fun _ =>
                  lnodes.foldMcps () (fun _ D s q =>
                    D.foldlMcps s (fun x _ s q =>
                        if !(empty? <| intersect x inds)
                        then return true
                        else q s) <| fun s => q s
                      ) <| fun _ =>
                        gnodes.foldlMcps () (fun x _ s q =>
                          if !(empty? <| intersect x inds)
                          then return true
                          else q s) <| fun _ =>
                            unodes.foldlMcps () (fun x _ s q =>
                              if !(empty? <| intersect x inds)
                              then return true
                              else q s) <| fun _ =>
                                bvars.foldlMcps () (fun x _ s q =>
                                  if !(empty? <| intersect x inds)
                                  then return true
                                  else q s) <| fun _ =>
                                    sorts.foldlMcps () (fun x _ s q =>
                                      if !(empty? <| intersect x inds)
                                      then return true
                                      else q s) <| fun _ =>
                                        consts.foldMcps () (fun _ D s q =>
                                          D.foldlMcps s (fun x _ s q =>
                                              if !(empty? <| intersect x inds)
                                              then return true
                                              else q s) <| fun s => q s
                                            ) <| fun _ =>
                                              lits.foldlMcps () (fun x _ s q =>
                                                if !(empty? <| intersect x inds)
                                                then return true
                                                else q s) <| fun _ =>
                                                  projs.foldMcps () (fun _ D s q =>
                                                    D.foldlMcps s (fun x _ s q =>
                                                        if !(empty? <| intersect x inds)
                                                        then return true
                                                        else q s) <| fun s => q s
                                                      ) <| fun _ =>
                                                        sharesIndicesWith intersect empty? proofsOf inds




inductive mapT (IdxCollType : Type _) where
| nil
| done (nx : mapT IdxCollType)
| sig1 (nx : mapT IdxCollType) | sig2 (nx : mapT IdxCollType) | sig3 (nx : mapT IdxCollType)
| apa (_ : PaInG IdxCollType) (nx : mapT IdxCollType)
| laf (_ : PaInG IdxCollType) (nx : mapT IdxCollType) | laa (_ : PaInG IdxCollType) (nx : mapT IdxCollType)
| alf (_ : PaInG IdxCollType) (nx : mapT IdxCollType) | ala (_ : PaInG IdxCollType) (nx : mapT IdxCollType)
| lef (_ : PaInG IdxCollType) (nx : mapT IdxCollType) | lea (_ : PaInG IdxCollType) (nx : mapT IdxCollType) | lez (_ : PaInG IdxCollType) (nx : mapT IdxCollType)
| projPre (_ : PaInG IdxCollType) (nx : mapT IdxCollType)
| projPost (name : ByteArray) (idx : Nat) (is : IdxCollType) (nx : mapT IdxCollType)
| proofsOf (_ : PaInG IdxCollType) (nx : mapT IdxCollType)
| proofs (_ : PaInG IdxCollType) (nx : mapT IdxCollType)
deriving Inhabited

#check CTrie.clean


@[specialize]
partial def mapIndsDown {IdxCollType IdxCollType' : Type}
  (trafo : IdxCollType → IdxCollType')
  (A : PaInG IdxCollType)
  (sofar : mapT IdxCollType) (vals : List (PaInG IdxCollType')) : (mapT IdxCollType) × (List (PaInG IdxCollType')) :=
  match A with
  | .dead => (.done sofar,vals)
  | .br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai alf ala ali lef lea lez lei projs proofsOf proofs =>
    let tnodes := tnodes.mapTR (fun is d => (trafo is, d))
    let lnodes := lnodes.map (fun D => .some <| D.map (fun is d => (trafo is, d)))
    let gnodes := gnodes.mapTR (fun is d => (trafo is, d))
    let unodes := unodes.mapTR (fun is d => (trafo is, d))
    let bvars := bvars.mapTR (fun is d => (trafo is, d))
    let sorts := sorts.mapTR (fun is d => (trafo is, d))
    let consts := consts.map (fun D => .some <| D.map (fun is d => (trafo is, d)))
    let lits := lits.mapTR (fun is d => (trafo is, d))
    let api := trafo api
    let lai := trafo lai
    let ali := trafo ali
    let lei := trafo lei
    let proto : PaInG IdxCollType' := .br tnodes lnodes gnodes unodes bvars sorts consts lits
      .dead .dead api .dead .dead lai .dead .dead ali .dead .dead .dead lei
      .empty .dead .dead
    let vals := proto :: vals
    let sofar : mapT IdxCollType := .proofs proofs (.sig3 sofar)
    let sofar : mapT IdxCollType := .proofsOf proofsOf (.sig2 sofar)
    let sofar : mapT IdxCollType := projs.fold sofar (fun bytA L sofar => L.foldl sofar (fun is (i,t) sofar => .projPre t (.projPost bytA i is sofar)))
    let sofar := .sig1 sofar
    let sofar : mapT IdxCollType := .lez lez sofar
    let sofar : mapT IdxCollType := .lea lea sofar
    let sofar : mapT IdxCollType := .lef lef sofar
    let sofar : mapT IdxCollType := .ala ala sofar
    let sofar : mapT IdxCollType := .alf alf sofar
    let sofar : mapT IdxCollType := .laa laa sofar
    let sofar : mapT IdxCollType := .laf laf sofar
    let sofar : mapT IdxCollType := .apa apa sofar
    mapIndsDown trafo apf sofar vals


@[specialize]
partial def mapIndsUp {IdxCollType IdxCollType' : Type}
  (trafo : IdxCollType → IdxCollType')
  (emptyCol : IdxCollType')
  (T : PaInG IdxCollType')
  (todo : mapT IdxCollType) (vals : List (PaInG IdxCollType')) : PaInG IdxCollType' :=
  match todo with
  | .nil => T
  | .done nx => mapIndsUp trafo emptyCol  .dead nx vals
  | .apa l nx =>
      match vals with
      | [] => panic! "mapIndsUp"
      | .dead :: more =>
          let res := .br .nil .empty .nil .nil .nil .nil .empty .nil T .dead emptyCol .dead .dead emptyCol .dead .dead emptyCol .dead .dead .dead emptyCol .empty .dead .dead
          let (nx,vals) := mapIndsDown trafo l nx (res :: more)
          mapIndsUp trafo emptyCol  .dead nx vals
      | .br tnodes lnodes gnodes unodes bvars sorts consts lits _ apa api laf laa lai alf ala ali lef lea lez lei projs proofsOf proofs :: more =>
          let res := .br tnodes lnodes gnodes unodes bvars sorts consts lits T apa api laf laa lai alf ala ali lef lea lez lei projs proofsOf proofs
          let (nx,vals) := mapIndsDown trafo l nx (res :: more)
          mapIndsUp trafo emptyCol  .dead nx vals
  | .laf l nx =>
      match vals with
      | [] => panic! "mapIndsUp"
      | .dead :: more =>
          let res := .br .nil .empty .nil .nil .nil .nil .empty .nil .dead T emptyCol .dead .dead emptyCol .dead .dead emptyCol .dead .dead .dead emptyCol .empty .dead .dead
          let (nx,vals) := mapIndsDown trafo l nx (res :: more)
          mapIndsUp trafo emptyCol  .dead nx vals
      | .br tnodes lnodes gnodes unodes bvars sorts consts lits apf _ api laf laa lai alf ala ali lef lea lez lei projs proofsOf proofs :: more =>
          let res := .br tnodes lnodes gnodes unodes bvars sorts consts lits apf T api laf laa lai alf ala ali lef lea lez lei projs proofsOf proofs
          let (nx,vals) := mapIndsDown trafo l nx (res :: more)
          mapIndsUp trafo emptyCol  .dead nx vals
  | .laa l nx =>
      match vals with
      | [] => panic! "mapIndsUp"
      | .dead :: more =>
          let res := .br .nil .empty .nil .nil .nil .nil .empty .nil .dead .dead emptyCol T .dead emptyCol .dead .dead emptyCol .dead .dead .dead emptyCol .empty .dead .dead
          let (nx,vals) := mapIndsDown trafo l nx (res :: more)
          mapIndsUp trafo emptyCol  .dead nx vals
      | .br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api _ laa lai alf ala ali lef lea lez lei projs proofsOf proofs :: more =>
          let res := .br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api T laa lai alf ala ali lef lea lez lei projs proofsOf proofs
          let (nx,vals) := mapIndsDown trafo l nx (res :: more)
          mapIndsUp trafo emptyCol  .dead nx vals
  | .alf l nx =>
      match vals with
      | [] => panic! "mapIndsUp"
      | .dead :: more =>
          let res := .br .nil .empty .nil .nil .nil .nil .empty .nil .dead .dead emptyCol .dead T emptyCol .dead .dead emptyCol .dead .dead .dead emptyCol .empty .dead .dead
          let (nx,vals) := mapIndsDown trafo l nx (res :: more)
          mapIndsUp trafo emptyCol  .dead nx vals
      | .br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf _ lai alf ala ali lef lea lez lei projs proofsOf proofs :: more =>
          let res := .br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf T lai alf ala ali lef lea lez lei projs proofsOf proofs
          let (nx,vals) := mapIndsDown trafo l nx (res :: more)
          mapIndsUp trafo emptyCol  .dead nx vals
  | .ala l nx =>
      match vals with
      | [] => panic! "mapIndsUp"
      | .dead :: more =>
          let res := .br .nil .empty .nil .nil .nil .nil .empty .nil .dead .dead emptyCol .dead .dead emptyCol T .dead emptyCol .dead .dead .dead emptyCol .empty .dead .dead
          let (nx,vals) := mapIndsDown trafo l nx (res :: more)
          mapIndsUp trafo emptyCol  .dead nx vals
      | .br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai _ ala ali lef lea lez lei projs proofsOf proofs :: more =>
          let res := .br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai T ala ali lef lea lez lei projs proofsOf proofs
          let (nx,vals) := mapIndsDown trafo l nx (res :: more)
          mapIndsUp trafo emptyCol  .dead nx vals
  | .lef l nx =>
      match vals with
      | [] => panic! "mapIndsUp"
      | .dead :: more =>
          let res := .br .nil .empty .nil .nil .nil .nil .empty .nil .dead .dead emptyCol .dead .dead emptyCol .dead T emptyCol .dead .dead .dead emptyCol .empty .dead .dead
          let (nx,vals) := mapIndsDown trafo l nx (res :: more)
          mapIndsUp trafo emptyCol  .dead nx vals
      | .br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai alf _ ali lef lea lez lei projs proofsOf proofs :: more =>
          let res := .br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai alf T ali lef lea lez lei projs proofsOf proofs
          let (nx,vals) := mapIndsDown trafo l nx (res :: more)
          mapIndsUp trafo emptyCol  .dead nx vals
  | .lea l nx =>
      match vals with
      | [] => panic! "mapIndsUp"
      | .dead :: more =>
          let res := .br .nil .empty .nil .nil .nil .nil .empty .nil .dead .dead emptyCol .dead .dead emptyCol .dead .dead emptyCol T .dead .dead emptyCol .empty .dead .dead
          let (nx,vals) := mapIndsDown trafo l nx (res :: more)
          mapIndsUp trafo emptyCol  .dead nx vals
      | .br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai alf ala ali _ lea lez lei projs proofsOf proofs :: more =>
          let res := .br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai alf ala ali T lea lez lei projs proofsOf proofs
          let (nx,vals) := mapIndsDown trafo l nx (res :: more)
          mapIndsUp trafo emptyCol  .dead nx vals
  | .lez l nx =>
      match vals with
      | [] => panic! "mapIndsUp"
      | .dead :: more =>
          let res := .br .nil .empty .nil .nil .nil .nil .empty .nil .dead .dead emptyCol .dead .dead emptyCol .dead .dead emptyCol .dead T .dead emptyCol .empty .dead .dead
          let (nx,vals) := mapIndsDown trafo l nx (res :: more)
          mapIndsUp trafo emptyCol  .dead nx vals
      | .br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai alf ala ali lef _ lez lei projs proofsOf proofs :: more =>
          let res := .br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai alf ala ali lef T lez lei projs proofsOf proofs
          let (nx,vals) := mapIndsDown trafo l nx (res :: more)
          mapIndsUp trafo emptyCol  .dead nx vals
  | .sig1 nx =>
      match vals with
      | [] => panic! "mapIndsUp"
      | .dead :: more =>
          let res := .br .nil .empty .nil .nil .nil .nil .empty .nil .dead .dead emptyCol .dead .dead emptyCol .dead .dead emptyCol .dead .dead T emptyCol .empty .dead .dead
          mapIndsUp trafo emptyCol  .dead nx (res :: more)
      | .br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai alf ala ali lef lea _ lei projs proofsOf proofs :: more =>
          let res := .br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai alf ala ali lef lea T lei projs proofsOf proofs
          mapIndsUp trafo emptyCol  .dead nx (res :: more)
  | .projPre l nx =>
      let (nx,vals) := mapIndsDown trafo l nx vals
      mapIndsUp trafo emptyCol  .dead nx vals
  | .projPost name i is nx =>
      let is := trafo is
      match vals with
      | [] => panic! "mapIndsUp"
      | .dead :: more =>
          let res := .br .nil .empty .nil .nil .nil .nil .empty .nil .dead .dead emptyCol .dead .dead emptyCol .dead .dead emptyCol .dead .dead .dead emptyCol (CTrie.empty.insert name (ListProd.cons is (i,T) .nil)) .dead .dead
          mapIndsUp trafo emptyCol  .dead nx (res :: more)
      | .br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai alf ala ali lef lea lez lei projs proofsOf proofs :: more =>
          let projs := projs.upsert name (fun | .none => .some (ListProd.cons is (i,T) .nil) | .some e => .some (.cons is (i,T) e))
          let res := .br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai alf ala ali lef lea lez lei projs proofsOf proofs
          mapIndsUp trafo emptyCol  .dead nx (res :: more)
  | .proofsOf l nx =>
      let (nx,vals) := mapIndsDown trafo l nx vals
      mapIndsUp trafo emptyCol  .dead nx vals
  | .sig2 nx =>
      match vals with
      | [] => panic! "mapIndsUp"
      | .dead :: more =>
          let res := .br .nil .empty .nil .nil .nil .nil .empty .nil .dead .dead emptyCol .dead .dead emptyCol .dead .dead emptyCol .dead .dead .dead emptyCol .empty T .dead
          mapIndsUp trafo emptyCol  .dead nx (res :: more)
      | .br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai alf ala ali lef lea lez lei projs _ proofs :: more =>
          let res := .br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai alf ala ali lef lea lez lei projs T proofs
          mapIndsUp trafo emptyCol  .dead nx (res :: more)
  | .proofs l nx =>
      let (nx,vals) := mapIndsDown trafo l nx vals
      mapIndsUp trafo emptyCol  .dead nx vals
  | .sig3 nx =>
      match vals with
      | [] => panic! "mapIndsUp"
      | .dead :: more =>
          let res := .br .nil .empty .nil .nil .nil .nil .empty .nil .dead .dead emptyCol .dead .dead emptyCol .dead .dead emptyCol .dead .dead .dead emptyCol .empty .dead T
          mapIndsUp trafo emptyCol  res nx more
      | .br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai alf ala ali lef lea lez lei projs proofsOf _ :: more =>
          let res := .br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai alf ala ali lef lea lez lei projs proofsOf T
          mapIndsUp trafo emptyCol  res nx more


/-- expects args to have disjoint index sets-/
@[specialize, inline]
partial def mapInds {IdxCollType IdxCollType' : Type}
  (trafo : IdxCollType → IdxCollType')
  (emptyCol : IdxCollType')
  (A : PaInG IdxCollType) : PaInG IdxCollType' :=
  let (nx,vals) := mapIndsDown trafo A .nil []
  mapIndsUp trafo emptyCol  .dead nx vals

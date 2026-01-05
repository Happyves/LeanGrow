
/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/


import LeanGrow.Src.Data.PathIndexG.Build

open Lean Meta

variable {IdxCollType : Type _}

namespace PaInG


inductive insertCoreType (IdxCollType : Type _) where
| nil
| proof (fst : Bool) (depth : Nat) (e: Expr) (T : PaInG IdxCollType) (_ : insertCoreType IdxCollType)
| app (fst : Bool) (depth : Nat) (a : Expr) (T : PaInG IdxCollType) (_ : insertCoreType IdxCollType)
| lam (fst : Bool) (depth : Nat) (f a : Expr) (T : PaInG IdxCollType) (_ : insertCoreType IdxCollType)
| all (fst : Bool) (depth : Nat) (f a : Expr) (T : PaInG IdxCollType) (_ : insertCoreType IdxCollType)
| letE (turn : UInt8) (depth : Nat) (f a z : Expr) (T : PaInG IdxCollType) (_ : insertCoreType IdxCollType)
| proj (name : ByteArray) (idx : Nat) (T : PaInG IdxCollType) (_ : insertCoreType IdxCollType)
| atom (depth : Nat) (e : Expr) (T : PaInG IdxCollType) (_ : insertCoreType IdxCollType)
deriving Inhabited


@[specialize]
partial def insertCoreDown
  (l1 : LocalContext) (l2 : LocalInstances)
  (skipP : Bool) (depth : Nat) (ce : Expr) (T : PaInG IdxCollType)
  (sofar : insertCoreType IdxCollType) : MetaM (insertCoreType IdxCollType) := do
  match T with
  | .br _ _ _ _ _ _ _ _ apf _ _ laf _ _ alf _ _ lef _ _ _ projs proofsOf _ =>
      if (← if !skipP then (IsProof ce l1 l2) else return false)
      then
        let ceT := (← InferType ce l1 l2)
        insertCoreDown l1 l2 false depth ceT proofsOf (.proof true depth ce T sofar)
      else
        match ce with
        | .mdata _ e => insertCoreDown l1 l2 skipP depth e T sofar
        | .app f a => insertCoreDown l1 l2 false depth f apf (.app true depth a T sofar)
        | .lam _ f a _ => insertCoreDown l1 l2 false depth f laf <| .lam true depth f a T sofar
        | .forallE _ f a _ => insertCoreDown l1 l2 false depth f alf <| .all true depth f a T sofar
        | .letE _ f a z _ => insertCoreDown l1 l2 false depth f lef <| .letE 0 depth f a z T sofar
        | .proj n i e =>
            let n := n.toString.toUTF8
            match projs.find? n with
            | .none =>
                insertCoreDown l1 l2 false depth e .dead <| .proj n i T sofar
            | .some ps =>
                match ps.find? (fun _ (j,_) => i == j) with
                | .none =>
                    insertCoreDown l1 l2 false depth e .dead <| .proj n i T sofar
                | .some _ (_,nT) =>
                    insertCoreDown l1 l2 false depth e nT <| .proj n i T sofar
        | _ => return .atom depth ce T sofar
  | _ =>
      if (← if !skipP then (IsProof ce l1 l2) else return false)
      then
        let ceT := (← InferType ce l1 l2)
        insertCoreDown l1 l2 false depth ceT .dead (.proof true depth ce T sofar)
      else
        match ce with
        | .mdata _ e => insertCoreDown l1 l2 skipP depth e T sofar
        | .app f a => insertCoreDown l1 l2 false depth f .dead (.app true depth a T sofar)
        | .lam _ f a _ => insertCoreDown l1 l2 false depth f .dead <| .lam true depth f a T sofar
        | .forallE _ f a _ => insertCoreDown l1 l2 false depth f .dead <| .all true depth f a T sofar
        | .letE _ f a z _ => insertCoreDown l1 l2 false depth f .dead <| .letE 0 depth f a z T sofar
        | .proj n i e =>
            let n := n.toString.toUTF8
            insertCoreDown l1 l2 false depth e .dead <| .proj n i T sofar
        | _ => return .atom depth ce T sofar


@[specialize]
partial def insertCoreUp
  (singleton : Nat → IdxCollType) (insert : Nat → IdxCollType → IdxCollType) (emptyCol : IdxCollType)
  (l1 : LocalContext) (l2 : LocalInstances)
  (idx : Nat)
  (sofar : PaInG IdxCollType) (todo : insertCoreType IdxCollType)
  : MetaM (Prod3 (PaInG IdxCollType) LocalContext LocalInstances) := do
    match todo with
    | .nil => return ⟨sofar,l1,l2⟩
    | .proof fst depth e T nx =>
        if fst
        then
          match T with
          | .dead =>
              let res := PaInG.br .nil .empty .nil .nil .nil .nil .empty .nil .dead .dead emptyCol .dead .dead emptyCol .dead .dead emptyCol .dead .dead .dead emptyCol .empty sofar .dead
              let NX ← insertCoreDown l1 l2 true depth e .dead <| .proof false depth e res nx
              insertCoreUp singleton insert emptyCol l1 l2 idx .dead NX
          | .br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai alf ala ali lef lea lez lei projs _ proofs =>
              let res := PaInG.br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai alf ala ali lef lea lez lei projs sofar proofs
              let NX ← insertCoreDown l1 l2 true depth e proofs <| .proof false depth e res nx
              insertCoreUp singleton insert emptyCol l1 l2 idx .dead NX
        else
          match T with
          | .dead => -- shouldn't ?
              let res := PaInG.br .nil .empty .nil .nil .nil .nil .empty .nil .dead .dead emptyCol .dead .dead emptyCol .dead .dead emptyCol .dead .dead .dead emptyCol .empty .dead sofar
              insertCoreUp singleton insert emptyCol l1 l2 idx res nx
          | .br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai alf ala ali lef lea lez lei projs proofsOf _ =>
              let res := PaInG.br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai alf ala ali lef lea lez lei projs proofsOf sofar
              insertCoreUp singleton insert emptyCol l1 l2 idx res nx
    | .app fst depth a T nx =>
        if fst
        then
          match T with
          | .dead =>
              let res := PaInG.br .nil .empty .nil .nil .nil .nil .empty .nil sofar .dead emptyCol .dead .dead emptyCol .dead .dead emptyCol .dead .dead .dead emptyCol .empty .dead .dead
              let NX ← insertCoreDown l1 l2 false depth a .dead <| .app false depth a res nx
              insertCoreUp singleton insert emptyCol l1 l2 idx .dead NX
          | .br tnodes lnodes gnodes unodes bvars sorts consts lits _ apa api laf laa lai alf ala ali lef lea lez lei projs proofsOf proofs =>
              let res := PaInG.br tnodes lnodes gnodes unodes bvars sorts consts lits sofar apa api laf laa lai alf ala ali lef lea lez lei projs proofsOf proofs
              let NX ← insertCoreDown l1 l2 false depth a apa <| .app false depth a res nx
              insertCoreUp singleton insert emptyCol l1 l2 idx .dead NX
        else
          match T with
          | .dead => -- shouldn't ?
              let api := singleton idx
              let res := PaInG.br .nil .empty .nil .nil .nil .nil .empty .nil .dead sofar api .dead .dead emptyCol .dead .dead emptyCol .dead .dead .dead emptyCol .empty .dead .dead
              insertCoreUp singleton insert emptyCol l1 l2 idx res nx
          | .br tnodes lnodes gnodes unodes bvars sorts consts lits apf _ api laf laa lai alf ala ali lef lea lez lei projs proofsOf proofs =>
              let api := insert idx api
              let res := PaInG.br tnodes lnodes gnodes unodes bvars sorts consts lits apf sofar api laf laa lai alf ala ali lef lea lez lei projs proofsOf proofs
              insertCoreUp singleton insert emptyCol l1 l2 idx res nx
    | .lam fst depth f a T nx =>
        if fst
        then
          match T with
          | .dead =>
              let res := PaInG.br .nil .empty .nil .nil .nil .nil .empty .nil .dead .dead emptyCol sofar .dead emptyCol .dead .dead emptyCol .dead .dead .dead emptyCol .empty .dead .dead
              let w ← worker depth
              let ⟨_,a,l1,l2⟩ ← withFreeing w f a l1 l2
              let NX ← insertCoreDown l1 l2 false (depth +1) a .dead <| .lam false (depth +1) f a res nx
              insertCoreUp singleton insert emptyCol l1 l2 idx .dead NX
          | .br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api _ laa lai alf ala ali lef lea lez lei projs proofsOf proofs =>
              let res := PaInG.br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api sofar laa lai alf ala ali lef lea lez lei projs proofsOf proofs
              let w ← worker depth
              let ⟨_,a,l1,l2⟩ ← withFreeing w f a l1 l2
              let NX ← insertCoreDown l1 l2 false (depth +1) a laa <| .lam false (depth +1) f a res nx
              insertCoreUp singleton insert emptyCol l1 l2 idx .dead NX
        else
          match T with
          | .dead => -- shouldn't ?
              let lai := singleton idx
              let res := PaInG.br .nil .empty .nil .nil .nil .nil .empty .nil .dead .dead emptyCol .dead sofar lai .dead .dead emptyCol .dead .dead .dead emptyCol .empty .dead .dead
              insertCoreUp singleton insert emptyCol l1 l2 idx res nx
          | .br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf _ lai alf ala ali lef lea lez lei projs proofsOf proofs =>
              let lai := insert idx lai
              let res := PaInG.br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf sofar lai alf ala ali lef lea lez lei projs proofsOf proofs
              insertCoreUp singleton insert emptyCol l1 l2 idx res nx
    | .all fst depth f a T nx =>
        if fst
        then
          match T with
          | .dead =>
              let res := PaInG.br .nil .empty .nil .nil .nil .nil .empty .nil .dead .dead emptyCol .dead .dead emptyCol sofar .dead emptyCol .dead .dead .dead emptyCol .empty .dead .dead
              let w ← worker depth
              let ⟨_,a,l1,l2⟩ ← withFreeing w f a l1 l2
              let NX ← insertCoreDown l1 l2 false (depth +1) a .dead <| .all false (depth +1) f a res nx
              insertCoreUp singleton insert emptyCol l1 l2 idx .dead NX
          | .br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai _ ala ali lef lea lez lei projs proofsOf proofs =>
              let res := PaInG.br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai sofar ala ali lef lea lez lei projs proofsOf proofs
              let w ← worker depth
              let ⟨_,a,l1,l2⟩ ← withFreeing w f a l1 l2
              let NX ← insertCoreDown l1 l2 false (depth +1) a ala <| .all false (depth +1) f a res nx
              insertCoreUp singleton insert emptyCol l1 l2 idx .dead NX
        else
          match T with
          | .dead => -- shouldn't ?
              let ali := singleton idx
              let res := PaInG.br .nil .empty .nil .nil .nil .nil .empty .nil .dead .dead emptyCol .dead .dead emptyCol .dead sofar ali .dead .dead .dead emptyCol .empty .dead .dead
              insertCoreUp singleton insert emptyCol l1 l2 idx res nx
          | .br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai alf _ ali lef lea lez lei projs proofsOf proofs =>
              let ali := insert idx ali
              let res := PaInG.br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai alf sofar ali lef lea lez lei projs proofsOf proofs
              insertCoreUp singleton insert emptyCol l1 l2 idx res nx
    | .letE fst depth f a z T nx =>
        if fst == 0
        then
          match T with
          | .dead =>
              let res := PaInG.br .nil .empty .nil .nil .nil .nil .empty .nil .dead .dead emptyCol .dead .dead emptyCol .dead .dead emptyCol sofar .dead .dead emptyCol .empty .dead .dead
              let NX ← insertCoreDown l1 l2 false depth a .dead <| .letE 1 depth f a z res nx
              insertCoreUp singleton insert emptyCol l1 l2 idx .dead NX
          | .br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai alf ala ali _ lea lez lei projs proofsOf proofs =>
              let res := PaInG.br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai alf ala ali sofar lea lez lei projs proofsOf proofs
              let NX ← insertCoreDown l1 l2 false depth a lea <| .letE 1 depth f a z res nx
              insertCoreUp singleton insert emptyCol l1 l2 idx .dead NX
        else if fst == 1
        then
          match T with
          | .dead =>
              let res := PaInG.br .nil .empty .nil .nil .nil .nil .empty .nil .dead .dead emptyCol .dead .dead emptyCol .dead .dead emptyCol .dead sofar .dead emptyCol .empty .dead .dead
              let w ← worker depth
              let ⟨_,z,l1,l2⟩ ← withFreeingLet w f a z l1 l2
              let NX ← insertCoreDown l1 l2 false (depth+1) z .dead <| .letE 2 (depth+1) f a z res nx
              insertCoreUp singleton insert emptyCol l1 l2 idx .dead NX
          | .br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai alf ala ali lef _ lez lei projs proofsOf proofs =>
              let res := PaInG.br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai alf ala ali lef sofar lez lei projs proofsOf proofs
              let w ← worker depth
              let ⟨_,z,l1,l2⟩ ← withFreeingLet w f a z l1 l2
              let NX ← insertCoreDown l1 l2 false (depth+1) z lez <| .letE 2 (depth+1) f a z res nx
              insertCoreUp singleton insert emptyCol l1 l2 idx .dead NX
        else
          match T with
          | .dead => -- shouldn't ?
              let lei := singleton idx
              let res := PaInG.br .nil .empty .nil .nil .nil .nil .empty .nil .dead .dead emptyCol .dead .dead emptyCol .dead .dead emptyCol .dead .dead sofar lei .empty .dead .dead
              insertCoreUp singleton insert emptyCol l1 l2 idx res nx
          | .br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai alf ala ali lef lea _ lei projs proofsOf proofs =>
              let lei := insert idx lei
              let res := PaInG.br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai alf ala ali lef lea sofar lei projs proofsOf proofs
              insertCoreUp singleton insert emptyCol l1 l2 idx res nx
    | .proj name pidx T nx =>
        match T with
        | .dead =>
            let is := singleton idx
            let projs := CTrie.empty.insert name (.cons is (pidx,sofar) .nil)
            let res := PaInG.br .nil .empty .nil .nil .nil .nil .empty .nil .dead .dead emptyCol .dead .dead emptyCol .dead .dead emptyCol .dead .dead .dead emptyCol projs .dead .dead
            insertCoreUp singleton insert emptyCol l1 l2 idx res nx
        | .br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai alf ala ali lef lea lez lei projs proofsOf proofs =>
            let projs := projs.upsert name ( fun
              | .none => .some <| .cons (singleton idx) (pidx,sofar) .nil
              | .some L => .some <| L.modifyAdd' (fun (i,_) => i == pidx) (fun en => {en with snd := sofar}) (insert idx) (pidx,sofar) (singleton idx))
            let res := PaInG.br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai alf ala ali lef lea lez lei projs proofsOf proofs
            insertCoreUp singleton insert emptyCol l1 l2 idx res nx
    | .atom depth e T nx =>
        match e with
        | .bvar i =>
            match T with
            | .dead =>
                let res := PaInG.br .nil .empty .nil .nil (.cons (singleton idx) i .nil) .nil .empty .nil .dead .dead emptyCol .dead .dead emptyCol .dead .dead emptyCol .dead .dead .dead emptyCol .empty .dead .dead
                insertCoreUp singleton insert emptyCol l1 l2 idx res nx
            | .br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai alf ala ali lef lea lez lei projs proofsOf proofs =>
                let bvars := bvars.insert_PaInG_nat singleton insert i idx
                let res := PaInG.br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai alf ala ali lef lea lez lei projs proofsOf proofs
                insertCoreUp singleton insert emptyCol l1 l2 idx res nx
        | .sort l =>
            match T with
            | .dead =>
                let res := PaInG.br .nil .empty .nil .nil .nil (.cons (singleton idx) l .nil) .empty .nil .dead .dead emptyCol .dead .dead emptyCol .dead .dead emptyCol .dead .dead .dead emptyCol .empty .dead .dead
                insertCoreUp singleton insert emptyCol l1 l2 idx res nx
            | .br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai alf ala ali lef lea lez lei projs proofsOf proofs =>
                let sorts := sorts.modifyAdd (fun x => insert idx x) l (singleton idx)
                let res := PaInG.br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai alf ala ali lef lea lez lei projs proofsOf proofs
                insertCoreUp singleton insert emptyCol l1 l2 idx res nx
        | .const n l =>
            match T with
            | .dead =>
                let consts := ListProd.insert_PaInG_const singleton insert .empty n l idx
                let res := PaInG.br .nil .empty .nil .nil .nil .nil consts .nil .dead .dead emptyCol .dead .dead emptyCol .dead .dead emptyCol .dead .dead .dead emptyCol .empty .dead .dead
                insertCoreUp singleton insert emptyCol l1 l2 idx res nx
            | .br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai alf ala ali lef lea lez lei projs proofsOf proofs =>
                let consts := ListProd.insert_PaInG_const singleton insert consts n l idx
                let res := PaInG.br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai alf ala ali lef lea lez lei projs proofsOf proofs
                insertCoreUp singleton insert emptyCol l1 l2 idx res nx
        | .lit l =>
            match T with
            | .dead =>
                let res := PaInG.br .nil .empty .nil .nil .nil .nil .empty (.cons (singleton idx) l .nil) .dead .dead emptyCol .dead .dead emptyCol .dead .dead emptyCol .dead .dead .dead emptyCol .empty .dead .dead
                insertCoreUp singleton insert emptyCol l1 l2 idx res nx
            | .br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai alf ala ali lef lea lez lei projs proofsOf proofs =>
                let lits := lits.modifyAdd (fun x => insert idx x) l (singleton idx)
                let res := PaInG.br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai alf ala ali lef lea lez lei projs proofsOf proofs
                insertCoreUp singleton insert emptyCol l1 l2 idx res nx
        | .mvar mid =>
            match mid.name with
            | .num (.num module thmIdx) pos =>
                match T with
                | .dead =>
                    let lnodes := ListProd.insert_PaInG_lnode singleton insert .empty module (thmIdx, pos) idx
                    let res := PaInG.br .nil lnodes .nil .nil .nil .nil .empty .nil .dead .dead emptyCol .dead .dead emptyCol .dead .dead emptyCol .dead .dead .dead emptyCol .empty .dead .dead
                    insertCoreUp singleton insert emptyCol l1 l2 idx res nx
                | .br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai alf ala ali lef lea lez lei projs proofsOf proofs =>
                    let lnodes := ListProd.insert_PaInG_lnode singleton insert lnodes module (thmIdx, pos) idx
                    let res := PaInG.br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai alf ala ali lef lea lez lei projs proofsOf proofs
                    insertCoreUp singleton insert emptyCol l1 l2 idx res nx
            | _ => throwError s!"[insertCore] mvar not in lnode format: {repr mid}"
        | .fvar fid =>
            match fid.name with
            | .num (.num _ backIdx) pos =>
                match T with
                | .dead =>
                    let tnodes := ListProd.nil.insert_PaInG_lex singleton insert (backIdx, pos) idx
                    let res := PaInG.br tnodes .empty .nil .nil .nil .nil .empty .nil .dead .dead emptyCol .dead .dead emptyCol .dead .dead emptyCol .dead .dead .dead emptyCol .empty .dead .dead
                    insertCoreUp singleton insert emptyCol l1 l2 idx res nx
                | .br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai alf ala ali lef lea lez lei projs proofsOf proofs =>
                    let tnodes := tnodes.insert_PaInG_lex singleton insert (backIdx, pos) idx
                    let res := PaInG.br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai alf ala ali lef lea lez lei projs proofsOf proofs
                    insertCoreUp singleton insert emptyCol l1 l2 idx res nx
            | .num (.str _ kind) fidx =>
                if kind == "w"
                then
                  match T with
                  | .dead =>
                      let bvars := ListProd.nil.insert_PaInG_nat singleton insert (depth - 1 - fidx) idx
                      let res := PaInG.br .nil .empty .nil .nil bvars .nil .empty .nil .dead .dead emptyCol .dead .dead emptyCol .dead .dead emptyCol .dead .dead .dead emptyCol .empty .dead .dead
                      insertCoreUp singleton insert emptyCol l1 l2 idx res nx
                  | .br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai alf ala ali lef lea lez lei projs proofsOf proofs =>
                      let bvars := bvars.insert_PaInG_nat singleton insert (depth - 1 - fidx) idx
                      let res := PaInG.br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai alf ala ali lef lea lez lei projs proofsOf proofs
                      insertCoreUp singleton insert emptyCol l1 l2 idx res nx
                else
                  if kind == "g"
                  then
                    match T with
                    | .dead =>
                        let gnodes := ListProd.nil.insert_PaInG_nat singleton insert fidx idx
                        let res := PaInG.br .nil .empty gnodes .nil .nil .nil .empty .nil .dead .dead emptyCol .dead .dead emptyCol .dead .dead emptyCol .dead .dead .dead emptyCol .empty .dead .dead
                        insertCoreUp singleton insert emptyCol l1 l2 idx res nx
                    | .br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai alf ala ali lef lea lez lei projs proofsOf proofs =>
                        let gnodes := gnodes.insert_PaInG_nat singleton insert fidx idx
                        let res := PaInG.br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai alf ala ali lef lea lez lei projs proofsOf proofs
                        insertCoreUp singleton insert emptyCol l1 l2 idx res nx
                  else
                    if kind == "u"
                    then
                      match T with
                      | .dead =>
                          let unodes := ListProd.nil.insert_PaInG_nat singleton insert fidx idx
                          let res := PaInG.br .nil .empty .nil unodes .nil .nil .empty .nil .dead .dead emptyCol .dead .dead emptyCol .dead .dead emptyCol .dead .dead .dead emptyCol .empty .dead .dead
                          insertCoreUp singleton insert emptyCol l1 l2 idx res nx
                      | .br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai alf ala ali lef lea lez lei projs proofsOf proofs =>
                          let unodes := unodes.insert_PaInG_nat singleton insert fidx idx
                          let res := PaInG.br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai alf ala ali lef lea lez lei projs proofsOf proofs
                          insertCoreUp singleton insert emptyCol l1 l2 idx res nx
                    else
                      throwError s!"[insertCore] fvar not in knonw format: {repr fid}"
            | _ => throwError s!"[insertCore] fvar not in knonw format: {repr fid}"
        | _ => throwError s!"[insertCore] unexpected atom {← PpExpr e l1 l2}"


@[specialize,inline]
def insert
  (l1 : LocalContext) (l2 : LocalInstances)
  (e : Expr) (idx : Nat) (T : PaInG IdxCollType)
  (emptyCol : IdxCollType) (singleton : Nat → IdxCollType) (insert : Nat → IdxCollType → IdxCollType)
  : MetaM (Prod3 (PaInG IdxCollType) LocalContext LocalInstances) := do
    insertCoreUp singleton insert emptyCol l1 l2 idx .dead (← insertCoreDown l1 l2 false 0 e T .nil) --false 0 e idx T emptyCol intersect empty? k

@[specialize,inline]
def ofList
  (l1 : LocalContext) (l2 : LocalInstances)
  (l : List (Nat × Expr)) (T : PaInG IdxCollType)
  (emptyCol : IdxCollType) (singleton : Nat → IdxCollType) (insert : Nat → IdxCollType → IdxCollType)
  : MetaM (Prod3 (PaInG IdxCollType) LocalContext LocalInstances) := do
  let rec @[specialize] go (l1 : LocalContext) (l2 : LocalInstances) (T : PaInG IdxCollType) : List (Nat × Expr) → MetaM (Prod3 (PaInG IdxCollType) LocalContext LocalInstances)
    | [] => return ⟨T,l1,l2⟩
    | (idx,e) :: more => do let ⟨res,l1,l2⟩ ←  T.insert l1 l2 e idx emptyCol singleton insert ; go l1 l2 res more
  go l1 l2 T l


@[specialize,inline]
def ofListProd
  (l1 : LocalContext) (l2 : LocalInstances)
  (l : ListProd Nat Expr) (T : PaInG IdxCollType)
  (emptyCol : IdxCollType) (singleton : Nat → IdxCollType) (insert : Nat → IdxCollType → IdxCollType)
  : MetaM (Prod3 (PaInG IdxCollType) LocalContext LocalInstances) := do
  let rec @[specialize] go (l1 : LocalContext) (l2 : LocalInstances) (T : PaInG IdxCollType) : ListProd Nat Expr → MetaM (Prod3 (PaInG IdxCollType) LocalContext LocalInstances)
    | .nil => return ⟨T,l1,l2⟩
    | .cons idx e more => do let ⟨res,l1,l2⟩ ←  T.insert l1 l2 e idx emptyCol singleton insert ; go l1 l2 res more
  go l1 l2 T l



@[specialize,inline]
def insertZetaFvs
  (l1 : LocalContext) (l2 : LocalInstances)
  (e : Expr) (idx : Nat) (T : PaInG IdxCollType)
  (emptyCol : IdxCollType) (singleton : Nat → IdxCollType) (insert : Nat → IdxCollType → IdxCollType)
  : MetaM (Prod3 (PaInG IdxCollType) LocalContext LocalInstances) := do
    insertCoreUp singleton insert emptyCol l1 l2 idx .dead (← insertCoreDown l1 l2 false 0 (← e.zetaFvs l1 l2) T .nil)




@[specialize]
partial def insertMultiCoreUp
  (insert : IdxCollType → IdxCollType → IdxCollType) (emptyCol : IdxCollType)
  (l1 : LocalContext) (l2 : LocalInstances)
  (idx : IdxCollType)
  (sofar : PaInG IdxCollType) (todo : insertCoreType IdxCollType)
  : MetaM (Prod3 (PaInG IdxCollType) LocalContext LocalInstances) := do
    match todo with
    | .nil => return ⟨sofar,l1,l2⟩
    | .proof fst depth e T nx =>
        if fst
        then
          match T with
          | .dead =>
              let res := PaInG.br .nil .empty .nil .nil .nil .nil .empty .nil .dead .dead emptyCol .dead .dead emptyCol .dead .dead emptyCol .dead .dead .dead emptyCol .empty sofar .dead
              let NX ← insertCoreDown l1 l2 true depth e .dead <| .proof false depth e res nx
              insertMultiCoreUp insert emptyCol l1 l2 idx .dead NX
          | .br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai alf ala ali lef lea lez lei projs _ proofs =>
              let res := PaInG.br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai alf ala ali lef lea lez lei projs sofar proofs
              let NX ← insertCoreDown l1 l2 true depth e proofs <| .proof false depth e res nx
              insertMultiCoreUp insert emptyCol l1 l2 idx .dead NX
        else
          match T with
          | .dead => -- shouldn't ?
              let res := PaInG.br .nil .empty .nil .nil .nil .nil .empty .nil .dead .dead emptyCol .dead .dead emptyCol .dead .dead emptyCol .dead .dead .dead emptyCol .empty .dead sofar
              insertMultiCoreUp insert emptyCol l1 l2 idx res nx
          | .br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai alf ala ali lef lea lez lei projs proofsOf _ =>
              let res := PaInG.br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai alf ala ali lef lea lez lei projs proofsOf sofar
              insertMultiCoreUp insert emptyCol l1 l2 idx res nx
    | .app fst depth a T nx =>
        if fst
        then
          match T with
          | .dead =>
              let res := PaInG.br .nil .empty .nil .nil .nil .nil .empty .nil sofar .dead emptyCol .dead .dead emptyCol .dead .dead emptyCol .dead .dead .dead emptyCol .empty .dead .dead
              let NX ← insertCoreDown l1 l2 false depth a .dead <| .app false depth a res nx
              insertMultiCoreUp insert emptyCol l1 l2 idx .dead NX
          | .br tnodes lnodes gnodes unodes bvars sorts consts lits _ apa api laf laa lai alf ala ali lef lea lez lei projs proofsOf proofs =>
              let res := PaInG.br tnodes lnodes gnodes unodes bvars sorts consts lits sofar apa api laf laa lai alf ala ali lef lea lez lei projs proofsOf proofs
              let NX ← insertCoreDown l1 l2 false depth a apa <| .app false depth a res nx
              insertMultiCoreUp insert emptyCol l1 l2 idx .dead NX
        else
          match T with
          | .dead => -- shouldn't ?
              let api := idx
              let res := PaInG.br .nil .empty .nil .nil .nil .nil .empty .nil .dead sofar api .dead .dead emptyCol .dead .dead emptyCol .dead .dead .dead emptyCol .empty .dead .dead
              insertMultiCoreUp insert emptyCol l1 l2 idx res nx
          | .br tnodes lnodes gnodes unodes bvars sorts consts lits apf _ api laf laa lai alf ala ali lef lea lez lei projs proofsOf proofs =>
              let api := insert idx api
              let res := PaInG.br tnodes lnodes gnodes unodes bvars sorts consts lits apf sofar api laf laa lai alf ala ali lef lea lez lei projs proofsOf proofs
              insertMultiCoreUp insert emptyCol l1 l2 idx res nx
    | .lam fst depth f a T nx =>
        if fst
        then
          match T with
          | .dead =>
              let res := PaInG.br .nil .empty .nil .nil .nil .nil .empty .nil .dead .dead emptyCol sofar .dead emptyCol .dead .dead emptyCol .dead .dead .dead emptyCol .empty .dead .dead
              let w ← worker depth
              let ⟨_,a,l1,l2⟩ ← withFreeing w f a l1 l2
              let NX ← insertCoreDown l1 l2 false (depth +1) a .dead <| .lam false (depth +1) f a res nx
              insertMultiCoreUp insert emptyCol l1 l2 idx .dead NX
          | .br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api _ laa lai alf ala ali lef lea lez lei projs proofsOf proofs =>
              let res := PaInG.br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api sofar laa lai alf ala ali lef lea lez lei projs proofsOf proofs
              let w ← worker depth
              let ⟨_,a,l1,l2⟩ ← withFreeing w f a l1 l2
              let NX ← insertCoreDown l1 l2 false (depth +1) a laa <| .lam false (depth +1) f a res nx
              insertMultiCoreUp insert emptyCol l1 l2 idx .dead NX
        else
          match T with
          | .dead => -- shouldn't ?
              let lai := idx
              let res := PaInG.br .nil .empty .nil .nil .nil .nil .empty .nil .dead .dead emptyCol .dead sofar lai .dead .dead emptyCol .dead .dead .dead emptyCol .empty .dead .dead
              insertMultiCoreUp insert emptyCol l1 l2 idx res nx
          | .br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf _ lai alf ala ali lef lea lez lei projs proofsOf proofs =>
              let lai := insert idx lai
              let res := PaInG.br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf sofar lai alf ala ali lef lea lez lei projs proofsOf proofs
              insertMultiCoreUp insert emptyCol l1 l2 idx res nx
    | .all fst depth f a T nx =>
        if fst
        then
          match T with
          | .dead =>
              let res := PaInG.br .nil .empty .nil .nil .nil .nil .empty .nil .dead .dead emptyCol .dead .dead emptyCol sofar .dead emptyCol .dead .dead .dead emptyCol .empty .dead .dead
              let w ← worker depth
              let ⟨_,a,l1,l2⟩ ← withFreeing w f a l1 l2
              let NX ← insertCoreDown l1 l2 false (depth +1) a .dead <| .all false (depth +1) f a res nx
              insertMultiCoreUp insert emptyCol l1 l2 idx .dead NX
          | .br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai _ ala ali lef lea lez lei projs proofsOf proofs =>
              let res := PaInG.br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai sofar ala ali lef lea lez lei projs proofsOf proofs
              let w ← worker depth
              let ⟨_,a,l1,l2⟩ ← withFreeing w f a l1 l2
              let NX ← insertCoreDown l1 l2 false (depth +1) a ala <| .all false (depth +1) f a res nx
              insertMultiCoreUp insert emptyCol l1 l2 idx .dead NX
        else
          match T with
          | .dead => -- shouldn't ?
              let ali := idx
              let res := PaInG.br .nil .empty .nil .nil .nil .nil .empty .nil .dead .dead emptyCol .dead .dead emptyCol .dead sofar ali .dead .dead .dead emptyCol .empty .dead .dead
              insertMultiCoreUp insert emptyCol l1 l2 idx res nx
          | .br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai alf _ ali lef lea lez lei projs proofsOf proofs =>
              let ali := insert idx ali
              let res := PaInG.br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai alf sofar ali lef lea lez lei projs proofsOf proofs
              insertMultiCoreUp insert emptyCol l1 l2 idx res nx
    | .letE fst depth f a z T nx =>
        if fst == 0
        then
          match T with
          | .dead =>
              let res := PaInG.br .nil .empty .nil .nil .nil .nil .empty .nil .dead .dead emptyCol .dead .dead emptyCol .dead .dead emptyCol sofar .dead .dead emptyCol .empty .dead .dead
              let NX ← insertCoreDown l1 l2 false depth a .dead <| .letE 1 depth f a z res nx
              insertMultiCoreUp insert emptyCol l1 l2 idx .dead NX
          | .br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai alf ala ali _ lea lez lei projs proofsOf proofs =>
              let res := PaInG.br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai alf ala ali sofar lea lez lei projs proofsOf proofs
              let NX ← insertCoreDown l1 l2 false depth a lea <| .letE 1 depth f a z res nx
              insertMultiCoreUp insert emptyCol l1 l2 idx .dead NX
        else if fst == 1
        then
          match T with
          | .dead =>
              let res := PaInG.br .nil .empty .nil .nil .nil .nil .empty .nil .dead .dead emptyCol .dead .dead emptyCol .dead .dead emptyCol .dead sofar .dead emptyCol .empty .dead .dead
              let w ← worker depth
              let ⟨_,z,l1,l2⟩ ← withFreeingLet w f a z l1 l2
              let NX ← insertCoreDown l1 l2 false (depth+1) z .dead <| .letE 2 (depth+1) f a z res nx
              insertMultiCoreUp insert emptyCol l1 l2 idx .dead NX
          | .br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai alf ala ali lef _ lez lei projs proofsOf proofs =>
              let res := PaInG.br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai alf ala ali lef sofar lez lei projs proofsOf proofs
              let w ← worker depth
              let ⟨_,z,l1,l2⟩ ← withFreeingLet w f a z l1 l2
              let NX ← insertCoreDown l1 l2 false (depth+1) z lez <| .letE 2 (depth+1) f a z res nx
              insertMultiCoreUp insert emptyCol l1 l2 idx .dead NX
        else
          match T with
          | .dead => -- shouldn't ?
              let lei := idx
              let res := PaInG.br .nil .empty .nil .nil .nil .nil .empty .nil .dead .dead emptyCol .dead .dead emptyCol .dead .dead emptyCol .dead .dead sofar lei .empty .dead .dead
              insertMultiCoreUp insert emptyCol l1 l2 idx res nx
          | .br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai alf ala ali lef lea _ lei projs proofsOf proofs =>
              let lei := insert idx lei
              let res := PaInG.br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai alf ala ali lef lea sofar lei projs proofsOf proofs
              insertMultiCoreUp insert emptyCol l1 l2 idx res nx
    | .proj name pidx T nx =>
        match T with
        | .dead =>
            let is := idx
            let projs := CTrie.empty.insert name (.cons is (pidx,sofar) .nil)
            let res := PaInG.br .nil .empty .nil .nil .nil .nil .empty .nil .dead .dead emptyCol .dead .dead emptyCol .dead .dead emptyCol .dead .dead .dead emptyCol projs .dead .dead
            insertMultiCoreUp insert emptyCol l1 l2 idx res nx
        | .br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai alf ala ali lef lea lez lei projs proofsOf proofs =>
            let projs := projs.upsert name ( fun
              | .none => .some <| .cons idx (pidx,sofar) .nil
              | .some L => .some <| L.modifyAdd' (fun (i,_) => i == pidx) (fun en => {en with snd := sofar}) (insert idx) (pidx,sofar) idx)
            let res := PaInG.br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai alf ala ali lef lea lez lei projs proofsOf proofs
            insertMultiCoreUp insert emptyCol l1 l2 idx res nx
    | .atom depth e T nx =>
        match e with
        | .bvar i =>
            match T with
            | .dead =>
                let res := PaInG.br .nil .empty .nil .nil (.cons idx i .nil) .nil .empty .nil .dead .dead emptyCol .dead .dead emptyCol .dead .dead emptyCol .dead .dead .dead emptyCol .empty .dead .dead
                insertMultiCoreUp insert emptyCol l1 l2 idx res nx
            | .br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai alf ala ali lef lea lez lei projs proofsOf proofs =>
                let bvars := bvars.insert_PaInG_nat_multi insert i idx
                let res := PaInG.br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai alf ala ali lef lea lez lei projs proofsOf proofs
                insertMultiCoreUp insert emptyCol l1 l2 idx res nx
        | .sort l =>
            match T with
            | .dead =>
                let res := PaInG.br .nil .empty .nil .nil .nil (.cons idx l .nil) .empty .nil .dead .dead emptyCol .dead .dead emptyCol .dead .dead emptyCol .dead .dead .dead emptyCol .empty .dead .dead
                insertMultiCoreUp insert emptyCol l1 l2 idx res nx
            | .br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai alf ala ali lef lea lez lei projs proofsOf proofs =>
                let sorts := sorts.modifyAdd (fun x => insert idx x) l idx
                let res := PaInG.br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai alf ala ali lef lea lez lei projs proofsOf proofs
                insertMultiCoreUp insert emptyCol l1 l2 idx res nx
        | .const n l =>
            match T with
            | .dead =>
                let consts := ListProd.insert_PaInG_const_multi insert .empty n l idx
                let res := PaInG.br .nil .empty .nil .nil .nil .nil consts .nil .dead .dead emptyCol .dead .dead emptyCol .dead .dead emptyCol .dead .dead .dead emptyCol .empty .dead .dead
                insertMultiCoreUp insert emptyCol l1 l2 idx res nx
            | .br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai alf ala ali lef lea lez lei projs proofsOf proofs =>
                let consts := ListProd.insert_PaInG_const_multi insert consts n l idx
                let res := PaInG.br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai alf ala ali lef lea lez lei projs proofsOf proofs
                insertMultiCoreUp insert emptyCol l1 l2 idx res nx
        | .lit l =>
            match T with
            | .dead =>
                let res := PaInG.br .nil .empty .nil .nil .nil .nil .empty (.cons idx l .nil) .dead .dead emptyCol .dead .dead emptyCol .dead .dead emptyCol .dead .dead .dead emptyCol .empty .dead .dead
                insertMultiCoreUp insert emptyCol l1 l2 idx res nx
            | .br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai alf ala ali lef lea lez lei projs proofsOf proofs =>
                let lits := lits.modifyAdd (fun x => insert idx x) l idx
                let res := PaInG.br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai alf ala ali lef lea lez lei projs proofsOf proofs
                insertMultiCoreUp insert emptyCol l1 l2 idx res nx
        | .mvar mid =>
            match mid.name with
            | .num (.num module thmIdx) pos =>
                match T with
                | .dead =>
                    let lnodes := ListProd.insert_PaInG_lnode_multi insert .empty module (thmIdx, pos) idx
                    let res := PaInG.br .nil lnodes .nil .nil .nil .nil .empty .nil .dead .dead emptyCol .dead .dead emptyCol .dead .dead emptyCol .dead .dead .dead emptyCol .empty .dead .dead
                    insertMultiCoreUp insert emptyCol l1 l2 idx res nx
                | .br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai alf ala ali lef lea lez lei projs proofsOf proofs =>
                    let lnodes := ListProd.insert_PaInG_lnode_multi insert lnodes module (thmIdx, pos) idx
                    let res := PaInG.br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai alf ala ali lef lea lez lei projs proofsOf proofs
                    insertMultiCoreUp insert emptyCol l1 l2 idx res nx
            | _ => throwError s!"[insertCore] mvar not in lnode format: {repr mid}"
        | .fvar fid =>
            match fid.name with
            | .num (.num _ backIdx) pos =>
                match T with
                | .dead =>
                    let tnodes := ListProd.nil.insert_PaInG_lex_multi insert (backIdx, pos) idx
                    let res := PaInG.br tnodes .empty .nil .nil .nil .nil .empty .nil .dead .dead emptyCol .dead .dead emptyCol .dead .dead emptyCol .dead .dead .dead emptyCol .empty .dead .dead
                    insertMultiCoreUp insert emptyCol l1 l2 idx res nx
                | .br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai alf ala ali lef lea lez lei projs proofsOf proofs =>
                    let tnodes := tnodes.insert_PaInG_lex_multi insert (backIdx, pos) idx
                    let res := PaInG.br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai alf ala ali lef lea lez lei projs proofsOf proofs
                    insertMultiCoreUp insert emptyCol l1 l2 idx res nx
            | .num (.str _ kind) fidx =>
                if kind == "w"
                then
                  match T with
                  | .dead =>
                      let bvars := ListProd.nil.insert_PaInG_nat_multi insert (depth - 1 - fidx) idx
                      let res := PaInG.br .nil .empty .nil .nil bvars .nil .empty .nil .dead .dead emptyCol .dead .dead emptyCol .dead .dead emptyCol .dead .dead .dead emptyCol .empty .dead .dead
                      insertMultiCoreUp insert emptyCol l1 l2 idx res nx
                  | .br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai alf ala ali lef lea lez lei projs proofsOf proofs =>
                      let bvars := bvars.insert_PaInG_nat_multi insert (depth - 1 - fidx) idx
                      let res := PaInG.br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai alf ala ali lef lea lez lei projs proofsOf proofs
                      insertMultiCoreUp insert emptyCol l1 l2 idx res nx
                else
                  if kind == "g"
                  then
                    match T with
                    | .dead =>
                        let gnodes := ListProd.nil.insert_PaInG_nat_multi insert fidx idx
                        let res := PaInG.br .nil .empty gnodes .nil .nil .nil .empty .nil .dead .dead emptyCol .dead .dead emptyCol .dead .dead emptyCol .dead .dead .dead emptyCol .empty .dead .dead
                        insertMultiCoreUp insert emptyCol l1 l2 idx res nx
                    | .br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai alf ala ali lef lea lez lei projs proofsOf proofs =>
                        let gnodes := gnodes.insert_PaInG_nat_multi insert fidx idx
                        let res := PaInG.br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai alf ala ali lef lea lez lei projs proofsOf proofs
                        insertMultiCoreUp insert emptyCol l1 l2 idx res nx
                  else
                    if kind == "u"
                    then
                      match T with
                      | .dead =>
                          let unodes := ListProd.nil.insert_PaInG_nat_multi insert fidx idx
                          let res := PaInG.br .nil .empty .nil unodes .nil .nil .empty .nil .dead .dead emptyCol .dead .dead emptyCol .dead .dead emptyCol .dead .dead .dead emptyCol .empty .dead .dead
                          insertMultiCoreUp insert emptyCol l1 l2 idx res nx
                      | .br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai alf ala ali lef lea lez lei projs proofsOf proofs =>
                          let unodes := unodes.insert_PaInG_nat_multi insert fidx idx
                          let res := PaInG.br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai alf ala ali lef lea lez lei projs proofsOf proofs
                          insertMultiCoreUp insert emptyCol l1 l2 idx res nx
                    else
                      throwError s!"[insertCore] fvar not in knonw format: {repr fid}"
            | _ => throwError s!"[insertCore] fvar not in knonw format: {repr fid}"
        | _ => throwError s!"[insertCore] unexpected atom {← PpExpr e l1 l2}"


@[specialize,inline]
def insertMulti
  (l1 : LocalContext) (l2 : LocalInstances)
  (e : Expr) (idx : IdxCollType) (T : PaInG IdxCollType)
  (emptyCol : IdxCollType) (insert : IdxCollType → IdxCollType → IdxCollType)
  : MetaM (Prod3 (PaInG IdxCollType) LocalContext LocalInstances) := do
    insertMultiCoreUp insert emptyCol l1 l2 idx .dead (← insertCoreDown l1 l2 false 0 e T .nil) --false 0 e idx T emptyCol intersect empty? k



/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/


import LeanGrow.Src.Data.PathIndexG.Operations
import LeanGrow.Src.Caching.Formating.Types
import LeanGrow.Src.Data.SetTrie.Specialize



open Lean Meta

variable {IdxCollType : Type _}

namespace PaInG


@[specialize, inline]
private def helpSpe_1 [Repr IdxCollType]
  (l1 : LocalContext) (l2 : LocalInstances)
  (thmData : CTrie (Array ThmFormat))
  (union : IdxCollType → IdxCollType → IdxCollType)
  (L R : CTrie (ListProd IdxCollType (Nat × Nat)))
  : MetaM (CTrie (ListProd IdxCollType (Nat × Nat))) := do
  mtracing
  L.foldMcps R (fun lmod ldata res q0 => do
    let lMod := (String.fromUTF8! lmod).toName
    match thmData.find? lmod with
    | .none => throwError s!"[helpSpe_1] module {(String.fromUTF8! lmod)} not in thmData"
    | .some thms =>
        ldata.foldlMcps res (fun linds (thmIdx,pos) res q1 => do
          mtrace on .zero with s!"[helpSpe_1] left lnode {lMod} {(thmIdx,pos)}, with indices {repr linds}"
          (thms[thmIdx]!).mctx.loadNoCo
          let ln := Expr.mvar ⟨lnode lMod thmIdx pos⟩
          res.foldMcps (Option.none : Option (Nat × Nat)) (fun rmod rdata _ q2 => do
            let rMod := (String.fromUTF8! rmod).toName
            rdata.foldlMcps (Option.none : Option (Nat × Nat)) (fun rinds (t,p) S q3 => do
              mtrace on .zero with s!"[helpSpe_1] right lnode {rMod} {(t,p)}, with indices {repr rinds}"
              let rn := Expr.mvar ⟨lnode rMod t p⟩ -- is assumed to have already been loaded durring merge session !
              if (← defEqWiMv ln rn l1 l2).isSome
              then
                mtrace on .zero with s!"[helpSpe_1] positive defeq"
                let res := res.upsert rmod (fun
                  | .none => panic "helpSpe_1 1"  -- shouldn't
                  | .some list => .some <| list.foldl .nil (fun I b@(T,P) lres =>
                        if T == t && P == p
                        then .cons (union linds I) b lres
                        else .cons I b lres
                        )
                  )
                q1 res
              else
                mtrace on .zero with s!"[helpSpe_1] negative defeq"
                q3 S
              ) <| fun matched => do
                match matched with
                | .none => q2 matched
                | .some .. => panic "helpSpe_1 2"  -- shouldn't
        ) <| fun matched => do
          match matched with
          | .none =>
              let res := res.upsert lmod (fun
                | .none => .some <| .cons linds (thmIdx, pos) .nil
                | .some x => .some <| .cons linds (thmIdx, pos) x)
              mtrace on .zero with s!"[helpSpe_1] adding lnode {lMod} {(thmIdx,pos)}, with indices {repr linds}"
              q1 res
          | .some .. => panic "helpSpe_1 3"  -- shouldn't
      ) <| fun res =>
          q0 res
  ) <| fun res => return res



@[specialize]
partial def mergeLSpeDown [Repr IdxCollType]
  (union : IdxCollType → IdxCollType → IdxCollType)
  (helpSpe : CTrie (ListProd IdxCollType (Nat × Nat)) → CTrie (ListProd IdxCollType (Nat × Nat)) → MetaM (CTrie (ListProd IdxCollType (Nat × Nat))))
  (A B : PaInG IdxCollType)
  (sofar : mergeT IdxCollType) (vals : List (PaInG IdxCollType)) : MetaM ((mergeT IdxCollType) × (List (PaInG IdxCollType))) :=
  let rec debt : List Level → List Level → Bool
    | x :: xs , y :: ys => if x.EqUpToMVar y then debt xs ys else false
    | [], [] => true
    | _, _ => false
  match A, B with
  | .dead, .dead => return (.done A sofar,vals)
  | .br .., .dead => return (.done A sofar,vals)
  | .dead, .br .. => return (.done B sofar, vals)
  | .br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai alf ala ali lef lea lez lei projs proofsOf proofs,
    .br tnodes' lnodes' gnodes' unodes' bvars' sorts' consts' lits' apf' apa' api' laf' laa' lai' alf' ala' ali' lef' lea' lez' lei' projs' proofsOf' proofs' => do
    let nt := help_1 union (· == ·) tnodes tnodes'
    let nl ← helpSpe lnodes lnodes'
    let ng := help_1 union (· == ·) gnodes gnodes'
    let nu := help_1 union (· == ·) unodes unodes'
    let nb := help_1 union (· == ·) bvars bvars'
    let ns := help_1 union Level.EqUpToMVar sorts sorts'
    let nc := help_2 union debt consts consts'
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
    mergeLSpeDown union helpSpe apf apf' sofar vals



@[specialize]
partial def mergeLSpeUp {IdxCollType : Type} [Repr IdxCollType]
  (union : IdxCollType → IdxCollType → IdxCollType) (emptyCol : IdxCollType)
  (helpSpe : CTrie (ListProd IdxCollType (Nat × Nat)) → CTrie (ListProd IdxCollType (Nat × Nat)) → MetaM (CTrie (ListProd IdxCollType (Nat × Nat))))
  (T : PaInG IdxCollType)
  (todo : mergeT IdxCollType) (vals : List (PaInG IdxCollType)) : MetaM (PaInG IdxCollType) := do
  match todo with
  | .nil => return T
  | .done T nx => mergeLSpeUp union emptyCol helpSpe T nx vals
  | .apa l r nx =>
      match vals with
      | [] => panic! "mergeLSpeUp"
      | .dead :: more =>
          let res := .br .nil .empty .nil .nil .nil .nil .empty .nil T .dead emptyCol .dead .dead emptyCol .dead .dead emptyCol .dead .dead .dead emptyCol .empty .dead .dead
          let (nx,vals) := ← mergeLSpeDown union helpSpe l r nx (res :: more)
          mergeLSpeUp union emptyCol helpSpe .dead nx vals
      | .br tnodes lnodes gnodes unodes bvars sorts consts lits _ apa api laf laa lai alf ala ali lef lea lez lei projs proofsOf proofs :: more =>
          let res := .br tnodes lnodes gnodes unodes bvars sorts consts lits T apa api laf laa lai alf ala ali lef lea lez lei projs proofsOf proofs
          let (nx,vals) := ← mergeLSpeDown union helpSpe l r nx (res :: more)
          mergeLSpeUp union emptyCol helpSpe .dead nx vals
  | .laf l r nx =>
      match vals with
      | [] => panic! "mergeLSpeUp"
      | .dead :: more =>
          let res := .br .nil .empty .nil .nil .nil .nil .empty .nil .dead T emptyCol .dead .dead emptyCol .dead .dead emptyCol .dead .dead .dead emptyCol .empty .dead .dead
          let (nx,vals) := ← mergeLSpeDown union helpSpe l r nx (res :: more)
          mergeLSpeUp union emptyCol helpSpe .dead nx vals
      | .br tnodes lnodes gnodes unodes bvars sorts consts lits apf _ api laf laa lai alf ala ali lef lea lez lei projs proofsOf proofs :: more =>
          let res := .br tnodes lnodes gnodes unodes bvars sorts consts lits apf T api laf laa lai alf ala ali lef lea lez lei projs proofsOf proofs
          let (nx,vals) := ← mergeLSpeDown union helpSpe l r nx (res :: more)
          mergeLSpeUp union emptyCol helpSpe .dead nx vals
  | .laa l r nx =>
      match vals with
      | [] => panic! "mergeLSpeUp"
      | .dead :: more =>
          let res := .br .nil .empty .nil .nil .nil .nil .empty .nil .dead .dead emptyCol T .dead emptyCol .dead .dead emptyCol .dead .dead .dead emptyCol .empty .dead .dead
          let (nx,vals) := ← mergeLSpeDown union helpSpe l r nx (res :: more)
          mergeLSpeUp union emptyCol helpSpe .dead nx vals
      | .br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api _ laa lai alf ala ali lef lea lez lei projs proofsOf proofs :: more =>
          let res := .br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api T laa lai alf ala ali lef lea lez lei projs proofsOf proofs
          let (nx,vals) := ← mergeLSpeDown union helpSpe l r nx (res :: more)
          mergeLSpeUp union emptyCol helpSpe .dead nx vals
  | .alf l r nx =>
      match vals with
      | [] => panic! "mergeLSpeUp"
      | .dead :: more =>
          let res := .br .nil .empty .nil .nil .nil .nil .empty .nil .dead .dead emptyCol .dead T emptyCol .dead .dead emptyCol .dead .dead .dead emptyCol .empty .dead .dead
          let (nx,vals) := ← mergeLSpeDown union helpSpe l r nx (res :: more)
          mergeLSpeUp union emptyCol helpSpe .dead nx vals
      | .br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf _ lai alf ala ali lef lea lez lei projs proofsOf proofs :: more =>
          let res := .br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf T lai alf ala ali lef lea lez lei projs proofsOf proofs
          let (nx,vals) := ← mergeLSpeDown union helpSpe l r nx (res :: more)
          mergeLSpeUp union emptyCol helpSpe .dead nx vals
  | .ala l r nx =>
      match vals with
      | [] => panic! "mergeLSpeUp"
      | .dead :: more =>
          let res := .br .nil .empty .nil .nil .nil .nil .empty .nil .dead .dead emptyCol .dead .dead emptyCol T .dead emptyCol .dead .dead .dead emptyCol .empty .dead .dead
          let (nx,vals) := ← mergeLSpeDown union helpSpe l r nx (res :: more)
          mergeLSpeUp union emptyCol helpSpe .dead nx vals
      | .br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai _ ala ali lef lea lez lei projs proofsOf proofs :: more =>
          let res := .br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai T ala ali lef lea lez lei projs proofsOf proofs
          let (nx,vals) := ← mergeLSpeDown union helpSpe l r nx (res :: more)
          mergeLSpeUp union emptyCol helpSpe .dead nx vals
  | .lef l r nx =>
      match vals with
      | [] => panic! "mergeLSpeUp"
      | .dead :: more =>
          let res := .br .nil .empty .nil .nil .nil .nil .empty .nil .dead .dead emptyCol .dead .dead emptyCol .dead T emptyCol .dead .dead .dead emptyCol .empty .dead .dead
          let (nx,vals) := ← mergeLSpeDown union helpSpe l r nx (res :: more)
          mergeLSpeUp union emptyCol helpSpe .dead nx vals
      | .br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai alf _ ali lef lea lez lei projs proofsOf proofs :: more =>
          let res := .br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai alf T ali lef lea lez lei projs proofsOf proofs
          let (nx,vals) := ← mergeLSpeDown union helpSpe l r nx (res :: more)
          mergeLSpeUp union emptyCol helpSpe .dead nx vals
  | .lea l r nx =>
      match vals with
      | [] => panic! "mergeLSpeUp"
      | .dead :: more =>
          let res := .br .nil .empty .nil .nil .nil .nil .empty .nil .dead .dead emptyCol .dead .dead emptyCol .dead .dead emptyCol T .dead .dead emptyCol .empty .dead .dead
          let (nx,vals) := ← mergeLSpeDown union helpSpe l r nx (res :: more)
          mergeLSpeUp union emptyCol helpSpe .dead nx vals
      | .br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai alf ala ali _ lea lez lei projs proofsOf proofs :: more =>
          let res := .br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai alf ala ali T lea lez lei projs proofsOf proofs
          let (nx,vals) := ← mergeLSpeDown union helpSpe l r nx (res :: more)
          mergeLSpeUp union emptyCol helpSpe .dead nx vals
  | .lez l r nx =>
      match vals with
      | [] => panic! "mergeLSpeUp"
      | .dead :: more =>
          let res := .br .nil .empty .nil .nil .nil .nil .empty .nil .dead .dead emptyCol .dead .dead emptyCol .dead .dead emptyCol .dead T .dead emptyCol .empty .dead .dead
          let (nx,vals) := ← mergeLSpeDown union helpSpe l r nx (res :: more)
          mergeLSpeUp union emptyCol helpSpe .dead nx vals
      | .br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai alf ala ali lef _ lez lei projs proofsOf proofs :: more =>
          let res := .br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai alf ala ali lef T lez lei projs proofsOf proofs
          let (nx,vals) := ← mergeLSpeDown union helpSpe l r nx (res :: more)
          mergeLSpeUp union emptyCol helpSpe .dead nx vals
  | .sig1 nx =>
      match vals with
      | [] => panic! "mergeLSpeUp"
      | .dead :: more =>
          let res := .br .nil .empty .nil .nil .nil .nil .empty .nil .dead .dead emptyCol .dead .dead emptyCol .dead .dead emptyCol .dead .dead T emptyCol .empty .dead .dead
          mergeLSpeUp union emptyCol helpSpe .dead nx (res :: more)
      | .br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai alf ala ali lef lea _ lei projs proofsOf proofs :: more =>
          let res := .br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai alf ala ali lef lea T lei projs proofsOf proofs
          mergeLSpeUp union emptyCol helpSpe .dead nx (res :: more)
  | .projPre l r nx =>
      let (nx,vals) := ← mergeLSpeDown union helpSpe l r nx vals
      mergeLSpeUp union emptyCol helpSpe .dead nx vals
  | .projPost name i is nx =>
      match vals with
      | [] => panic! "mergeLSpeUp"
      | .dead :: more =>
          let res := .br .nil .empty .nil .nil .nil .nil .empty .nil .dead .dead emptyCol .dead .dead emptyCol .dead .dead emptyCol .dead .dead .dead emptyCol (CTrie.empty.insert name (ListProd.cons is (i,T) .nil)) .dead .dead
          mergeLSpeUp union emptyCol helpSpe .dead nx (res :: more)
      | .br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai alf ala ali lef lea lez lei projs proofsOf proofs :: more =>
          let projs := projs.upsert name (fun | .none => .some (ListProd.cons is (i,T) .nil) | .some e => .some (.cons is (i,T) e))
          let res := .br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai alf ala ali lef lea lez lei projs proofsOf proofs
          mergeLSpeUp union emptyCol helpSpe .dead nx (res :: more)
  | .proofsOf l r nx =>
      let (nx,vals) := ← mergeLSpeDown union helpSpe l r nx vals
      mergeLSpeUp union emptyCol helpSpe .dead nx vals
  | .sig2 nx =>
      match vals with
      | [] => panic! "mergeLSpeUp"
      | .dead :: more =>
          let res := .br .nil .empty .nil .nil .nil .nil .empty .nil .dead .dead emptyCol .dead .dead emptyCol .dead .dead emptyCol .dead .dead .dead emptyCol .empty T .dead
          mergeLSpeUp union emptyCol helpSpe .dead nx (res :: more)
      | .br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai alf ala ali lef lea lez lei projs _ proofs :: more =>
          let res := .br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai alf ala ali lef lea lez lei projs T proofs
          mergeLSpeUp union emptyCol helpSpe .dead nx (res :: more)
  | .proofs l r nx =>
      let (nx,vals) := ← mergeLSpeDown union helpSpe l r nx vals
      mergeLSpeUp union emptyCol helpSpe .dead nx vals
  | .sig3 nx =>
      match vals with
      | [] => panic! "mergeLSpeUp"
      | .dead :: more =>
          let res := .br .nil .empty .nil .nil .nil .nil .empty .nil .dead .dead emptyCol .dead .dead emptyCol .dead .dead emptyCol .dead .dead .dead emptyCol .empty .dead T
          mergeLSpeUp union emptyCol helpSpe res nx more
      | .br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai alf ala ali lef lea lez lei projs proofsOf _ :: more =>
          let res := .br tnodes lnodes gnodes unodes bvars sorts consts lits apf apa api laf laa lai alf ala ali lef lea lez lei projs proofsOf T
          mergeLSpeUp union emptyCol helpSpe res nx more




@[specialize]
private def helpSpe_2 [Repr IdxCollType]
  (l1 : LocalContext) (l2 : LocalInstances)
  (union : IdxCollType → IdxCollType → IdxCollType)
  (L R : CTrie (ListProd IdxCollType (Nat × Nat)))
  : MetaM (CTrie (ListProd IdxCollType (Nat × Nat))) := do
  mtracing
  L.foldMcps R (fun lmod ldata res q0 => do
    let lMod := (String.fromUTF8! lmod).toName
    ldata.foldlMcps res (fun linds (thmIdx,pos) res q1 => do
      let ln := Expr.mvar ⟨lnode lMod thmIdx pos⟩
      res.foldMcps (Option.none : Option (Nat × Nat)) (fun rmod rdata _ q2 => do
        let rMod := (String.fromUTF8! rmod).toName
        rdata.foldlMcps (Option.none : Option (Nat × Nat)) (fun rinds (t,p) S q3 => do
          mtrace on .zero with s!"[helpSpe_1] right lnode {rMod} {(t,p)}, with indices {repr rinds}"
          let rn := Expr.mvar ⟨lnode rMod t p⟩ -- is assumed to have already been loaded durring merge session !
          if (← defEqWiMv ln rn l1 l2).isSome
          then
            mtrace on .zero with s!"[helpSpe_1] positive defeq"
            let res := res.upsert rmod (fun
              | .none => panic "helpSpe_1 1"  -- shouldn't
              | .some list => .some <| list.foldl .nil (fun I b@(T,P) lres =>
                    if T == t && P == p
                    then .cons (union linds I) b lres
                    else .cons I b lres
                    )
              )
            q1 res
          else
            mtrace on .zero with s!"[helpSpe_1] negative defeq"
            q3 S
          ) <| fun matched => do
            match matched with
            | .none => q2 matched
            | .some .. => panic "helpSpe_1 2"  -- shouldn't
        ) <| fun matched => do
          match matched with
          | .none =>
              let res := res.upsert lmod (fun
                | .none => .some <| .cons linds (thmIdx, pos) .nil
                | .some x => .some <| .cons linds (thmIdx, pos) x)
              mtrace on .zero with s!"[helpSpe_1] adding lnode {lMod} {(thmIdx,pos)}, with indices {repr linds}"
              q1 res
          | .some .. => panic "helpSpe_1 3"  -- shouldn't
      ) <| fun res =>
          q0 res
  ) <| fun res => return res


/-- expects args to have disjoint index sets-/
@[specialize, inline]
partial def mergeLSpe [Repr IdxCollType]
  (union : IdxCollType → IdxCollType → IdxCollType) (emptyCol : IdxCollType)
  (l1 : LocalContext) (l2 : LocalInstances)
  (thmData : CTrie (Array ThmFormat))
  (A B : PaInG IdxCollType) : MetaM (PaInG IdxCollType) := do
  let (nx,vals) := ← mergeLSpeDown union (helpSpe_1 l1 l2 thmData union) A B .nil []
  mergeLSpeUp union emptyCol (helpSpe_1 l1 l2 thmData union) .dead nx vals


/-- expects args to have disjoint index sets-/
@[specialize, inline]
partial def mergeLSpeSpe [Repr IdxCollType]
  (union : IdxCollType → IdxCollType → IdxCollType) (emptyCol : IdxCollType)
  (l1 : LocalContext) (l2 : LocalInstances)
  (A B : PaInG IdxCollType) : MetaM (PaInG IdxCollType) := do
  let (nx,vals) := ← mergeLSpeDown union (helpSpe_2 l1 l2 union) A B .nil []
  mergeLSpeUp union emptyCol (helpSpe_2 l1 l2 union) .dead nx vals

end PaInG

@[specialize]
def SetTriePGSpe.ofList [Inhabited α] [Repr α] [Repr IdxCollType]
  (thmData : CTrie (Array ThmFormat))
  (intersect union difference : IdxCollType → IdxCollType → IdxCollType)
  (emptyCol : IdxCollType)  (empty? : IdxCollType → Bool) (size : IdxCollType → Nat)
  (l : ListProd (PaInG IdxCollType) α)
  : MetaM (SetTrieP α IdxCollType PaInG) :=
  trace set TracingFlags.none in do
  let res ← SetTrie.ofListMcps
    (PaInG.dead, PaInG.dead)
    (fun x (y,z) q => do q (PaInG.merge union emptyCol x y, ← PaInG.mergeLSpe union emptyCol {} {} thmData x z))
    (fun (x,y) =>
      trace on .zero with s!"[SetTrieP.ofList] x : {repr x}\n[SetTrieP.ofList] y : {repr y}\n" in
      match y.max intersect empty? size with
      | .none => OptionProd.none
      | .some inds m =>
          trace on .zero with s!"[SetTrieP.ofList] inds : {repr inds} ; m {m}\n" in
          let res := x.keepOnlyOfInds inds difference union emptyCol empty?
          -- ↑ should be buildIndices
          -- in fact, it should be x with all indices except for inds deleted
          -- so that we pass a PaIn, that we can use in addKey ↓
          let is := res.getIndices emptyCol union
          OptionProd.some (is, res) m
      )
    (fun x (is,_) q => q <| x.sharesIndicesWith intersect empty? is)
    (fun x (is,_) => x.deleteOfInds is difference emptyCol empty?)
    (fun x => match x.clean emptyCol empty? with | .dead => true | _ => false)
    (fun (_,es) q =>  q es)
    (fun (_,es) τ q => q <| PaInG.merge union emptyCol es τ)
    (PaInG.clean emptyCol empty?)
    l
    (fun x => return x)
  return SetTrieP.mk (PaInG.merge union emptyCol) .dead (PaInG.getIndices emptyCol union) res

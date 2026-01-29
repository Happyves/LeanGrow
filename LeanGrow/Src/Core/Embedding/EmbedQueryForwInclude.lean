
/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/



import LeanGrow.Src.Core.Embedding.EmbedQueryForwSimple


open Lean Meta

variable {IndexColType : Type}

private def compatible
  (l1 : LocalContext) (l2 : LocalInstances)
  (l r : (ListProd Nat Expr) × (ListProd Nat Level)) : MetaM (Option <| (ListProd Nat Expr) × (ListProd Nat Level)) := do
  l.2.foldlMcps r.2 (fun i lv R q =>
    match r.2.find? (fun x _ => x == i) with
    | .none => q <| .cons i lv R
    | .some _ clv => do
        if ← (do let res ← isLevelDefEq clv lv ; clearMvarAssignments ; return res)
        then q R
        else return Option.none
    ) <| fun lvlM => do
      l.1.foldlMcps r.1 (fun i lv R q =>
        match r.1.find? (fun x _ => x == i) with
        | .none => q <| .cons i lv R
        | .some _ clv => do
            if (← defEqWiMv clv lv l1 l2).isSome
            then q R
            else return Option.none
        ) <| fun expM => do
            return .some (expM, lvlM)


namespace PaInG

@[specialize, inline]
private def merge1
  (intersect : IndexColType → IndexColType → IndexColType) (empty? : IndexColType → Bool)
  {α : Type _} (compat : α → α → MetaM (Option α))
  (start : ListProd3 IndexColType IndexColType α)
  (L R : ListProd3 IndexColType IndexColType α)
  : MetaM (ListProd3 IndexColType IndexColType α):=
  let rec @[specialize] comp (done : ListProd3 IndexColType IndexColType α) (l r : IndexColType) (s : α) : (ListProd3 IndexColType IndexColType α) → MetaM (ListProd3 IndexColType IndexColType α)
    | .nil => return done
    | .cons nx1 nx2 sh more => do
        let I1 := intersect nx1 l
        if empty? I1
        then comp done l r s more
        else
          let I2 := intersect nx2 r
          if empty? I2
          then comp done l r s more
          else
            match ← compat s sh with
            | .none => comp done l r s more
            | .some ns =>  comp (.cons I1 I2 ns done) l r s more
  let rec @[specialize] go (done : ListProd3 IndexColType IndexColType α) : (ListProd3 IndexColType IndexColType α) → MetaM (ListProd3 IndexColType IndexColType α)
    | .nil =>
      return done
    | .cons l r s more => do
        let nx := (← comp .nil l r s R).foldl done (fun x y z R => .cons x y z R)
        go nx more
  go start L



@[specialize]
private def merge2 {α : Type _} (eq : α → α → Bool)
  (start : ListProd3 IndexColType IndexColType ((ListProd Nat Expr) × (ListProd Nat Level)))
  (L R : ListProd IndexColType α)
  : ListProd3 IndexColType IndexColType ((ListProd Nat Expr) × (ListProd Nat Level)) :=
  let rec @[specialize] go (done : ListProd3 IndexColType IndexColType ((ListProd Nat Expr) × (ListProd Nat Level)))
    : ListProd IndexColType α → ListProd3 IndexColType IndexColType ((ListProd Nat Expr) × (ListProd Nat Level))
    | .nil => done
    | .cons nx1 nx2 more =>
        match L.find? (fun _ y => eq y nx2) with
        | .none => .nil
        | .some x _ => go (.cons x nx1 (.nil, .nil) done) more
  go start R



@[specialize]
private def merge3 {α : Type _}
  (start : ListProd3 IndexColType IndexColType ((ListProd Nat Expr) × (ListProd Nat Level)))
  (L R : ListProd IndexColType α) (eq : α → α → MetaM (Option ((ListProd Nat Expr) × (ListProd Nat Level))))
  : MetaM <| ListProd3 IndexColType IndexColType ((ListProd Nat Expr) × (ListProd Nat Level)) :=
  let rec @[specialize] go (done : ListProd3 IndexColType IndexColType ((ListProd Nat Expr) × (ListProd Nat Level)))
    : ListProd IndexColType α → MetaM (ListProd3 IndexColType IndexColType ((ListProd Nat Expr) × (ListProd Nat Level)))
    | .nil => return done
    | .cons nx1 nx2 more =>
        L.foldlMcps (false,done) (fun x y s@(_,D) q => do
          match ← eq y nx2 with
          | .none => q s
          | .some (La,Ta) => q (true, .cons x nx1 (La,Ta) D)
          ) (fun (seen?, ndone) =>
            if seen?
            then go ndone more
            else return .nil)
  go start R

@[specialize, inline]
private def merge4
  (intersect difference : IndexColType → IndexColType → IndexColType) (empty? : IndexColType → Bool)
  {α : Type _} (compat : α → α → MetaM (Option α))
  (start : ListProd3 IndexColType IndexColType α)
  (L R : ListProd3 IndexColType IndexColType α)
  : MetaM (ListProd3 IndexColType IndexColType α):=
  let rec @[specialize] comp (done : ListProd3 IndexColType IndexColType α) (lrem rrem l r : IndexColType) (s : α) : (ListProd3 IndexColType IndexColType α) → MetaM (ListProd3 IndexColType IndexColType α)
    | .nil =>
        if empty? lrem || empty? rrem
        then return done
        else return .cons lrem rrem s done
    | .cons nx1 nx2 sh more => do
        let I1 := intersect nx1 l
        if empty? I1
        then comp done lrem rrem  l r s more
        else
          let I2 := intersect nx2 r
          if empty? I2
          then comp done lrem rrem  l r s more
          else
            match ← compat s sh with
            | .none => comp done lrem rrem l r s more
            | .some ns =>
                let lrem := difference lrem I1
                let rrem := difference rrem I2
                comp (.cons I1 I2 ns done) lrem rrem l r s more
  let rec @[specialize] go (done : ListProd3 IndexColType IndexColType α) : (ListProd3 IndexColType IndexColType α) → MetaM (ListProd3 IndexColType IndexColType α)
    | .nil =>
      return done
    | .cons l r s more => do
        let nx := (← comp .nil l r l r s R).foldl done (fun x y z R => .cons x y z R)
        go nx more
  go start L



/-- Q is ltx, l is hyps with lnodes, in the sense l ⊆ Q -/
@[specialize, inline]
partial def embedForwIncludeCore
  (thmData : CTrie (Array ThmFormat)) [Repr IndexColType]
  (intersect difference : IndexColType → IndexColType → IndexColType) (empty? : IndexColType → Bool)
  (l1 : LocalContext) (l2 : LocalInstances)
  (Q l : PaInG IndexColType)
  : MetaM <| ListProd3 IndexColType IndexColType ((ListProd Nat Expr) × (ListProd Nat Level)) :=
    let traceHelp (st : ListProd3 IndexColType IndexColType ((ListProd Nat Expr) × (ListProd Nat Level))) : MetaM String := do
      let pre ← st.foldlM ListProd3.nil (fun x y z R => return .cons x y (← z.1.foldlM ListProd.nil (fun x y R => return ListProd.cons x s!"{(← ppExpr y)}" R), z.2) R)
      return s!"{repr pre}"
    let rec @[specialize] go (Q l : PaInG IndexColType) : MetaM <| ListProd3 IndexColType IndexColType ((ListProd Nat Expr) × (ListProd Nat Level)) :=
      do -- trace set Tracing.Flags.none in do
      mtracing
      mtrace on .one with s!"[embedForwIncludeCore] Q : {← Q.pp l1 l2 [] 0 intersect empty?}"
      mtrace on .one with s!"[embedForwIncludeCore] l : {← l.pp l1 l2 [] 0 intersect empty?}"
      match Q, l with
      | _, .dead =>
          mtrace on .zero with s!"[embedForwIncludeCore] l is dead"
          return .nil
      | .dead, _=>
          mtrace on .zero with s!"[embedForwIncludeCore] Q is dead"
          return .nil
      | .br tnodes _ gnodes unodes bvars sorts consts lits apf apa api laf laa lai alf ala ali lef lea lez lei projs proofsOf proofs,
        -- **Debt** : unodes of Q should be built and merged with the current branch ; also, we don't expect unodes in l ...
        .br tnodes' lnodes' gnodes' unodes' bvars' sorts' consts' lits' apf' apa' api' laf' laa' lai' alf' ala' ali' lef' lea' lez' lei' projs' proofsOf' proofs' =>
          do
          if (empty? api && !(empty? api')) || (empty? lai && !(empty? lai')) || (empty? ali && !(empty? ali')) || (empty? lei && !(empty? lei'))
          then
            mtrace on .zero with s!"[embedForwIncludeCore] early return due to missing branch : api {repr api} api' {repr api'} ; lai {repr lai} lai' {repr lai'} ; ali {repr ali} ali' {repr ali'} ; lei {repr lei} lei' {repr lei'}"
            return .nil
          else
            let IT := merge2 (· == ·) .nil tnodes tnodes' -- we don't really expect any
            mtrace on .zero with s!"[embedForwIncludeCore] IT : {← traceHelp IT}"
            let QB ← Q.buildNoLoBvCore l1 l2 0 id intersect empty?
            let IL : ListProd3 IndexColType IndexColType ((ListProd Nat Expr) × (ListProd Nat Level)) := ← do
              let R ← lnodes'.foldM IT (fun nb D R => do
                    match thmData.find? nb with
                    | .none => return R
                    | .some moduleData =>
                        let R ← D.foldlM R (fun inds (thmIdx,pos) R => do
                          let thm := moduleData[thmIdx]!
                          thm.mctx.loadNoCo
                          let mv := Expr.mvar ⟨lnode (String.fromUTF8! nb).toName thmIdx pos⟩
                          let R ← QB.foldlM R (fun e qinds R => do
                            mtrace on .zero with s!"[embedForwIncludeCore] defeq e {← ppExpr e} vs lnode {repr mv} of type {← ppExpr <| ← inferType mv}"
                            match ← defEqWiMv mv e l1 l2 with
                            | .none =>
                                mtrace on .zero with s!"[embedForwIncludeCore] negative defeq"
                                return R
                            | .some (La,Ta) =>
                                mtrace on .zero with s!"[embedForwIncludeCore] positive defeq"
                                let mut Ls := .nil
                                for (lid,la) in La do
                                  match lid.name with
                                  | .num _ p => Ls := .cons p la Ls
                                  | _ => throwError s!"[embedForwIncludeCore] unsupporeted level mvar {repr lid}"
                                let mut Ts := .nil
                                for (lid,la) in Ta do
                                  match lid.name with
                                  | .num _ p => Ts := .cons p la Ts
                                  | _ => throwError s!"[embedForwIncludeCore] unsupporeted expr mvar {repr lid}"
                                return .cons qinds inds (Ts,Ls) R
                            )
                          return R
                          )
                        return R
                )
              return R
            mtrace on .zero with s!"[embedForwIncludeCore] IL : {← traceHelp IL}"
            let IG := merge2 (· == ·) IL gnodes gnodes'
            mtrace on .zero with s!"[embedForwIncludeCore] IG : {← traceHelp IG}"
            let IU := merge2 (· == ·) IG unodes unodes'
            mtrace on .zero with s!"[embedForwIncludeCore] IU : {← traceHelp IU}"
            let IB := merge2 (· == ·) IU bvars bvars'
            mtrace on .zero with s!"[embedForwIncludeCore] IB : {← traceHelp IB}"
            let IS ← merge3 IB sorts sorts' (fun u u' => do
              match ← defEqWiMv (.sort u) (.sort u') l1 l2 with
              | .none => return .none
              | .some (La,_) =>
                  let mut Ls := .nil
                  for (lid,la) in La do
                    match lid.name with
                    | .num _ p => Ls := .cons p la Ls
                    | _ => throwError s!"[embedForwIncludeCore] unsupporeted level mvar {repr lid}"
                  return .some (.nil,Ls)
              )
            mtrace on .zero with s!"[embedForwIncludeCore] IS : {← traceHelp IS}"
            let IC : ListProd3 IndexColType IndexColType ((ListProd Nat Expr) × (ListProd Nat Level)) := ← do
              (CTrie.intersect_val_pairs' consts consts').foldlM IS (fun cs cs' R => do
                merge3 R cs cs' (fun lv lv' => do
                  -- ugly but can't be bothered to get clean version
                  let mut Ls := .nil
                  for u in lv, u' in lv' do
                    match ← defEqWiMv (.sort u) (.sort u') l1 l2 with
                    | .none => return .none
                    | .some (La,_) =>
                        for (lid,la) in La do
                          match lid.name with
                          | .num _ p => Ls := .cons p la Ls
                          | _ => throwError s!"[embedForwIncludeCore] unsupporeted level mvar {repr lid}"
                  return .some (.nil,Ls)
                  ))
            mtrace on .zero with s!"[embedForwIncludeCore] IC : {← traceHelp IC}"
            let II := merge2 (· == ·) IC lits lits'
            mtrace on .zero with s!"[embedForwIncludeCore] II : {← traceHelp II}"
            let Iap := ← do if !(empty? api') then merge1 intersect empty? (compatible l1 l2) II (← go apf apf') (← go apa apa') else return II
            mtrace on .zero with s!"[embedForwIncludeCore] Iap : {← traceHelp Iap}"
            let Ila := ← do if !(empty? lai') then merge1 intersect empty? (compatible l1 l2) Iap (← go laf laf') (← go laa laa') else return Iap
            mtrace on .zero with s!"[embedForwIncludeCore] Ila : {← traceHelp Ila}"
            let Ial := ← do if !(empty? ali') then merge1 intersect empty? (compatible l1 l2) Ila (← go alf alf') (← go ala ala') else return Ila
            mtrace on .zero with s!"[embedForwIncludeCore] Ial : {← traceHelp Ial}"
            let Ile := ← do if !(empty? lei') then merge1 intersect empty? (compatible l1 l2) Ial (← merge1 intersect empty? (compatible l1 l2) .nil (← go lef lef') (← go lea lea')) (← go lez lez') else return Ial
            mtrace on .zero with s!"[embedForwIncludeCore] Ile : {← traceHelp Ile}"
            let IP : ListProd3 IndexColType IndexColType ((ListProd Nat Expr) × (ListProd Nat Level)) := ← do
              (CTrie.intersect_val_pairs' projs projs').foldlM Ile (fun cs cs' R => do
                cs.foldlM R (fun _ (i,p1) R => do
                  cs'.foldlM R (fun _ (j,p2) R => do
                    if i == j
                    then
                      let res ← go p1 p2
                      return res.foldl R (fun x y z w => .cons x y z w)
                    else
                      return R
                    )))
            mtrace on .zero with s!"[embedForwIncludeCore] IP : {← traceHelp IP}"
            -- ↓ is so that we assign lnodes inside proofs, in a way that matching IndexColTypes don't get duplicated
            let final ← merge4 intersect difference empty? (compatible l1 l2) IP (← go proofsOf proofsOf') (← go proofs proofs')
            mtrace on .zero with s!"[embedForwIncludeCore] final : {← traceHelp final}"
            return final
    go Q l

#check 1



@[specialize]
private def merge2' {α : Type _} (eq : α → α → Bool)
  (start : ListProd3 IndexColType IndexColType ((ListProd Nat Expr) × (ListProd Nat Level)))
  (L R : ListProd IndexColType α)
  : ListProd3 IndexColType IndexColType ((ListProd Nat Expr) × (ListProd Nat Level)) :=
  let rec @[specialize] go (done : ListProd3 IndexColType IndexColType ((ListProd Nat Expr) × (ListProd Nat Level)))
    : ListProd IndexColType α → ListProd3 IndexColType IndexColType ((ListProd Nat Expr) × (ListProd Nat Level))
    | .nil => done
    | .cons nx1 nx2 more =>
        match L.find? (fun _ y => eq y nx2) with
        | .none => go done more
        | .some x _ => go (.cons x nx1 (.nil, .nil) done) more
  go start R



@[specialize]
private def merge3' {α : Type _}
  (start : ListProd3 IndexColType IndexColType ((ListProd Nat Expr) × (ListProd Nat Level)))
  (L R : ListProd IndexColType α) (eq : α → α → MetaM (Option ((ListProd Nat Expr) × (ListProd Nat Level))))
  : MetaM <| ListProd3 IndexColType IndexColType ((ListProd Nat Expr) × (ListProd Nat Level)) :=
  let rec @[specialize] go (done : ListProd3 IndexColType IndexColType ((ListProd Nat Expr) × (ListProd Nat Level)))
    : ListProd IndexColType α → MetaM (ListProd3 IndexColType IndexColType ((ListProd Nat Expr) × (ListProd Nat Level)))
    | .nil => return done
    | .cons nx1 nx2 more =>
        L.foldlMcps done (fun x y D q => do
          match ← eq y nx2 with
          | .none => q D
          | .some (La,Ta) => q (.cons x nx1 (La,Ta) D)
          ) (fun ndone =>
            go ndone more)
  go start R



/-- Q is ltx, l is hyps with lnodes, in the sense Q ∩ l -/
@[specialize, inline]
partial def embedForwInterCore
  (thmData : CTrie (Array ThmFormat)) [Repr IndexColType]
  (intersect difference : IndexColType → IndexColType → IndexColType) (empty? : IndexColType → Bool)
  (l1 : LocalContext) (l2 : LocalInstances)
  (Q l : PaInG IndexColType)
  : MetaM <| ListProd3 IndexColType IndexColType ((ListProd Nat Expr) × (ListProd Nat Level)) :=
    let traceHelp (st : ListProd3 IndexColType IndexColType ((ListProd Nat Expr) × (ListProd Nat Level))) : MetaM String := do
      let pre ← st.foldlM ListProd3.nil (fun x y z R => return .cons x y (← z.1.foldlM ListProd.nil (fun x y R => return ListProd.cons x s!"{(← ppExpr y)}" R), z.2) R)
      return s!"{repr pre}"
    let rec @[specialize] go (Q l : PaInG IndexColType) : MetaM <| ListProd3 IndexColType IndexColType ((ListProd Nat Expr) × (ListProd Nat Level)) :=
      do -- trace set Tracing.Flags.none in do
      mtracing
      mtrace on .one with s!"[embedForwIncludeCore] Q : {← Q.pp l1 l2 [] 0 intersect empty?}"
      mtrace on .one with s!"[embedForwIncludeCore] l : {← l.pp l1 l2 [] 0 intersect empty?}"
      match Q, l with
      | _, .dead =>
          mtrace on .zero with s!"[embedForwIncludeCore] l is dead"
          return .nil
      | .dead, _=>
          mtrace on .zero with s!"[embedForwIncludeCore] Q is dead"
          return .nil
      | .br tnodes _ gnodes unodes bvars sorts consts lits apf apa api laf laa lai alf ala ali lef lea lez lei projs proofsOf proofs,
        -- **Debt** : unodes of Q should be built and merged with the current branch ; also, we don't expect unodes in l ...
        .br tnodes' lnodes' gnodes' unodes' bvars' sorts' consts' lits' apf' apa' api' laf' laa' lai' alf' ala' ali' lef' lea' lez' lei' projs' proofsOf' proofs' =>
            do
            let IT := merge2' (· == ·) .nil tnodes tnodes' -- we don't really expect any
            mtrace on .zero with s!"[embedForwIncludeCore] IT : {← traceHelp IT}"
            let IL : ListProd3 IndexColType IndexColType ((ListProd Nat Expr) × (ListProd Nat Level)) := ← do
              match lnodes' with
              | .leaf =>
                return IT
              | _ =>
                let QB ← Q.buildNoLoBvCore l1 l2 0 id intersect empty?
                let R ← lnodes'.foldM IT (fun nb D R => do
                  match thmData.find? nb with
                  | .none => return R
                  | .some moduleData =>
                      let R ← D.foldlM R (fun inds (thmIdx,pos) R => do
                        let thm := moduleData[thmIdx]!
                        thm.mctx.loadNoCo
                        let mv := Expr.mvar ⟨lnode (String.fromUTF8! nb).toName thmIdx pos⟩
                        let R ← QB.foldlM R (fun e qinds R => do
                          mtrace on .zero with s!"[embedForwIncludeCore] defeq e {← ppExpr e} vs lnode {repr mv} of type {← ppExpr <| ← inferType mv}"
                          match ← defEqWiMv mv e l1 l2 with
                          | .none =>
                              mtrace on .zero with s!"[embedForwIncludeCore] negative defeq"
                              return R
                          | .some (La,Ta) =>
                              mtrace on .zero with s!"[embedForwIncludeCore] positive defeq"
                              let mut Ls := .nil
                              for (lid,la) in La do
                                match lid.name with
                                | .num _ p => Ls := .cons p la Ls
                                | _ => throwError s!"[embedForwIncludeCore] unsupporeted level mvar {repr lid}"
                              let mut Ts := .nil
                              for (lid,la) in Ta do
                                match lid.name with
                                | .num _ p => Ts := .cons p la Ts
                                | _ => throwError s!"[embedForwIncludeCore] unsupporeted expr mvar {repr lid}"
                              return .cons qinds inds (Ts,Ls) R
                          )
                        return R
                        )
                      return R
                  )
                return R
            mtrace on .zero with s!"[embedForwIncludeCore] IL : {← traceHelp IL}"
            let IG := merge2' (· == ·) IL gnodes gnodes'
            mtrace on .zero with s!"[embedForwIncludeCore] IG : {← traceHelp IG}"
            let IU := merge2' (· == ·) IG unodes unodes'
            mtrace on .zero with s!"[embedForwIncludeCore] IU : {← traceHelp IU}"
            let IB := merge2' (· == ·) IU bvars bvars'
            mtrace on .zero with s!"[embedForwIncludeCore] IB : {← traceHelp IB}"
            let IS ← merge3' IB sorts sorts' (fun u u' => do
              match ← defEqWiMv (.sort u) (.sort u') l1 l2 with
              | .none => return .none
              | .some (La,_) =>
                  let mut Ls := .nil
                  for (lid,la) in La do
                    match lid.name with
                    | .num _ p => Ls := .cons p la Ls
                    | _ => throwError s!"[embedForwIncludeCore] unsupporeted level mvar {repr lid}"
                  return .some (.nil,Ls)
              )
            mtrace on .zero with s!"[embedForwIncludeCore] IS : {← traceHelp IS}"
            let IC : ListProd3 IndexColType IndexColType ((ListProd Nat Expr) × (ListProd Nat Level)) := ← do
              (CTrie.intersect_val_pairs' consts consts').foldlM IS (fun cs cs' R => do
                mtrace on .zero with s!"[embedForwIncludeCore] intersection\ncs: {cs.toListOfProd.map (fun (x,y) => (repr x, y))}\ncs': {cs'.toListOfProd.map (fun (x,y) => (repr x, y))}"
                merge3' R cs cs' (fun lv lv' => do
                  -- ugly but can't be bothered to get clean version
                  let mut Ls := .nil
                  for u in lv, u' in lv' do
                    mtrace on .zero with s!"[embedForwIncludeCore] defeqing u {u} vs u' {u'}"
                    match ← defEqWiMv (.sort u) (.sort u') l1 l2 with
                    | .none => return .none
                    | .some (La,_) =>
                        mtrace on .zero with s!"[embedForwIncludeCore] positive {La.toArray.map (fun (x,y) => (repr x, y))}"
                        for (lid,la) in La do
                          match lid.name with
                          | .num _ p => Ls := .cons p la Ls
                          | _ => throwError s!"[embedForwIncludeCore] unsupporeted level mvar {repr lid}"
                  return .some (.nil,Ls)
                  ))
            mtrace on .zero with s!"[embedForwIncludeCore] IC : {← traceHelp IC}"
            let II := merge2' (· == ·) IC lits lits'
            mtrace on .zero with s!"[embedForwIncludeCore] II : {← traceHelp II}"
            let Iap := ← merge1 intersect empty? (compatible l1 l2) II (← go apf apf') (← go apa apa')
            mtrace on .zero with s!"[embedForwIncludeCore] Iap : {← traceHelp Iap}"
            let Ila := ← merge1 intersect empty? (compatible l1 l2) Iap (← go laf laf') (← go laa laa')
            mtrace on .zero with s!"[embedForwIncludeCore] Ila : {← traceHelp Ila}"
            let Ial := ← merge1 intersect empty? (compatible l1 l2) Ila (← go alf alf') (← go ala ala')
            mtrace on .zero with s!"[embedForwIncludeCore] Ial : {← traceHelp Ial}"
            let Ile := ← merge1 intersect empty? (compatible l1 l2) Ial (← merge1 intersect empty? (compatible l1 l2) .nil (← go lef lef') (← go lea lea')) (← go lez lez')
            mtrace on .zero with s!"[embedForwIncludeCore] Ile : {← traceHelp Ile}"
            let IP : ListProd3 IndexColType IndexColType ((ListProd Nat Expr) × (ListProd Nat Level)) := ← do
              (CTrie.intersect_val_pairs' projs projs').foldlM Ile (fun cs cs' R => do
                cs.foldlM R (fun _ (i,p1) R => do
                  cs'.foldlM R (fun _ (j,p2) R => do
                    if i == j
                    then
                      let res ← go p1 p2
                      return res.foldl R (fun x y z w => .cons x y z w)
                    else
                      return R
                    )))
            mtrace on .zero with s!"[embedForwIncludeCore] IP : {← traceHelp IP}"
            -- ↓ is so that we assign lnodes inside proofs, in a way that matching IndexColTypes don't get duplicated
            let final ← merge4 intersect difference empty? (compatible l1 l2) IP (← go proofsOf proofsOf') (← go proofs proofs')
            mtrace on .zero with s!"[embedForwIncludeCore] final : {← traceHelp final}"
            return final
    go Q l

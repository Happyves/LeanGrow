

import LeanGrow.F.Prototypes.MarkFour.trTypes
import LeanGrow.F.Utils.Array
import LeanGrow.F.Data.CExpr.API

open Lean

/-
Backsteps should delete one goal, and possibly (probably) add new goals.
Unisteps should delete goals.
If there are no active goals, then we may assemble.
-/

/-- Won't be needed in final version, as we expct to add additional
gnodes as lets, but we'll still have to assemble them -/
partial def unfoldAddedGnodes (ltx_assemmbly : List (Nat × BackType × Array CExpr)) (e : CExpr) : CExpr :=
  let rec go (e : CExpr) : CExpr := -- add API for this =__=
    match e with
    | .app f a =>  (.app (go f) (go a))
    | .lam n f a i => .lam n (go f) (go a) i
    | .forallE n f a i => .forallE n (go f) (go a) i
    | .letE n f a z i => .letE n (go f) (go a) (go z) i
    | .proj n i f => .proj n i (go f)
    | .gnode i _ =>
        match ltx_assemmbly.find? (fun (id,_,_) => id == i) with
        | .some (_,n,emb) => go (CExpr.mkAppA (
            match n with -- fix universe !!
            | .ofThm N => .const N []
            | .ofLocal i => .gnode i (.ofBvar 42)
            ) emb)
        | .none => e
    | x => x
  go e


/-
Thoughts:

- maintain a list of pairs of solutions terms and a list of uni-ids they require

- unifications (uni-ids) clash if they assign non-equal values to the same lnode
  (given by a tag and position)

- For .ofGoal, recurse on the sols, and join the results. So if a goal isn't solved,
  the return should be empty

- For .ofBack, recurse on the args and make the cartesian product of results,
  which should then be pruned on unification-clashes. Then, form new terms that
  are applications of the back-thm to the elements of the catesian prod, and join
  the uni-ids corresponding to the product to be the new uni-ids list constraint.
  We want that when one of the args returns empty solutions, to return empt solutions

- For .ofAssign, we should postpone somehow ? Or not, just keep the lnodes. We should
  wait for the term to be fully assembled, at which stage we replace the lnodes by the
  values set by unifications (and fix levels ?)

- for .ofUni, we retrieve the value as term, and add the uni-id and the other data
  to the constraint context

- for .ofPropa, recurse on the sols, join the results, and (as opposed to .ofGoal)
  add the uni-id to each results constraint. Don't know if there can be unification
  clashes here, so do a clash check anyway ?

OR ... we can collect the information which lnodes gets fixed with which values durring
unification propagation. Then, we can tell in advance if unifications clash or not,
without working on the BackTree

-/


private def uniClash? (a b : List (Nat × Nat × CExpr)) : Bool :=
  let rec go : List (Nat × Nat × CExpr) → Bool
    | [] => false
    | (xt,xp,xv) :: xs =>
        match b.find? (fun y => y.1 == xt && y.2.1 == xp) with
        | .some (_,_,w) =>
            if xv == w then go xs else true
        | _ => go xs
  go a

private def uniClash?Big (knowClashes : List (Nat × Nat)) (unif_assign : List (Nat × (List (Nat × Nat × CExpr)))) (a b : List Nat) : Option (List (Nat × Nat)) :=
  let main (x y : Nat) : Option (Nat × Nat) :=
    let p := if x < y then (x,y) else (y,x)
    if knowClashes.contains p
    then .none
    else
      match unif_assign.find? (fun z => z.1 == x) with
      | .some (_,Ax) =>
          match unif_assign.find? (fun z => z.1 == y) with
          | .some (_,Bx) =>
              if uniClash? Ax Bx then .some p else .none
          | _ => .none
      | _ => .none
  let rec go : List Nat → List Nat → Option (List (Nat × Nat))
    | x :: xs, y :: ys =>
        match main x y with
        | .some p => .some (p :: knowClashes)
        | _ => go xs (y :: ys)
    | [], _ :: ys => go a ys
    | _,_ => .none
  go a b


private def candidMerge (knowClashes : List (Nat × Nat)) (unif_assign : List (Nat × (List (Nat × Nat × CExpr))))
  (n : BackType) (argNum : Nat) -- add levels !
  (todo : Array (List (CExpr × List Nat))) : List (CExpr × List Nat) × List (Nat × Nat) :=
  --dbg_trace "(candidMerge)"
  let rec go (knowClashes : List (Nat × Nat)) (sofar : List ((Array CExpr) × List Nat)) : Nat → (List ((Array CExpr) × List Nat) × List (Nat × Nat))
    | 0 => (sofar, knowClashes)
    | n+1 =>
        --dbg_trace s!"▸ Generation {repr sofar}"
        let choices := todo.get! n
        --dbg_trace s!"Choices {repr choices}"
        let (res,okC) := choices.foldl (fun (st,kC) (ce,constr) =>
          --dbg_trace s!"Choice contr {constr} and term {repr ce}"
          let (new,ikC) := sofar.foldl (fun (passed,nkC) (argsVals,innerConstr) =>
            --dbg_trace s!"Candidate {repr argsVals}"
            let relCons := constr.filter (fun x => !(innerConstr.contains x))
            --dbg_trace s!"relCons {repr relCons}"
            match uniClash?Big nkC unif_assign innerConstr relCons with
            | .none => --dbg_trace s!"pass !"
                ((argsVals.set! n ce, relCons ++ innerConstr) :: passed ,nkC)
            | .some NkC => --dbg_trace s!"no pass"
                (passed, NkC)
            ) ([],kC)
          (new :: st,ikC)
          ) ([], knowClashes)
        go okC res.join n
  let (pruned, nextKC) := go knowClashes [(Array.mkArray argNum .failed,[])] argNum
  --dbg_trace s!"(candidMerge) pruned : {repr pruned}"
  (pruned.map (fun (as,cs) => (CExpr.mkAppA ((
      match n with -- fix universe !!
      | .ofThm N => .const N []
      | .ofLocal i => .gnode i (.ofBvar 42)
      )) as, cs)) ,nextKC)


--#exit

def lamdifyGnode (gi : Nat) (e : CExpr) : CExpr :=
  let rec go (depth : Nat) : CExpr → CExpr
    | .app f a => .app (go depth f) (go depth a)
    | .lam n f a i => .lam n (go depth f) (go (depth+1) a) i
    | .forallE n f a i => .forallE n (go depth f) (go (depth+1) a) i
    | .letE n f a z i => .letE n (go depth f) (go depth a) (go (depth+1) z) i
    | .proj n i x => .proj n i (go depth x)
    | .gnode i o =>
        if i == gi
        then .bvar depth
        else .gnode i o
    | x => x
  go 0 e




-- partial def bizzare (unif_assign : List (Nat × (List (Nat × Nat × CExpr)))) (val : CExpr) : Bool :=
--   let rec go : List CExpr → Bool
--     | .app f a :: m =>  go (f :: a :: m)
--     | .lam n f a i :: m => go (f :: a :: m)
--     | .forallE n f a i :: m => go (f :: a :: m)
--     | .letE n f a z i :: m => go (f :: a :: z :: m)
--     | .proj n i f :: m => go (f :: m)
--     | .lnode i _ (.some t) :: m =>
--           if (unif_assign.find? (fun (_,L) => (L.find? (fun (T,P,_) => T == t && P == i)).isSome)).isSome
--           then go m
--           else false
--     | _ :: m => go m
--     | [] => true
--   go [val]

--#exit

partial def BackTree.assemble?
  (ltx_assemmbly : List (Nat × BackType × Array CExpr))
  (unif_assign : List (Nat × (List (Nat × Nat × CExpr))))
  (knowClashes : List (Nat × Nat))
  (bt : BackTree) : List (CExpr × List Nat) × List (Nat × Nat) :=
  dbg_trace "\n\n(assembly)\n"
  let rec go (knowClashes : List (Nat × Nat)) (addedConstr : List Nat) : BackTree → (List (CExpr × List Nat) × List (Nat × Nat))
    | .ofGoal i _ _ _ ts =>
      let res :=
      ts.foldl (fun (sols,kC) t =>
        let (msols,nkC) := go kC addedConstr t
        (msols ++ sols, nkC)
        ) ([],knowClashes)
        dbg_trace s!"Goal {i}, returning {repr res}"
      res
    | .ofBack i n _ _ ts =>
        let (_,candid,nkC) := ts.foldl (fun (i,sols,kC) t =>
          let (msols,nkC) := go kC addedConstr t
          (i+1, sols.set! i msols, nkC)
          ) (0,(Array.mkArray ts.size [] : Array (List (CExpr × List Nat))),knowClashes)
        let res := candidMerge nkC unif_assign n ts.size candid
        dbg_trace s!"Back {i}, returning {repr res}" ;
        res
    | .ofAssign val =>
        dbg_trace s!"Assing, returning {repr (unfoldAddedGnodes ltx_assemmbly val)}"
        -- if bizzare unif_assign val
        -- then
        ([(unfoldAddedGnodes ltx_assemmbly val,[])],[])
    | .ofUni id val =>
        dbg_trace s!"Uni {id}"
        match uniClash?Big knowClashes unif_assign [id] addedConstr with
        | .none =>
            dbg_trace s!"No clash, returning {repr (unfoldAddedGnodes ltx_assemmbly val)}"
            ([(unfoldAddedGnodes ltx_assemmbly val,[id])],[])
        | .some p =>
            dbg_trace s!"Clash {p}"
            ([], p ++ knowClashes)
    | .ofPropa uid _ _ _ _ sols =>
        dbg_trace s!"Propa {uid}"
        match uniClash?Big knowClashes unif_assign [uid] addedConstr with
        | .some p =>
            dbg_trace s!"Clash {p}"
            ([],p ++ knowClashes)
        | .none =>
            let newConstr := uid :: addedConstr
            let res :=
            sols.foldl (fun (sols,kC) t =>
              let (msols,nkC) := go kC newConstr t
              (msols ++ sols, nkC)
              ) ([],knowClashes)
            dbg_trace s!"No clash, retunring {repr res}"
            res
    | .ofIntro i _ bvs _ _ ts =>
        let (res, nkC) :=
        ts.foldl (fun (sols,kC) t =>
          let (msols,nkC) := go kC addedConstr t
          (msols ++ sols, nkC)
          ) ([],knowClashes)
          dbg_trace s!"Goal {i}, returning {repr res}"
        let R := res.map (fun (ce,cstr) =>
          let r := bvs.foldl (fun cex (gi,t) =>
            .lam `grow t (lamdifyGnode gi cex) .default
            ) ce
          (r,cstr))
        (R,nkC)
    | .fail => ([],[])
  go knowClashes [] bt

--#exit

def unfoldLNodes (unif_assign : List (Nat × (List (Nat × Nat × CExpr)))) -- add levels
  (unis : List Nat) (ce : CExpr) : CExpr :=
  --dbg_trace "unif_assign : {repr unif_assign}\n unis {unis}"
  let rec getVals (done : List (Nat × Nat × CExpr)) : List (Nat × (List (Nat × Nat × CExpr))) → List (Nat × Nat × CExpr)
    | [] => done
    | (id,x) :: xs => if unis.contains id then getVals (x ++ done) xs else getVals done xs
  let Vals := getVals [] unif_assign
  --dbg_trace "VALS : {repr Vals}"
  let rec go : CExpr → CExpr
    | .app f a =>  (.app (go f) (go a))
    | .lam n f a i => .lam n (go f) (go a) i
    | .forallE n f a i => .forallE n (go f) (go a) i
    | .letE n f a z i => .letE n (go f) (go a) z i
    | .proj n i f => .proj n i (go f)
    | .lnode pos _ (.some tag) =>
        match Vals.find? (fun (x,y,_) => x == tag && y == pos) with
        | .some (_,_,ce) =>  ce
        | _ => dbg_trace s!"SUS {pos} {tag}" ;  .failed
    | x => x
  go ce

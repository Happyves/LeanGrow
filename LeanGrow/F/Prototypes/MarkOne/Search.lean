
import LeanGrow.F.Search.A.trBack
import LeanGrow.F.Search.A.trSolve
import LeanGrow.F.Data.Unification.EmbedRawWInferWUnis
import LeanGrow.F.Data.Unification.EmbedGoalWInferWUnis
import LeanGrow.F.Search.ForwardData.Forward
import LeanGrow.F.Utils.Paging

#check 1

open Lean

structure miniPermiseDict where
  name : Name
  data : Array EmbedData
  order : Array Nat
  goal : CExpr
deriving Inhabited, Repr, BEq


structure SearchState where
  back : BackState
  forw : List (Nat × CExpr)
  forw2 : List (Array CExpr)
  ltx_handler : Nat → (Nat × Nat)
  forwID : Nat
  fctx : FixCtx
  ltx_assemmbly : List (Nat × Name × Array CExpr) -- add universe levels
deriving Inhabited--, Repr, BEq




def tryBackOn (fctx : FixCtx) (premises : List miniPermiseDict)
  (active_goal : CExpr) (active_goal_id : Nat) (state : BackState) : Option (BackState × FixCtx) :=
  let rec findBack : List miniPermiseDict → Option (miniPermiseDict × Array (Option CExpr))
    | [] => .none
    | p :: ps =>
        dbg_trace s!"Back Trying premise {p.name}"
        let res? := match_goal {fctx with current := p.data} p.data p.data.size p.goal active_goal
        match res? with
        | .some res => .some (p,res)
        | _ => findBack ps
  match findBack premises with
  | .none => .none
  | .some (prem,res) =>
      dbg_trace s!"Back candidate {repr (prem,res)}"
      let (assi,newg) := propagate_lnode_and_tag prem.data state.id_gen_back res
      .some (integrate_backstep_main prem.name prem.data.size active_goal_id assi newg state, {fctx with ltxTypes := (state.id_gen_back, prem.data) :: fctx.ltxTypes})

def tryBack (fctx : FixCtx) (premises : List miniPermiseDict) (state : BackState) : Option (BackState × FixCtx) :=
  let rec go : List (Nat × CExpr) → Option (BackState × FixCtx)
    | [] => .none
    | (id,g) :: more =>
        match tryBackOn fctx premises g id state with
        | .some new => .some new
        | _ => go more
  go state.active_goals



def tryForWith (fctx : FixCtx) (prem : miniPermiseDict) (state : SearchState) : Option SearchState :=
  match full_matcher_rawF {fctx with current := .some prem.data} prem.data prem.order state.forw with
  | [] => .none
  | opts =>
      let rez := (opts.map (fun x => (integrate_forward_raw x prem.goal, (prem.name, x.embed.reduceOption)))).filter (fun x => (state.forw.find? (fun y => y.2 == x.1)).isNone)
      let sz := rez.length
      let add_to_forw := List.zip ((List.range sz).map (· + state.forwID)) (rez.map Prod.fst)
      let add_to_asm := List.zip ((List.range sz).map (· + state.forwID)) (rez.map Prod.snd)
      let newforw := add_to_forw ++ state.forw
      let newforw2 := add_to_forw.foldl
        (fun sofar (idx,exp) => PageingSet sofar state.ltx_handler 42 (.failed) idx exp)
        state.forw2
      .some {state with forw := newforw, forw2 := newforw2, forwID := state.forwID + sz, ltx_assemmbly := add_to_asm ++ state.ltx_assemmbly}

def tryFor (fctx : FixCtx) (prems : List miniPermiseDict) (state : SearchState) : Option SearchState :=
  let rec go : List miniPermiseDict → Option SearchState
    | [] => .none
    | x :: xs =>
        match tryForWith fctx x state with
        | .some s => .some s
        | _ => go xs
  go prems


def TryStep (prems : List miniPermiseDict) (state : SearchState) : Option SearchState :=
  dbg_trace s!"trying back"
  match tryBack state.fctx prems state.back with
  | .some (newback, newfctx) =>
      dbg_trace s!"new back {repr newback}\nTry forw"
      match tryFor newfctx prems state with
      | .some st => dbg_trace s!"new forw {repr st.forw}" ; .some {st with back := newback, fctx := newfctx}
      | _ => .some {state with back := newback, fctx := newfctx}
  | _ =>
    dbg_trace s!"No back, try forw"
    match tryFor state.fctx prems state with
      | .some st => dbg_trace "new forw {repr st.forw}" ; .some st
      | _ => .none




partial def search_step (premises : List miniPermiseDict) (st : SearchState) : Option SearchState :=
  dbg_trace s!"Search step back {repr st.back}"
  let rec uni_ltx_activeGoals  (s g : List (Nat × CExpr)) : Option (Nat × Nat × List (Nat × Nat × CExpr)) :=
    -- try to find one unification of ltx result and an active goal
    match s, g with
    | x :: xs, y :: _ =>
        dbg_trace s!"looking at {repr x.2} and {repr y.2}"
        let xT := CExpr.whnf st.fctx (CExpr.inferType st.fctx x.2)
        if xT == .sort .zero
        then
          match (CExpr.MatchAssignSolutions' x.2 y.2) with
          | .some (res,_) => .some (x.1,y.1,res)
          | .none => uni_ltx_activeGoals xs g
        else
          uni_ltx_activeGoals xs g
    | [], _ :: ys => uni_ltx_activeGoals st.forw ys
    | _,_ => .none

  match uni_ltx_activeGoals st.forw st.back.active_goals with
  | .some (sol,gol,uni_res) =>
      dbg_trace s!"foudn uni {repr uni_res}"
      let uni_tree := BackTree.modifyAtGoalId gol (fun _ => .ofAssign (.gnode sol (.ofBvar 42))) st.back.bt
      match integrate_uni? st.forw2 st.ltx_handler uni_res uni_tree with
      | .some (nbt, updt, slved) =>
         let nb := integrate_uni_full st.back nbt updt (gol :: slved)
         .some {st with back := nb}
      | _ =>
        dbg_trace "unification didn't propagate, proceeding"
        TryStep premises st
  | _ =>
    dbg_trace "no unification of goals and ltx, proceeding"
    TryStep premises st


partial def search (fuel : Nat ) (premises : List miniPermiseDict) (st : SearchState) : Option SearchState :=
  dbg_trace s!"fuel {fuel}"
  if fuel == 0 || st.back.active_goals.isEmpty
  then .some st
  else
    match search_step premises st with
    | .some more => search (fuel - 1) premises more
    | _ => .none


/-
State of things:
- Unification integration seems to not assign goals, so that we loop
  on performing the same unification over and over again ...
-/

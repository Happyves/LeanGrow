
import LeanGrow.F.Prototypes.MarkTwo.trBack
import LeanGrow.F.Prototypes.MarkTwo.trSolve
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
  fctx : FixCtx -- it would be better to seperate the gnode info and lnode info
                -- so that we can do forward and backward steps independently of backsteps
  ltx_assemmbly : List (Nat × Name × Array CExpr) -- add universe levels
deriving Inhabited--, Repr, BEq

instance : BEq SearchState where
  beq := fun a b => (a.back == b.back) && (a.forw == b.forw)



def tryBackOn (fctx : FixCtx) (premises : List miniPermiseDict)
  (active_goal : CExpr) (active_goal_id : Nat) (state : BackState) : List (BackState × FixCtx) :=
  let rec findBack
  (done : List (miniPermiseDict × Array (Option CExpr) × List (Name × Level)))
  : List miniPermiseDict → List (miniPermiseDict × Array (Option CExpr) × List (Name × Level))
    | [] => done
    | p :: ps =>
        let res? := match_goal {fctx with current := p.data} p.data p.data.size p.goal active_goal
        match res? with
        | .some (res,us) => findBack ((p,res,us) :: done) ps
        | _ => findBack done ps
  let done := findBack [] premises
  done.map (fun (prem,res,us) =>
      let (assi,newg) := propagate_lnode_and_tag prem.data state.id_gen_back res us
      (integrate_backstep_main prem.name prem.data.size active_goal_id assi newg state, {fctx with ltxTypes := (state.id_gen_back, prem.data) :: fctx.ltxTypes})
    )

def tryBackAll (fctx : FixCtx) (premises : List miniPermiseDict) (state : BackState) : List (BackState × FixCtx) :=
  (state.active_goals.map (fun (id,g) => tryBackOn fctx premises g id state)).join



partial def tryUniAll (st : SearchState) : List SearchState :=
  let rec uni_ltx_activeGoals
    (done : List (Nat × Nat × List (Nat × Nat × CExpr) × List (Name × Level)))
    (s g : List (Nat × CExpr)) : List (Nat × Nat × List (Nat × Nat × CExpr) × List (Name × Level)) :=
    -- try to find one unification of ltx result and an active goal
    match s, g with
    | x :: xs, y :: _ =>
        let xT := CExpr.whnf st.fctx (CExpr.inferType st.fctx x.2)
        if xT == .sort .zero
        then
          match (CExpr.MatchAssignSolutions' x.2 y.2) with
          | .some (res,us) => uni_ltx_activeGoals ((x.1,y.1,res,us) :: done) xs g
          | .none => uni_ltx_activeGoals done xs g
        else
          uni_ltx_activeGoals done xs g
    | [], _ :: ys => uni_ltx_activeGoals done st.forw ys
    | _,_ => done
  let candidates := uni_ltx_activeGoals [] st.forw st.back.active_goals
  let interated := (candidates.map (fun (sol,gol,uni_res,us) =>
    let uni_tree := BackTree.modifyAtGoalId gol (fun _ => .ofAssign (.gnode sol (.ofBvar 42))) st.back.bt
    match integrate_uni? st.forw2 st.ltx_handler uni_res us uni_tree with
    | .some (nbt, updt, slved) =>
        let nb := integrate_uni_full st.back nbt updt us (gol :: slved)
        Option.some {st with back := nb}
    | _ => .none
    )).reduceOption
  interated


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

def tryFor (prems : List miniPermiseDict) (state : SearchState) : Option SearchState :=
  let rec go : List miniPermiseDict → Option SearchState
    | [] => .none
    | x :: xs =>
        match tryForWith state.fctx x state with
        | .some s => .some s
        | _ => go xs
  go prems





partial def search_step (premises : List miniPermiseDict) (st : SearchState) (old_gen : List SearchState) : List SearchState :=
  let unistep := (tryUniAll st).filter (fun x => !(old_gen.contains x))
  let unistep := if unistep.isEmpty then [st] else unistep
  let forwstep := (unistep.map (fun x =>  match tryFor premises x with | .some new => new | _ => x)).filter (fun x => !(old_gen.contains x))
  ((forwstep.map (fun st => (tryBackAll st.fctx premises st.back).map (fun (xb,xf) => {st with back := xb, fctx := xf}))).join).filter (fun x => !(old_gen.contains x))



partial def search (fuel : Nat) (premises : List miniPermiseDict) (st : SearchState) : Option SearchState :=
  let rec loop : Nat → List SearchState → Option SearchState
    | 0, _  | _ ,[] => .none
    | n+1, nx :: more =>
      dbg_trace s!"Fuel {n+1}\nBack:\n{repr nx.back}\nForw:\n{repr nx.forw}\n\n"
      if nx.back.active_goals.isEmpty
      then
        dbg_trace s!"Success!\nBack:\n{repr nx.back}\nForw:\n{repr nx.forw}\n\n"
        .some nx
      else
        let go := search_step premises nx more
        dbg_trace s!"Added {go.length} states\n\n"
        loop n (more ++ go)
  loop fuel [st]

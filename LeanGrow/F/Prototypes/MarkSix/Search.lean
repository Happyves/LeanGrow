
import LeanGrow.F.Prototypes.MarkSix.trBack
import LeanGrow.F.Prototypes.MarkSix.trSolve
import LeanGrow.F.Data.Unification.EmbedGoalWInferWUnis
import LeanGrow.F.Prototypes.MarkSix.Forward
import LeanGrow.F.Prototypes.MarkSix.IntroTreeEmbed

#check 1

open Lean

structure miniPermiseDict where
  name : BackType
  data : Array EmbedData
  order : Array Nat
  goal : CExpr
deriving Inhabited, Repr, BEq


structure SearchState where
  back : BackState
  forw : IntroTree
  forw2 : List (Array CExpr)
  ltx_handler : Nat → (Nat × Nat)
  forwID : Nat
  fctx : FixCtx -- it would be better to seperate the gnode info and lnode info
                -- so that we can do forward and backward steps independently of backsteps
  ltx_assemmbly : List (Nat × BackType × Array CExpr) -- add universe levels
  unif_assign : List (Nat × (List (Nat × Nat × CExpr) × List (Name × Level))) -- (uni_id, params assignements)
  back_memo : List (Nat × List BackType)
  uni_memo : List (Nat × Nat)
  uni_claches : List (Nat × Nat)
deriving Inhabited--, Repr, BEq

instance : BEq SearchState where
  beq := fun a b => (a.back == b.back) && (a.forw == b.forw)



def tryBackOn (fctx : FixCtx) (premises : List miniPermiseDict)
  (back_memo : List BackType) (forwID : Nat)
  (gnodeTypes : List (Array CExpr)) (gnodeTypesHandler : Nat → (Nat × Nat))
  (active_goal : CExpr) (active_goal_id : Nat) (state : BackState) : Option (Nat × List (Nat × CExpr) × BackState × FixCtx × BackType) :=
  let rec findBack : List miniPermiseDict → Option (miniPermiseDict × Array (Option CExpr) × List (Name × Level))
    | [] => .none
    | p :: ps =>
        --dbg_trace s!"(findBack) prem res {repr p}"
        if back_memo.contains p.name
        then findBack ps
        else
          --dbg_trace s!"Trying to match :\n{repr p.goal}\n{repr active_goal}\n\n"
          let res? := match_goal {fctx with current := p.data} p.data p.data.size p.goal active_goal
          match res? with
          | .some (res,us) => .some (p,res,us)
          | _ => findBack ps
  match findBack premises with
  | .none => .none
  | .some (prem,res,us) =>
      --dbg_trace s!"(tryBackOn) prem res {repr (prem,res)}"
      let (assi,newg) := propagate_lnode_and_tag prem.data state.id_gen_back res us
      --dbg_trace s!"(tryBackOn) assi newg {repr assi} {repr newg}"
      let (new_forwID, introGnodes, nbs) := integrate_backstep_main fctx forwID prem.name prem.data.size active_goal_id assi newg state
      --dbg_trace s!"(tryBackOn) after integ {repr nbs.active_goals}"
      let newforw2 := introGnodes.foldl
        (fun sofar (idx,exp) => PageingSet sofar gnodeTypesHandler 42 (CExpr.failed) idx exp)
        gnodeTypes
      .some (new_forwID, introGnodes, nbs, {fctx with gnodeTypes := newforw2, ltxTypes := (state.id_gen_back, prem.data) :: fctx.ltxTypes},prem.name)


def updateLtxIntros (forw : IntroTree)
  (forw2 : List (Array CExpr)) (ltx_handler : Nat → (Nat × Nat))
  (target_id : Nat) (newGs : List Nat) (toAdd : List (Nat × CExpr)) :
  IntroTree × List (Array CExpr) :=
  match toAdd with
  | [] => (forw.addStdBack target_id newGs, forw2)
  | _ =>
    let nf := forw.addIntroBack target_id newGs toAdd
    let nf2 := toAdd.foldl (fun sofar (zn,ze) => PageingSet sofar ltx_handler 42 .failed zn ze) forw2
    (nf,nf2)


def tryBack (premises : List miniPermiseDict) (st : SearchState) : Option (SearchState) :=
  let rec go : List (Nat × CExpr) → Option (SearchState)
    | [] => .none
    | (id,g) :: more =>
        --dbg_trace s!"tryBack on {id}"
        match st.back_memo.find? (fun x => x.1 == id) with
        | .some (_,nms) =>
            match tryBackOn st.fctx premises nms st.forwID st.fctx.gnodeTypes st.fctx.gnodeTypesHandler g id st.back with
            | .some (newfid,ngno,newb,newf,add) =>
              let newGs := (List.range (newb.id_gen_goal - st.back.id_gen_goal)).map (· + st.back.id_gen_goal)
              let (nf,nf2) := updateLtxIntros st.forw st.forw2 st.ltx_handler id newGs ngno -- already incremented in newb
              .some {st with forw := nf, forw2 := nf2, forwID := newfid, back := newb, fctx := newf, back_memo := st.back_memo.findModifyAdd (fun x => x.1 == id) (fun (n,l) => (n, ( add) :: l)) (id,[(add)])}
            | _ => go more
        | _ =>
          match tryBackOn st.fctx premises [] st.forwID st.fctx.gnodeTypes st.fctx.gnodeTypesHandler g id st.back with
          | .some (newfid,ngno,newb,newf,add) =>
              let newGs := (List.range (newb.id_gen_goal - st.back.id_gen_goal)).map (· + st.back.id_gen_goal)
              let (nf,nf2) := updateLtxIntros st.forw st.forw2 st.ltx_handler id newGs ngno -- already incremented in newb
              .some {st with forw := nf, forw2 := nf2, forwID := newfid, back := newb, fctx := newf, back_memo := st.back_memo.findModifyAdd (fun x => x.1 == id) (fun (n,l) => (n, add :: l)) (id,[add])}
          | _ => go more
  go st.back.active_goals


def tryForWith (fctx : FixCtx) (prem : miniPermiseDict) (state : SearchState) : Option SearchState :=
  match full_matcher_rawF {fctx with current := .some prem.data} prem.data prem.order state.forw with
  | [] => .none
  | opts =>
      let preRez := opts.map (fun x => ((integrate_forward_raw x prem.goal, x.topGoals), prem.name, x.embed.reduceOption))
      let rez := (preRez.map (fun ((ce,l),b,a) =>
        let vers := [ce] --(cexprReduceShallow fctx 2 ce) -- massive debt from Mark5
          -- here we don't filter, else we loose the un-reduce version
        vers.map (fun x => ((x,l),b,a))
        )).join.filter (fun x => !(state.forw.has? x.1.1))
      let sz := rez.length
      let add_to_forw := List.zip ((List.range sz).map (· + state.forwID)) (rez.map Prod.fst)
      let add_to_asm := (List.zip ((List.range sz).map (· + state.forwID)) (rez.map Prod.snd))--.foldl
        --(fun L (a,b,c) => match b with | .ofThm N => (a,N,c) :: L | _ => L) []
      let newforw := state.forw.addForws add_to_forw
      let newforw2 := add_to_forw.foldl
        (fun sofar (idx,exp,_) => PageingSet sofar state.ltx_handler 42 (.failed) idx exp)
        state.forw2
      let clueless := add_to_forw.foldl
        (fun sofar (idx,exp,_) => PageingSet sofar state.fctx.gnodeTypesHandler 42 (.failed) idx exp)
        state.fctx.gnodeTypes
      .some {state with fctx := {state.fctx with gnodeTypes := clueless}, forw := newforw, forw2 := newforw2, forwID := state.forwID + sz, ltx_assemmbly := add_to_asm ++ state.ltx_assemmbly}


def tryFor (prems : List miniPermiseDict) (state : SearchState) : Option SearchState :=
  let rec go : List miniPermiseDict → Option SearchState
    | [] => .none
    | x :: xs =>
        match tryForWith state.fctx x state with
        | .some s => .some s
        | _ => go xs
  go prems


--#exit

partial def tryUniAll (st : SearchState) : SearchState :=
  let rec main (tars : List Nat) (ltx: List (Nat × CExpr))
    (done : List (Nat × Nat × List (Nat × Nat × CExpr) × List (Name × Level)))
    (s g : List (Nat × CExpr)) :
    List (Nat × Nat × List (Nat × Nat × CExpr) × List (Name × Level)) :=
    match s, g with
    | x :: xs, y :: ys =>
        if tars.contains y.1
        -- think about storing active goals in a way that we can match them with
        -- the coresponding ltx more efficiently
        then
          if st.uni_memo.contains (x.1,y.1)
          -- actually, we should add the pair if it doesn't match, so that we dont try again
          then main tars ltx done xs g
          else
            let xT := CExpr.whnf st.fctx (CExpr.inferType st.fctx x.2)
            if xT == .sort .zero
            -- should definitely store this info instead of recomputing every time
            then
              if x.1 == 4 && y.1 == 8
              then
                match (CExpr.MatchAssignSolutions' x.2 y.2) with
                | .some (res,us) =>
                      --dbg_trace s!"HMMM yes"
                      main tars ltx ((x.1,y.1,res,us) :: done) xs g
                | .none =>
                      --dbg_trace s!"HMMM no"
                      main tars ltx done xs g
              else
                match (CExpr.MatchAssignSolutions' x.2 y.2) with
                | .some (res,us) => main tars ltx ((x.1,y.1,res,us) :: done) xs g
                | .none => main tars ltx done xs g
            else main tars ltx done xs g
          else main tars ltx done s ys
    | [], _ :: ys => main tars ltx done ltx ys
    | _,_ => done
  let rec uni_ltx_activeGoals
    (done : List (Nat × Nat × List (Nat × Nat × CExpr) × List (Name × Level)))
    (g : List (Nat × CExpr)) : List IntroTree →
    List (Nat × Nat × List (Nat × Nat × CExpr) × List (Name × Level))
      | [] => done
      | nx :: more =>
        match nx with
        | .leaf gids ltx =>
          let next := main gids ltx [] ltx g
          uni_ltx_activeGoals (next ++ done) g more
        | .node gids ltx kwd =>
          let next := main gids ltx [] ltx g
          uni_ltx_activeGoals (next ++ done) g ((kwd.map Prod.snd) ++ more)
  --dbg_trace s!"\n\n(tryUniAll) init tree : {repr st.back.bt}\n"
  let candidates := uni_ltx_activeGoals [] st.back.active_goals [st.forw]
  --dbg_trace s!"(tryUniAll) candidates : {repr candidates}\n"
  let interated := (candidates.foldl (fun S (sol,gol,uni_res,us) =>
    let uni_tree := BackTree.modifyAtGoalId gol (fun
      | .ofGoal j t bdirs gdirs ts => .ofGoal j t bdirs gdirs ((.ofUni st.back.id_gen_assign (.gnode sol (.ofBvar 42))) :: ts)
      | .ofPropa i j t bdirs gdirs ts => .ofPropa i j t bdirs gdirs ((.ofUni st.back.id_gen_assign (.gnode sol (.ofBvar 42))) :: ts)
      | .ofIntro i j t bdirs gdirs ts => .ofIntro i j t bdirs gdirs ((.ofUni st.back.id_gen_assign (.gnode sol (.ofBvar 42))) :: ts)
      | x => x) st.back.bt
    --dbg_trace s!"(tryUniAll) uni_tree : {repr uni_tree}\n"
    match integrate_uni? st.forwID st.back.id_gen_assign st.back.id_gen_goal (us.map Prod.fst) (us.map Prod.snd) st.fctx uni_res uni_tree with
    | .some (uni_assi, nfid, nfwdI, nbt, ngs, ngi) =>
        --dbg_trace s!"(tryUniAll) integrate_uni? output : {repr (uni_assi, nfid, nfwdI, nbt, ngs, ngi) }\n"
        let (nF,nF2) := nfwdI.foldl (fun (IF,IF2) (tgId,nltx) =>
          updateLtxIntros IF IF2 st.ltx_handler tgId [gol] nltx) (st.forw, st.forw2)
        let nb := integrate_uni_full st.back nbt ngs ngi gol
        --dbg_trace s!"(tryUniAll) integrate_uni_full output : {repr nb}\n"
        --dbg_trace s!"(tryUniAll) unif_assign output : {repr (st.back.id_gen_assign, uni_assi, us)}\n"
        let clueless := (nfwdI.map Prod.snd).join.foldl
          (fun sofar (idx,exp) => PageingSet sofar st.fctx.gnodeTypesHandler 42 (.failed) idx exp)
          st.fctx.gnodeTypes
        {st with fctx := {st.fctx with gnodeTypes := clueless} ,forwID := nfid, forw := nF, forw2 := nF2, back := nb, unif_assign := (st.back.id_gen_assign, uni_assi, us) :: st.unif_assign, uni_memo := (sol,gol) :: st.uni_memo}
    | _ => S
    )) st
  interated




--#exit





partial def search_step (premises : List miniPermiseDict) (st : SearchState) : SearchState :=
  let unistep := tryUniAll st
  --dbg_trace s!"(unistep)\nBacktree:\n{repr unistep.back.bt}\nGoals:\n{repr unistep.back.active_goals}\nForward:{repr unistep.forw}\nBack memo:\n{unistep.back_memo}\nUni memo:\n{unistep.uni_memo}\nUni clashes:\n{unistep.uni_claches}\n\n"
  let forwstep := match tryFor premises unistep with | .some new => new | _ => unistep
  --dbg_trace s!"(forward)\nBacktree:\n{repr forwstep.back.bt}\nGoals:\n{repr forwstep.back.active_goals}\nForward:{repr forwstep.forw}\nBack memo:\n{forwstep.back_memo}\nUni memo:\n{forwstep.uni_memo}\nUni clashes:\n{forwstep.uni_claches}\n\n"
  match tryBack premises forwstep with
  | .some res => res
  | _ => forwstep


partial def search (fuel : Nat) (premises : List miniPermiseDict) (st : SearchState) : Option CExpr :=
  let rec loop : Nat → SearchState → Option CExpr
    | 0, _ => .none
    | n+1, nx =>
      let st := search_step premises nx
      dbg_trace s!"(search) loop {n+1}\nBacktree:\n{repr st.back.bt}\nGoals:\n{repr st.back.active_goals}\nForward:{repr st.forw}\nBack memo:\n{repr st.back_memo}\nUni memo:\n{st.uni_memo}\nUni clashes:\n{st.uni_claches}\n\n"
      let tmp := (st.unif_assign.map (fun (a,b,_) => (a,b)))
      --dbg_trace s!"(search) loop {n+1}\nUNI {repr tmp}\n\n"
      let (sols?,kC) := BackTree.assemble?
        st.ltx_assemmbly tmp
        st.uni_claches st.back.bt
      let sols! := sols?.filter (fun x => !x.2.isEmpty)
      match sols! with
      | [] => loop n {st with uni_claches := kC}
      | (tada, ah?) :: _ => .some (unfoldLNodes tmp ah? tada)
  dbg_trace s!"(search) loop init\nBacktree:\n{repr st.back.bt}\nGoals:\n{repr st.back.active_goals}\nForward:{repr st.forw}\nBack memo:\n{repr st.back_memo}\nUni memo:\n{st.uni_memo}\nUni clashes:\n{st.uni_claches}\n\n"
  loop fuel st


/-
Todo:
- check for unification clashes durring unification step, not assembly ?

-/

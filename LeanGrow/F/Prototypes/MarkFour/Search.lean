
import LeanGrow.F.Prototypes.MarkFour.trBack
import LeanGrow.F.Prototypes.MarkFour.trSolve
import LeanGrow.F.Data.Unification.EmbedRawWInferWUnis
import LeanGrow.F.Data.Unification.EmbedGoalWInferWUnis
import LeanGrow.F.Search.ForwardData.Forward
import LeanGrow.F.Utils.Paging
import LeanGrow.F.Prototypes.MarkFour.IntroTree

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
  forw : IntroTree
  forw2 : List (Array CExpr)
  ltx_handler : Nat → (Nat × Nat)
  forwID : Nat
  fctx : FixCtx -- it would be better to seperate the gnode info and lnode info
                -- so that we can do forward and backward steps independently of backsteps
  ltx_assemmbly : List (Nat × Name × Array CExpr) -- add universe levels
  unif_assign : List (Nat × (List (Nat × Nat × CExpr) × List (Name × Level))) -- (uni_id, params assignements)
  back_memo : List (Nat × List Name)
  uni_memo : List (Nat × Nat)
  uni_claches : List (Nat × Nat)
deriving Inhabited--, Repr, BEq

instance : BEq SearchState where
  beq := fun a b => (a.back == b.back) && (a.forw == b.forw)



def tryBackOn (fctx : FixCtx) (premises : List miniPermiseDict)
  (back_memo : List Name) (forwID : Nat)
  (gnodeTypes : List (Array CExpr)) (gnodeTypesHandler : Nat → (Nat × Nat))
  (active_goal : CExpr) (active_goal_id : Nat) (state : BackState) : Option (Nat × List (Nat × CExpr) × BackState × FixCtx × Name) :=
  let rec findBack : List miniPermiseDict → Option (miniPermiseDict × Array (Option CExpr) × List (Name × Level))
    | [] => .none
    | p :: ps =>
        if back_memo.contains p.name
        then findBack ps
        else
          let res? := match_goal {fctx with current := p.data} p.data p.data.size p.goal active_goal
          match res? with
          | .some (res,us) => .some (p,res,us)
          | _ => findBack ps
  match findBack premises with
  | .none => .none
  | .some (prem,res,us) =>
      -- dbg_trace s!"(tryBackOn) prem res {repr (prem,res)}"
      let (assi,newg) := propagate_lnode_and_tag prem.data state.id_gen_back res us
      --dbg_trace s!"(tryBackOn) assi newg {repr assi} {repr newg}"
      let (new_forwID, introGnodes, nbs) := integrate_backstep_main forwID prem.name prem.data.size active_goal_id assi newg state
      -- dbg_trace s!"(tryBackOn) after integ {repr nbs.active_goals}"
      let newforw2 := introGnodes.foldl
        (fun sofar (idx,exp) => PageingSet sofar gnodeTypesHandler 42 (CExpr.failed) idx exp)
        gnodeTypes
      .some (new_forwID, introGnodes, nbs, {fctx with gnodeTypes := newforw2, ltxTypes := (state.id_gen_back, prem.data) :: fctx.ltxTypes},prem.name)


def updateLtxIntros (forw : IntroTree)
  (forw2 : List (Array CExpr)) (ltx_handler : Nat → (Nat × Nat))
  (target_id id_gen_back : Nat) (toAdd : List (Nat × CExpr)) :
  IntroTree × List (Array CExpr) :=
  match toAdd with
  | [] => (forw.addStdBack target_id id_gen_back, forw2)
  | _ =>
    let nf := forw.addIntroBack target_id id_gen_back toAdd
    let nf2 := toAdd.foldl (fun sofar (zn,ze) => PageingSet sofar ltx_handler 42 .failed zn ze) forw2
    (nf,nf2)


def tryBack (premises : List miniPermiseDict) (st : SearchState) : Option (SearchState) :=
  let rec go : List (Nat × CExpr) → Option (SearchState)
    | [] => .none
    | (id,g) :: more =>
        match st.back_memo.find? (fun x => x.1 == id) with
        | .some (_,nms) =>
            match tryBackOn st.fctx premises nms st.forwID st.fctx.gnodeTypes st.fctx.gnodeTypesHandler g id st.back with
            | .some (newfid,ngno,newb,newf,add) =>
              let (nf,nf2) := updateLtxIntros st.forw st.forw2 st.ltx_handler id st.back.id_gen_back ngno -- already incremented in newb
              .some {st with forw := nf, forw2 := nf2, forwID := newfid, back := newb, fctx := newf, back_memo := st.back_memo.findModify (fun x => x.1 == id) (fun (n,l) => (n, add :: l))}
            | _ => go more
        | _ =>
          match tryBackOn st.fctx premises [] st.forwID st.fctx.gnodeTypes st.fctx.gnodeTypesHandler g id st.back with
          | .some (newfid,ngno,newb,newf,add) =>
              let (nf,nf2) := updateLtxIntros st.forw st.forw2 st.ltx_handler id st.back.id_gen_back ngno -- already incremented in newb
              .some {st with forw := nf, forw2 := nf2, forwID := newfid, back := newb, fctx := newf, back_memo := st.back_memo.findModify (fun x => x.1 == id) (fun (n,l) => (n, add :: l))}
          | _ => go more
  go st.back.active_goals


def tryForWith (fctx : FixCtx) (prem : miniPermiseDict) (state : SearchState) : Option SearchState :=
  match full_matcher_rawF {fctx with current := .some prem.data} prem.data prem.order state.forw with
  | [] => .none
  | opts =>
      let rez := (opts.map (fun x => (integrate_forward_raw x prem.goal, (prem.name, x.embed.reduceOption)))).filter (fun x => (state.forw.find? (fun y => y.2 == x.1)).isNone)
      --dbg_trace s!"\n(DEBUG) Forw, opts : {repr (opts.map (EmbedStruct.embed))}\n"
      let sz := rez.length
      let add_to_forw := List.zip ((List.range sz).map (· + state.forwID)) (rez.map Prod.fst)
      let add_to_asm := List.zip ((List.range sz).map (· + state.forwID)) (rez.map Prod.snd)
      let newforw := add_to_forw ++ state.forw
      let newforw2 := add_to_forw.foldl
        (fun sofar (idx,exp) => PageingSet sofar state.ltx_handler 42 (.failed) idx exp)
        state.forw2
      .some {state with forw := newforw, forw2 := newforw2, forwID := state.forwID + sz, ltx_assemmbly := add_to_asm ++ state.ltx_assemmbly}
      -- potiential bug: newforw2 should also be added to FixCtx !!!


#exit

def tryFor (prems : List miniPermiseDict) (state : SearchState) : Option SearchState :=
  let rec go : List miniPermiseDict → Option SearchState
    | [] => .none
    | x :: xs =>
        match tryForWith state.fctx x state with
        | .some s => .some s
        | _ => go xs
  go prems


#exit

partial def tryUniAll (st : SearchState) : SearchState :=
  let rec uni_ltx_activeGoals
    (done : List (Nat × Nat × List (Nat × Nat × CExpr) × List (Name × Level)))
    (s g : List (Nat × CExpr)) : List (Nat × Nat × List (Nat × Nat × CExpr) × List (Name × Level)) :=
    -- try to find all (new) unifications of ltx result and an active goal
    match s, g with
    | x :: xs, y :: _ =>
        if st.uni_memo.contains (x.1,y.1)
        then uni_ltx_activeGoals done xs g
        else
          let xT := CExpr.whnf st.fctx (CExpr.inferType st.fctx x.2)
          if xT == .sort .zero
          then
            match (CExpr.MatchAssignSolutions' x.2 y.2) with
            | .some (res,us) => uni_ltx_activeGoals ((x.1,y.1,res,us) :: done) xs g
            | .none => uni_ltx_activeGoals done xs g
          else uni_ltx_activeGoals done xs g
    | [], _ :: ys => uni_ltx_activeGoals done st.forw ys
    | _,_ => done
  let candidates := uni_ltx_activeGoals [] st.forw st.back.active_goals
  --dbg_trace s!"(tryUniAll) candidates {repr candidates}"
  let interated := (candidates.foldl (fun S (sol,gol,uni_res,us) =>
    let uni_tree := BackTree.modifyAtGoalId_wUpdatesG gol st.back.id_gen_assign (fun
      | .ofGoal j t bdirs gdirs ts => .ofGoal j t bdirs gdirs ((.ofUni st.back.id_gen_assign (.gnode sol (.ofBvar 42))) :: ts)
      | .ofPropa i j t bdirs gdirs ts => .ofPropa i j t bdirs gdirs ((.ofUni st.back.id_gen_assign (.gnode sol (.ofBvar 42))) :: ts)
      | x => x) st.back.bt
    match integrate_uni? st.back.id_gen_assign st.back.id_gen_goal (us.map Prod.fst) (us.map Prod.snd) st.fctx uni_res uni_tree with
    | .some (uni_assi, nbt, ngs, ngi) =>
        --dbg_trace s!"(tryUniAll) ngs {repr ngs}"
        let nb := integrate_uni_full st.back nbt ngs ngi gol
        --dbg_trace s!"(tryUniAll) nb.active_goals {repr nb.active_goals}"
        {st with back := nb, unif_assign := (st.back.id_gen_assign, uni_assi, us) :: st.unif_assign, uni_memo := (sol,gol) :: st.uni_memo}
    | _ => S
    )) st
  interated

#exit






partial def search_step (premises : List miniPermiseDict) (st : SearchState) : SearchState :=
  let unistep := tryUniAll st
  --dbg_trace s!"(unistep)\nBacktree:\n{repr unistep.back.bt}\nGoals:\n{repr unistep.back.active_goals}\nForward:{repr unistep.forw}\nBack memo:\n{unistep.back_memo}\nUni memo:\n{unistep.uni_memo}\nUni clashes:\n{unistep.uni_claches}\n\n"
  let forwstep := match tryFor premises unistep with | .some new => new | _ => unistep
  --dbg_trace s!"(forward)\nBacktree:\n{repr forwstep.back.bt}\nGoals:\n{repr forwstep.back.active_goals}\nForward:{repr forwstep.forw}\nBack memo:\n{forwstep.back_memo}\nUni memo:\n{forwstep.uni_memo}\nUni clashes:\n{forwstep.uni_claches}\n\n"
  match tryBack forwstep.fctx premises forwstep.back_memo forwstep.back with
  | .some (nb,nf,nm) => {forwstep with back := nb, fctx := nf, back_memo := nm}
  | _ => forwstep


partial def search (fuel : Nat) (premises : List miniPermiseDict) (st : SearchState) : Option CExpr :=
  let rec loop : Nat → SearchState → Option CExpr
    | 0, _ => .none
    | n+1, nx =>
      let st := search_step premises nx
      dbg_trace s!"(search) loop {n+1}\nBacktree:\n{repr st.back.bt}\nGoals:\n{repr st.back.active_goals}\nForward:{repr st.forw}\nBack memo:\n{st.back_memo}\nUni memo:\n{st.uni_memo}\nUni clashes:\n{st.uni_claches}\n\n"
      let tmp := (st.unif_assign.map (fun (a,b,_) => (a,b)))
      let (sols?,kC) := BackTree.assemble?
        st.ltx_assemmbly tmp
        st.uni_claches st.back.bt
      match sols? with
      | [] => loop n {st with uni_claches := kC}
      | (tada, ah?) :: _ => .some (unfoldLNodes tmp ah? tada)
  loop fuel st


/-
Todo:
- check for unification clashes durring unification step, not assembly ?

-/

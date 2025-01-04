
import LeanGrow.F.Search.A.trBack
import LeanGrow.F.Data.Unification.EmbedRawWInferWUnis
import LeanGrow.F.Data.Unification.EmbedGoalWInferWUnis


#check 1


structure miniPermiseDict where
  name : Name
  data : Array EmbedData
  order : Array Nat
  goal : CExpr



structure SearchState where
  back : BackState
  forw : List (Nat × CExpr)
  forw2 : List (Array CExpr)
  ltx_handler : Nat → (Nat × Nat)
  forwID : Nat
deriving Inhabited--, Repr, BEq




def tryBackOn (fctx : FixCtx) (premises : List miniPermiseDict)
  (active_goal : CExpr) (active_goal_id : Nat) (state : BackState) : Option BackState :=
  let rec findBack : List miniPermiseDict → Option (miniPermiseDict × Array (Option CExpr))
    | [] => .none
    | p :: ps =>
        let res? := match_goal fctx p.data p.data.size p.goal active_goal
        match res? with
        | .some res => .some (p,res)
        | _ => findBack ps
  match findBack premises with
  | .none => .none
  | .some (prem,res) =>
      let (assi,newg) := propagate_lnode_and_tag prem.data state.id_gen_back res
      .some (integrate_backstep_main prem.name prem.data.size active_goal_id assi newg state)

def tryBack (fctx : FixCtx) (premises : List miniPermiseDict) (state : BackState) : Option BackState :=
  let rec go : List (Nat × CExpr) → Option BackState
    | [] => .none
    | (id,g) :: more =>
        match tryBackOn fctx premises g id state with
        | .some new => .some new
        | _ => go more
  go state.active_goals

def tryForwWith (fctx : FixCtx) (premises : List miniPermiseDict)


#exit

def search_step (fctx : FixCtx) (premises : List miniPermiseDict) (st : SearchState) : SearchState :=

  let rec uni_ltx_activeGoals  (s g : List (Nat × CExpr)) : Option (List (Nat × Nat × CExpr)) :=
    -- try to find one unification of ltx result and an active goal
    match s, g with
    | x :: xs, y :: _ =>
        match (CExpr.MatchAssignSolutions' x.2 y.2) with
        | .some (res,_) => .some res
        | .none => .none
    | [], _ :: ys => uni_ltx_activeGoals st.forw ys
    | _,_ => .none

  match uni_ltx_activeGoals st.forw st.back.active_goals with
  | .some uni_res =>
      match integrate_uni? st.forw2 st.ltx_handler uni_res st.back.bt with
      | .some (nbt, slved) =>
         let nb := integrate_uni_full st.back nbt slved
         {st with back := nb}
      | _ => sorry
  | _ => sorry

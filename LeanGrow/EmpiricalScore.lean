
import LeanGrow.Caches.QueryTreeSmoothClusters_wL_col2
import LeanGrow.Caches.QueryTreeSmoothClustersGoal_wL_col2
import LeanGrow.Transitions_QueTreClus

open Lean Data


#check LinkTreeTop
#check g_LinkTreeTop



partial def Trie.merge_with [BEq α] [Inhabited α] (l r : Trie α) (f : α → α → α) : Trie α  :=
  let mini_merge (x y : Option α) : Option α :=
    (match x, y with
     | .some X , .some Y => .some (f X Y)
     | .some X , .none => .some X
     | .none,  .some Y => .some Y
     | _, _ => .none)
  match l with
  | .leaf x =>
      match r with
      | .leaf y => .leaf (mini_merge x y)
      | .node1 y ay cy => .node1 (mini_merge x y) ay cy
      | .node y ay cy => .node (mini_merge x y) ay cy
  | .node1 x ax cx =>
      match r with
      | .leaf y => .node1 (mini_merge x y) ax cx
      | .node1 y ay cy =>
          match Ord.compare ax ay with
          | .lt => .node (mini_merge x y) ⟨#[ax, ay]⟩  #[cx, cy]
          | .eq => .node1 (mini_merge x y) ax  (Trie.merge cx cy)
          | .gt => .node (mini_merge x y) ⟨#[ay, ax]⟩  #[cy, cx]
      | .node y ay cy =>
          match ay.has? ax with
          | .none =>
                let (cs',n) := Array.orderedInsertWithIndex (· ≤ ·) ax ay.data
                .node (mini_merge x y) (⟨cs'⟩) (cy.insertAt! n cx)
          | .some i =>
                .node (mini_merge x y) ay (cy.modify i (Trie.merge cx))
  | .node x ax cx =>
      match r with
      | .leaf y => .node (mini_merge x y) ax cx
      | .node1 y ay cy =>
          match ax.has? ay with
          | .none =>
                let (cs',n) := Array.orderedInsertWithIndex (· ≤ ·) ay ax.data
                .node (mini_merge x y) (⟨cs'⟩) (cx.insertAt! n cy)
          | .some i =>
                .node (mini_merge x y) ax (cx.modify i (Trie.merge cy))
      | .node y ay cy =>
          let (uni_b, uni_t) := ByteArray.merge_extra ax ay cx cy
          .node (mini_merge x y) uni_b uni_t



open Meta


def myWithDecl (n : Name) (type : Expr) (k : Expr → MetaM α ) : Expr → MetaM (α × Context)  := fun b => do
    let fvarId ← mkFreshFVarId
    let ctx ← read
    let lctx := ctx.lctx.mkLocalDecl fvarId n type
    let fvar := mkFVar fvarId
    withReader (fun ctx => { ctx with lctx := lctx }) do
      (if let .some c := (← isClass? type)
       then withNewLocalInstance c fvar (do let res ← k (b.instantiate1 fvar) ; return (res,← read))
       else (do let res ← k (b.instantiate1 fvar) ; return (res,← read))
        )

elab "test_1" : tactic => do
  let k : Expr → MetaM Unit := fun e => do let s ← ppExpr e ; let s' ← ppExpr (← inferType e) ; logInfo s!"{s} of type {s'}"
  let K := myWithDecl `test (.const `Nat []) k
  let _ ← K (.bvar 0)

set_option linter.unusedTactic false in
example : True :=
  by
  test_1
  exact True.intro



def loadDecls (d : Array (Name × Expr)) : MetaM (List (Expr) × Context) := do
  let ctx ← read
  let loop := fun (sofar_vars, sofar_ctx) (n,t) => do
    let fvarId ← mkFreshFVarId
    let lctx := sofar_ctx.mkLocalDecl fvarId n t
    let fvar := mkFVar fvarId
    return(fvar :: sofar_vars, lctx)
  let (L,lC) ← d.foldlM loop ([],ctx.lctx)
  return (L.reverse, {ctx with lctx := lC})


elab "test_2" : tactic => do
  let (_,c) ← loadDecls #[(`A, (.const `Nat [])), (`B, (.const `Int []))]
  let new_goal ← mkFreshExprMVarAt c.lctx c.localInstances (← Elab.Tactic.getMainTarget)
  MVarId.assign (← Elab.Tactic.getMainGoal) new_goal
  Elab.Tactic.setGoals [new_goal.mvarId!]

#check Elab.Tactic.TacticM

set_option linter.unusedTactic false in
example : True :=
  by
  test_2
  -- note the new hyps
  exact True.intro



def get_body_hyps (proof : Expr) : Expr × List (Name × Expr) :=
  match proof with
  | .lam n t b _ => (get_body_hyps b).map id (List.cons (n,t))
  | e => (e,[])


#check Meta.lambdaTelescope


partial def load_body_hyps_aux (proof : Expr) (c : Context) : MetaM (Expr × List (Expr) × Context) := do
  match proof with
  | .lam n t b _ => do
        let fvarId ← mkFreshFVarId
        let new_lctx := c.lctx.mkLocalDecl fvarId n t
        let fvar := mkFVar fvarId
        let B := b.instantiate1 fvar
        let (g,L,C) ← load_body_hyps_aux B {c with lctx := new_lctx}
        return (g, t :: L, C)
  | e => return (e,[],c)


def load_body_hyps (proof : Expr) : MetaM (Expr × Array (Expr) × Context) := do
  let (g,L,C) ← load_body_hyps_aux proof (← read)
  return (g,L.toArray,C)


#print Nat.add_comm

#print List.append_cons

lemma test_3 (as : List α) (b : α) (bs : List α) : as ++ b :: bs = as ++ [b] ++ bs :=
  by
  have beta? := List.append_cons as b
  exact beta? bs

--set_option pp.all true in
#print test_3

#check Lean.isBRecOnRecursor

#check Lean.Meta.reduce


elab "test_4" : command => do
  let .thmInfo proof := (← getEnv).constants.find! `Nat.add_comm | throwError "ahh 1"
  let r ← Elab.Command.liftTermElabM (@Lean.Meta.reduce proof.value false true false)
  let s ← Elab.Command.liftTermElabM (ppExpr r)
  logInfo s

-- set_option pp.all true in
-- set_option pp.instances false in
test_4

elab "test_5" t:term : command => do
  let T ← Elab.Command.liftTermElabM (Elab.Term.elabTermAndSynthesize t .none)
  let r ← Elab.Command.liftTermElabM (@Lean.Meta.reduce T false false false)
  let s ← Elab.Command.liftTermElabM (ppExpr r)
  logInfo s

set_option pp.all true in
test_5 (fun n : Nat => (n+n))
-- replace printed r with T in `test_5` and note that instances get replaced !

elab "test_6" : command => do
  let info := (← getEnv).constants.find! `Nat.brecOn
  logInfo s!"{info.isThm}"

test_6


structure sampleType where
  thm_name : Name
  goal_type : Expr
  hyp_types : Array Expr
  ctx : Meta.Context

def isThmApp (proof : Expr) : MetaM (Option (Name × Array Expr)) := do
  let args := proof.getAppArgs
  if args.isEmpty
  then
    return .none
  else
    let .some (n,_) := proof.getAppFn.const? | return .none
    let .thmInfo _ := (← getEnv).constants.find! n |  return .none
    return (n,args)


def sample_finisher (proof : Expr) : MetaM (Option sampleType) := do
  let (g,_,c) ← load_body_hyps proof
  let .some (n,args) ← isThmApp g | return .none
  let gt ← withLCtx c.lctx c.localInstances (inferType g)
  let argst ← args.mapM (fun x => withLCtx c.lctx c.localInstances (inferType x))
  return .some ⟨n, gt, argst, c⟩

def Expr.getFunBody : Expr → Expr
| .lam _ _ b _ => Expr.getFunBody b
| x => x

def Expr.isAtom : Expr → MetaM Bool
| .fvar _ | .sort _ | .lit _ => return true
| .mdata _ e => Expr.isAtom e
| .proj _ _ e => Expr.isAtom e
| .app l r => return (← Expr.isAtom l) && (← Expr.isAtom r)
| .const n l => do
      let T ← inferType (.const n l)
      let Th := Expr.getFunBody T
      if (← inferType Th).isProp then return false else return true
| _ => return false


def Expr.isStarter (e : Expr) : MetaM (Option (Name × Array Expr)) := do
  let .some (n,args) ← isThmApp e | return .none
  let arg_atoms? := (← args.mapM Expr.isAtom).contains false
  if arg_atoms? then return .none else return .some (n,args)

partial def Expr.findStarters : Expr →  MetaM (Array (Name × Array Expr))
| .mdata _ e => Expr.findStarters e
| .proj _ _ e => Expr.findStarters  e
| e => do
    if let .some (n,args) ← Expr.isStarter e
    then
      return #[(n,args)]
    -- if not, search starters among args, and return nothing if fun appli (as these would require a different context)
    else
      let args := e.getAppArgs
      let res ← args.mapM Expr.findStarters
      return res.join


def sample_starters (proof : Expr) : MetaM (Array sampleType) := do
  let (g,_,c) ← load_body_hyps proof
  let A ← Expr.findStarters g
  let gt ← withLCtx c.lctx c.localInstances (inferType g)
  let AT ←  A.mapM (fun (n,x) => do let ts ← x.mapM (fun y => withLCtx c.lctx c.localInstances (inferType y)) ; return (n,ts))
  return AT.map (fun h => ⟨h.1,gt,h.2,c⟩)


def sample_self (proof : Expr) (name : Name) : MetaM (sampleType) := do
  let (g,as,c) ← load_body_hyps proof
  let gt ← withLCtx c.lctx c.localInstances (inferType g)
  return ⟨name,gt,as,c⟩

def dsiplay_sample (s : sampleType) : MetaM String := do
  let g ← (withLCtx s.ctx.lctx s.ctx.localInstances (ppExpr s.goal_type))
  let hs ← (withLCtx s.ctx.lctx s.ctx.localInstances (s.hyp_types.mapM  ppExpr))
  return s!"Thm: {s.thm_name}\nGoal {g}\nHyps {hs}"

def lifting_sucks (proof : TheoremVal) (N : Name) : MetaM String := do
  let p ←  (@Lean.Meta.reduce proof.value false true false)
  let ss ←  (Array.mapM dsiplay_sample (← (sample_starters p)))
  let sf' ← sample_finisher p
  let mut pain := "none"
  if let .some sf := sf' then pain ← dsiplay_sample sf
  let sS ←  (dsiplay_sample (←  (sample_self p N)))
  return s!"Self:\n{sS}\nStarters:\n{String.intercalate "\n" (ss).toList}\nFinisher:\n{pain}"


elab "test_sampling" : command => do
  let N := `List.append_cons
  let .thmInfo proof := (← getEnv).constants.find! N | throwError "ahh 1"
  let print ← Elab.Command.liftTermElabM (lifting_sucks proof N)
  logInfo print

--test_sampling

#print List.append_cons
#print Nat.add_comm
#print test_3

#check 1

#eval ppExpr (.bvar 0)

#exit


#check Trie.upsert

#check Expr.getAppFn



open Meta

partial def count_thms : Expr → MetaM Nat
| .lam n t b _ => do
    let fvarId ← mkFreshFVarId
    let ctx ← read
    let lctx := ctx.lctx.mkLocalDecl fvarId n t
    let fvar := mkFVar fvarId
    withReader (fun ctx => { ctx with lctx := lctx }) do
      (if
        let .some c := (← isClass? t)
        then
        withNewLocalInstance c fvar <| count_thms (b.instantiate1 fvar)
        else
        count_thms (b.instantiate1 fvar)
          )
| .mdata _ e | .proj _ _ e => count_thms e
| .app l r => do
      let cl ← count_thms l
      let cr ← count_thms r
      return cl+cr
| .const c l => do --const and fvar
      if (← inferType (.const c l)).isProp then return 1 else return 0
| _ => return 0



partial def sample_goal_and_hyps (proof : Expr) : MetaM (Option (Name × (Expr × Context) × List (Expr × Context))) :=
  match proof with
  | .lam n t b _ => do
      let fvarId ← mkFreshFVarId
      let ctx ← read
      let lctx := ctx.lctx.mkLocalDecl fvarId n t
      let fvar := mkFVar fvarId
      withReader (fun ctx => { ctx with lctx := lctx }) do
        (if
          let .some c := (← isClass? t)
         then
          withNewLocalInstance c fvar ((Option.map (fun (s,g,h) => (s,g, (t,ctx) :: h))) <$> (sample_goal_and_hyps (b.instantiate1 fvar)))
         else
          ((Option.map (fun (s,g,h) => (s,g, (t,ctx) :: h))) <$> (sample_goal_and_hyps (b.instantiate1 fvar)))
           )
  | .mdata _ e | .proj _ _ e => sample_goal_and_hyps e
  | e => do
      let args := e.getAppArgs
      let h := e.getAppFn
      match h with
      | .const n _ =>
            if (← inferType h).isProp
            then
              let appears ← args.mapM count_thms
              let total := appears.foldl (fun s x => s+x) 0
              if total = 0
              then
                return .some (n,((← inferType e), (← read)),[])
              else
                let r ← IO.rand 0 (total + 1)
                if r = total + 1
                then
                  return .some (n,(← inferType e, (← read)),[])
                else
                  let mut sum := 0
                  let mut idx := 0
                  for w in appears do
                    if r > sum then sum := sum + w ; idx := idx + 1
                  let .some (N, goal, _) ← sample_goal_and_hyps (args.get! idx) | return .none
                  let mut hyps := []
                  let mut idx2 := 0
                  for a in args do
                    if idx2 ≠ idx
                    then
                      let .some (_,_, hyp) ← sample_goal_and_hyps a | pure ()
                      hyps := hyp :: hyps
                      idx2 := idx2 + 1
                    else
                      idx2 := idx2 + 1
                  return .some (N, goal, hyps.join)
            else
              return .none
      | _ => return .some (`Dummy ,(.const `DUMMY [], {}) ,[(← inferType e, (← read))])


elab "testing_sample_goal_and_hyps" : command => do
  let thm_name := `List.append_cons
  let info := ((← getEnv).constants.find! thm_name)
  match info with
  | .thmInfo v =>
      let .some (N,T,H) ←  (sample_goal_and_hyps v.value) | throwError "aaahh 1"
      --let TT := ← withLCtx T.2.lctx T.2.localInstances (inferType T.1)
      let X ←   ((H.map Prod.fst).mapM (ppExpr) : MetaM (List Format))
      IO.println s!"Sampleted: {N}\nGoal: {←   (ppExpr T.1)}\nAssumptions: {X}"
  | _ => throwError "aaahh 2"

--testing_sample_goal_and_hyps

#exit

#check IO.rand
#check Meta.transform

def sample_data (proof : Expr) : MetaM (Trie (List ((List Nat) × (List Nat)))) := do
  sorry

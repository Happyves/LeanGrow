
import LeanGrow.Caches.QueryTreeSmoothClusters_wL_col2
import LeanGrow.Caches.QueryTreeSmoothClustersGoal_wL_col2
import LeanGrow.Transitions_QueTreClus



open Lean Data Meta


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
        return (g, fvar :: L, C)
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
  hyps : Array Expr
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
  --let argst ← args.mapM (fun x => withLCtx c.lctx c.localInstances (inferType x))
  return .some ⟨n, gt, args, c⟩

def sample_finisher_wC (proof : Expr) (k : Context) (As : Array Expr) : MetaM (Option sampleType) := do
  let (g,_,c) ← load_body_hyps_aux proof k
  let .some (n,args) ← isThmApp g | return .none
  let gt ← withLCtx c.lctx c.localInstances (inferType g)
  --let argst ← args.mapM (fun x => withLCtx c.lctx c.localInstances (inferType x))
  return .some ⟨n, gt, As ++ args, c⟩




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
  --let AT ←  A.mapM (fun (n,x) => do let ts ← x.mapM (fun y => withLCtx c.lctx c.localInstances (inferType y)) ; return (n,ts))
  return A.map (fun h => ⟨h.1,gt,h.2,c⟩)

def sample_starters_wC (proof : Expr) (k : Context) (As : Array Expr) : MetaM (Array sampleType) := do
  let (g,_,c) ← load_body_hyps_aux proof k
  let A ← Expr.findStarters g
  let gt ← withLCtx c.lctx c.localInstances (inferType g)
  --let AT ←  A.mapM (fun (n,x) => do let ts ← x.mapM (fun y => withLCtx c.lctx c.localInstances (inferType y)) ; return (n,ts))
  return A.map (fun h => ⟨h.1,gt,As ++ h.2,c⟩)


def sample_self (proof : Expr) (name : Name) : MetaM (sampleType) := do
  let (g,as,c) ← load_body_hyps proof
  let gt ← withLCtx c.lctx c.localInstances (inferType g)
  return ⟨name,gt,as,c⟩

def dsiplay_sample (s : sampleType) : MetaM String := do
  let g ← (withLCtx s.ctx.lctx s.ctx.localInstances (ppExpr s.goal_type))
  let hs ← (withLCtx s.ctx.lctx s.ctx.localInstances (s.hyps.mapM  ppExpr))
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



partial def get_topmost_potential_subproofs (proof : Expr) (d : Nat) : (List (Expr × Bool)) :=
match proof with
| .proj _ _ e | .mdata _ e => get_topmost_potential_subproofs e d
| _ =>
  let args := proof.getAppArgs
  let h := proof.getAppFn
  if d == 0 || args.isEmpty
  then
    [(proof, false)]
  else
    Id.run do
      let mut toAdd := []
      for a in args do
        if !(a.getAppFn).isLambda
        then
          let res := get_topmost_potential_subproofs a (d-1)
          toAdd := res :: toAdd
        else
          toAdd := [(a,true)] :: toAdd
      if !(h.getAppFn).isLambda -- for cases when head is a projection, for example
      then
        let res := get_topmost_potential_subproofs h (d-1)
        toAdd := res :: toAdd
      else
        toAdd := [(h,true)] :: toAdd
      return ((proof, false) :: toAdd.join)

--#exit

def sample_hard (proof : TheoremVal) (name : Name) (d : Nat) : MetaM (sampleType × Array sampleType) := do
  let proofR ←  (@Lean.Meta.reduce proof.value false true false)
  let ss ← sample_self proofR name
  let mut out := []
  let (g,as,c) ← load_body_hyps proofR
  let sp := get_topmost_potential_subproofs g d
  for (p,_) in sp do -- bool wasn't needed
    let sf ← sample_finisher_wC p c as
    let sS ← sample_starters_wC p c as
    match sf with
    | .some S => out := #[S] :: sS :: out
    | _ => out := sS :: out
  return (ss,out.toArray.join)


def lifting_sucks_2 (proof : TheoremVal) (N : Name) (d : Nat) : MetaM String := do
  let res ← sample_hard proof N d
  let sS ← dsiplay_sample res.1
  let os := (← res.2.mapM dsiplay_sample).toList
  return s!"Self:\n{sS}\n\nOthers:\n{String.intercalate "\n" os}"


elab "test_sampling_2" : command => do
  let N := `Nat.add_comm
  let .thmInfo proof := (← getEnv).constants.find! N | throwError "ahh 1"
  let print ← Elab.Command.liftTermElabM (lifting_sucks_2 proof N 10)
  logInfo print

test_sampling_2
-- Notes wrt ↓↑ : proofs can be wrap in wierd stuff due to tactics ; for `Nat.add_comm` , the induction steps are in a product with PUnit (?!?), so we need to dig dow (high depth at `sample_hard`) to get to them
test_4

#print List.append_cons
#print Nat.add_comm
#print test_3

#check 1


partial def get_potential_subproofs (proof : Expr) (d : Nat) (c : Context) : MetaM (List (Expr × Context)) :=
match proof with
| .proj _ _ e | .mdata _ e => get_potential_subproofs e d c
| _ => do
  let args := proof.getAppArgs
  let h := proof.getAppFn
  if d == 0 || args.isEmpty
  then
    return [(proof, c)]
  else
    let mut toAdd := []
    for a in args do
      if !(a.getAppFn).isLambda
      then
        let res ← get_potential_subproofs a (d-1) c
        toAdd := res :: toAdd
      else
        let (g,_,nc) ← load_body_hyps_aux a c
        let res ← get_potential_subproofs g (d-1) nc
        toAdd := res :: toAdd
    if !(h.getAppFn).isLambda -- for cases when head is a projection, for example
    then
      let res ← get_potential_subproofs h (d-1) c
      toAdd := res :: toAdd
    else
      let (g,_,nc) ← load_body_hyps_aux h c
      let res ← get_potential_subproofs g (d-1) nc
      toAdd := res :: toAdd
    return ((proof, c) :: toAdd.join)

def sample_harder (proof : TheoremVal) (name : Name) (d : Nat) : MetaM (sampleType × Array sampleType) := do
  let proofR ←  (@Lean.Meta.reduce proof.value false true false)
  let ss ← sample_self proofR name
  let mut out := []
  let (g,as,c) ← load_body_hyps proofR
  let sp ←  get_potential_subproofs g d c
  for (p,pc) in sp do -- bool wasn't needed
    let sf ← sample_finisher_wC p pc as
    let sS ← sample_starters_wC p pc as
    match sf with
    | .some S => out := #[S] :: sS :: out
    | _ => out := sS :: out
  return (ss,out.toArray.join)


def lifting_sucks_3 (proof : TheoremVal) (N : Name) (d : Nat) : MetaM String := do
  let res ← sample_harder proof N d
  let sS ← dsiplay_sample res.1
  let os := (← res.2.mapM dsiplay_sample).toList
  return s!"Self:\n{sS}\n\nOthers:\n{String.intercalate "\n" os}"


elab "test_sampling_3" : command => do
  let N := `Nat.add_comm
  let .thmInfo proof := (← getEnv).constants.find! N | throwError "ahh 1"
  let print ← Elab.Command.liftTermElabM (lifting_sucks_3 proof N 10)
  logInfo print

test_sampling_3


def samples_clean (S : Array sampleType) : Array sampleType := Id.run do
  let mut ignore : Trie Expr := Trie.empty
  let mut cs := []
  for s in S do
    let sn := s.thm_name.toString
    if let .some e := ignore.find? sn
    then
      if !(e == s.goal_type)
      then
        cs := s :: cs
        ignore := ignore.insert sn s.goal_type
    else
      cs := s :: cs
      ignore := ignore.insert sn s.goal_type
  return cs.toArray

def lifting_sucks_4 (proof : TheoremVal) (N : Name) (d : Nat) : MetaM String := do
  let res ← sample_harder proof N d
  let sS ← dsiplay_sample res.1
  let os := (← (samples_clean res.2).mapM dsiplay_sample).toList
  return s!"Self:\n{sS}\n\nOthers:\n{String.intercalate "\n" os}"


elab "test_sampling_4" : command => do
  let N := `Nat.add_comm
  let .thmInfo proof := (← getEnv).constants.find! N | throwError "ahh 1"
  let print ← Elab.Command.liftTermElabM (lifting_sucks_4 proof N 10)
  logInfo print

test_sampling_4


-- here so as to avoid import pain
structure empiricalScores where
  hyp_cl : RBNode Nat (fun _ => Nat)
  g_cl : RBNode Nat (fun _ => Nat)

inductive tBS (α : Type _) where
| ofVal (_ : α)
| ofPoint (_ : Trie (tBS α))
deriving Inhabited

-- make it polymorphic during fix
structure empiricalScores' where
  hyp_cl : RBNode Nat (fun _ => Float)
  g_cl : RBNode Nat (fun _ => Float)

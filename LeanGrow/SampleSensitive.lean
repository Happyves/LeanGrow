
import LeanGrow.EmpiricalScore

open Lean Data Meta

#check Nat → Nat → Prop
#check Prop
universe u
#check Nat → Nat → Sort u

def Expr.isSensitiveType (e : Expr) : MetaM Bool := do
  let T ← inferType e
  match T with
  | .sort .zero => return false
  | _ => return true

def Expr.isSensitiveType_inC (c : Context) (e : Expr) : MetaM Bool := do
  let T ← withLCtx c.lctx c.localInstances (inferType e)
  let H ← withLCtx c.lctx c.localInstances (inferType (Expr.getForallBody T))
  match H with
  | .sort .zero => return false
  | _ => return true

#check Expr.getForallBody
--#exit

def showConstInfo : ConstantInfo → String
  | .axiomInfo    _ => "axiom"
  | .defnInfo     _ => "def"
  | .thmInfo      _ => "thm"
  | .opaqueInfo   _ => "opaque"
  | .quotInfo     _ => "quot"
  | .inductInfo   _ => "induct"
  | .ctorInfo     _ => "ctor"
  | .recInfo      _ => "recursor"

elab "test_7" n:name : command => do
  match (Lean.Syntax.isNameLit? n.raw) with
  | none => throwError "aaahh"
  | some N =>
      let info := (← getEnv).constants.find! N
      logInfo s!"{showConstInfo info}"


test_7 `Nat.brecOn
test_7 `Nat.recOn
test_7 `Nat.rec
test_7 `Eq.rec
test_7 `List.noConfusion
test_7 `Decidable.casesOn
test_7 `Decidable.rec


#check List.noConfusion
-- not a def though

test_7 `Decidable.casesOn
--test_7 `Decidable.cases -- doesn't it exist ?
#check Decidable.casesOn
#check_failure Decidable.cases


--#exit

structure sampleType_Recursor where
  rec_name : Name
  goal_type : Expr
  ctx : Meta.Context

structure sampleType_Sensitive where
  thm_name : Name
  goal_type : Expr
  terms : List (Nat × Expr)
  ctx : Meta.Context

def isRecApp (proof : Expr) : MetaM (Option (Name × Array Expr)) := do
  let args := proof.getAppArgs
  if args.isEmpty
  then
    return .none
  else
    let .some (n,_) := proof.getAppFn.const? | return .none
    let .recInfo _ := (← getEnv).constants.find! n |  return .none
    return (n,args)


#check Nat.rec

partial def getSensitiveTypeArgs_main (candidates : Array Expr) (e : Expr) (c : Context) (count : Nat) : MetaM (List (Nat × Expr)) :=
  match e with
  | .forallE n t b _ => do
        -- let fvarId ← mkFreshFVarId
        -- let new_lctx := c.lctx.mkLocalDecl fvarId n t
        -- let fvar := mkFVar fvarId
        -- let B := b.instantiate1 fvar
        -- let L ← getSensitiveTypeArgs_main candidates B {c with lctx := new_lctx} (count+1)
        let s? ← Expr.isSensitiveType_inC c t
        if s?
        then
          let hmm := candidates.get! count
          let B := b.instantiate1 hmm
          let L ← getSensitiveTypeArgs_main candidates B c (count+1)
          return ((count, hmm) :: L)
        else
          let fvarId ← mkFreshFVarId
          let new_lctx := c.lctx.mkLocalDecl fvarId n t
          let fvar := mkFVar fvarId
          let B := b.instantiate1 fvar
          getSensitiveTypeArgs_main candidates B {c with lctx := new_lctx} (count+1)
  | _ => return []


--#exit

def getSensitiveTypeArgs (e : Expr) (c : Context) : MetaM (Option (Name × List (Nat × Expr))) := do
  let h := Expr.getAppFn e
  let .some (n, _) := h.const? | return .none
  let T ← withLCtx c.lctx c.localInstances (inferType h)
  let args := Expr.getAppArgs e
  dbg_trace s!"Args {← args.mapM (fun a => withLCtx c.lctx c.localInstances (ppExpr a))}"
  let res ← getSensitiveTypeArgs_main args T c 0
  return .some (n,res)


def getSensitiveTypeArgs' (e : Expr) (c : Context) : MetaM (Option (Name × List (Nat × Expr))) := do
  let h := Expr.getAppFn e
  let .some (n, _) := h.const? | return .none
  let args := Expr.getAppArgs e
  let mut idx := 0
  let mut out := []
  for a in args do
    if ← Expr.isSensitiveType_inC c a
    then
      out := (idx, a) :: out
      idx := idx + 1
    else
      idx := idx + 1
  if out.isEmpty
  then
    return .none
  else
    return .some (n, out)




--#exit

#check get_potential_subproofs


def sample_Recs_Sensitives (proof : Expr) (d : Nat) (c : Context) : MetaM (List sampleType_Recursor × List sampleType_Sensitive) := do
  let subs ← get_potential_subproofs proof d c
  let mut ST := []
  let mut R := []
  for (p, C) in subs do
    let G ← withLCtx C.lctx C.localInstances (inferType p)
    if let .some (n,_) ← isRecApp p
    then
      R := ⟨n,G,C⟩ :: R
    let .some ls ← getSensitiveTypeArgs' p C | pure ()
    ST := ⟨ls.1,G,ls.2,C⟩ :: ST
  return (R,ST)


def samples_clean_R (S : Array sampleType_Recursor) : Array sampleType_Recursor := Id.run do
  let mut ignore : Trie Expr := Trie.empty
  let mut cs := []
  for s in S do
    let sn := s.rec_name.toString
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



def samples_clean_S (S : Array sampleType_Sensitive) : Array sampleType_Sensitive := Id.run do
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


def sample_spe (proof : TheoremVal) (d : Nat) : MetaM (Array sampleType_Sensitive × Array sampleType_Recursor) := do
  let proofR ←  (@Lean.Meta.reduce proof.value false true false)
  let (g,_,c) ← load_body_hyps proofR
  let (R,S) ← sample_Recs_Sensitives g d c
  return (samples_clean_S S.toArray, samples_clean_R R.toArray)


def lifting_sucks_5 (proof : TheoremVal) (d : Nat) : MetaM String := do
  let (S,R) ← sample_spe proof d
  let mut P := ["Recursors"]
  for r in R do
    let g ← withLCtx r.ctx.lctx r.ctx.localInstances (ppExpr r.goal_type)
    P := s!"{r.rec_name} at goal {g}" :: P
  P := "Sensitives" :: P
  for s in S do
    let g ← withLCtx s.ctx.lctx s.ctx.localInstances (ppExpr s.goal_type)
    let sts ← withLCtx s.ctx.lctx s.ctx.localInstances (s.terms.mapM (fun (n,t) => do let pt ← ppExpr t ; return (n,pt)))
    P := s!"{s.thm_name} at goal {g} with sensitive types\n{String.intercalate "\n" (sts.map (fun (n,f) => s!"   Arg {n} as {f}"))}" :: P
  return (String.intercalate "\n" P.reverse)


lemma why (a b : Nat) : a+b=b+a :=
  @Nat.rec (fun x => x+b=b+x) (Nat.zero_add b) (fun n ih => (by dsimp at * ; rw [Nat.succ_add, ih, ← Nat.add_assoc])) a

--#print why
-- stackoverflow bug of 4.10

lemma more_test (a b : List Nat) : List.map (fun x => x^2) (a ++ b) = List.map (fun x => x^2) a ++ List.map (fun x => x^2) b :=
  List.map_append _ a b
-- in test, the power actually gets reduced so as to become (Nat.mul 1 x).mul x
-- ins't a propri a problem, as its coherent if theis is always reduced, but will produce memroisation of unnecessarily big terms

#check 1


lemma more_test_2 : True := @Bool.rec (fun _ => True) True.intro True.intro true
-- nothing gather, as it seems to be reduced ; if reduction is turned of, we recover the motive and `true` as sensitives

set_option pp.all true in
#print by_cases

set_option pp.all true in
#print dite

#check 1

#check Decidable.casesOn

lemma more_test_3 : True := @Decidable.casesOn (2+2=4) (fun _ => True) (.isTrue (by rfl)) (fun _ => True.intro) (fun _ => True.intro)
-- also gets fully reduced ...

lemma more_test_4 (n : Nat) : n ≥ 0 := @Or.rec (Nat.Prime n) (¬ Nat.Prime n) (fun _ => n ≥ 0) (fun _ => Nat.zero_le n) (fun _ => Nat.zero_le n) (em _)


--#exit

elab "test_sampling_5" : command => do
  let N := `more_test_4 -- Nat.add_comm
  let .thmInfo proof := (← getEnv).constants.find! N | throwError "ahh 1"
  let print ← Elab.Command.liftTermElabM (lifting_sucks_5 proof 10)
  logInfo print



test_sampling_5
--
#check PUnit
#check PProd

#check (fun n => n+0 = 0+n)
#check Nat → Prop
#check Nat → Nat
#check Nat.zero_add 1
#check Eq.rec

#check List.map_append


#check congrArg

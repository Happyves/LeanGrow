
import LeanGrow.F.EnvironmentManagement.SampleRegular.ExtractApply
import LeanGrow.F.EnvironmentManagement.SampleRegular.ExtractRW



open Lean Meta


def sample_ofProof (proof : Expr) : MetaM (List SampleTypeRaw) :=
  sorry


#check lambdaLetTelescope
#check lambdaTelescope

#check LocalContext.addDecl

#check inferType

def sample_self (n : Name) (type : Expr) : SampleTypeRaw :=
  sorry

#check getLocalInstances


partial def contextualize (fuel : Nat) (proof : Expr) : MetaM (List (List Expr)) := do
  dbg_trace s!"Looking at {← ppExpr proof}"
  if fuel = 0
  then
    let prop ← inferType proof
    dbg_trace s!"ran out of fuel, returning {← ppExpr prop}"
    return [[prop]]
  else
    match proof with
    | .lam _ _ _ _ => return [[]]
    | _ =>
      let prop ← inferType proof
      let rw? ← extractRWall_main proof
      match rw? with
      | [] =>
        dbg_trace s!"no rw"
        let (_,args?,np) ← extractApply_main proof
        match np ++ args? with -- else apps using no further props aren't recognized
        | [] =>
          dbg_trace s!"no apply"
          let prop ← inferType proof
          dbg_trace s!"none returning {← ppExpr prop}"
          return [[prop]]
        | _ =>
          dbg_trace s!"yes apply"
          if args?.isEmpty
          then
            return [[prop]]
          else
            let ctxs ← args?.mapM (contextualize (fuel - 1))
            dbg_trace s!"apply returning {← ([prop] :: (ctxs.lPi_make'.tailD [])).mapM (fun x => x.mapM ppExpr)}"
            return [prop] :: (ctxs.lPi_make'.tailD []) -- tail because lPi_make' will always start with []
      | _ =>
          dbg_trace s!"yes rw {repr rw?}"
          let big ← rw?.foldlM (fun sofar rw => do
          match rw with
          | .ofLocal next =>
              let ctxs ← [next].mapM (contextualize (fuel - 1))
              return (ctxs) ++ sofar
          | .ofThm a _ b =>
              let ctxs ← (a :: b).mapM (contextualize (fuel - 1))
              return (ctxs) ++ sofar
          | .none => return sofar
          ) []
          dbg_trace s!"rw returning {← ([prop] :: (big.lPi_make'.tailD [])).mapM (fun x => x.mapM ppExpr)}"
          return [prop] :: (big.lPi_make'.tailD [])


partial def subproofs (fuel : Nat) (proof : Expr) : MetaM (List Expr × List (List Expr)) := do
  --dbg_trace s!"Looking at {← ppExpr proof}"
  if fuel = 0
  then
    return ([], [[proof]])
  else
    match proof with
    | .lam _ _ _ _ => return ([proof],[]) -- we ignore ∀ typed parts, as they won't show up durring proof search
    | _ =>
      let rw? ← extractRWall_main proof
      match rw? with
      | [] =>
        let (_,args?,np) ← extractApply_main proof
        match np ++ args? with -- else apps using no further props aren't recognized
        | [] =>
          return ([], [[proof]])
        | _ =>
          if args?.isEmpty
          then
            return ([], [[proof]])
          else
            let pre ← args?.mapM (subproofs (fuel - 1))
            let (todos,ctxs) := pre.unzip
            return (todos.join, [proof] :: (ctxs.lPi_make'.tailD [])) -- tail because lPi_make' will always start with []
      | _ =>
          let (Todos, big) ← rw?.foldlM (fun (sT,sofar) rw => do
          match rw with
          | .ofLocal next =>
              let pre ← [next].mapM (subproofs (fuel - 1))
              let (todos,ctxs) := pre.unzip
              return (todos.join ++ sT, (ctxs) ++ sofar)
          | .ofThm a _ b =>
              let pre ← (a :: b).mapM (subproofs (fuel - 1))
              let (todos,ctxs) := pre.unzip
              return (todos.join ++ sT, (ctxs) ++ sofar)
          | .none => return (sT,sofar)
          ) ([],[])
          return (Todos, [proof] :: (big.lPi_make'.tailD []))



#check 1

def primitiveForwardBlacklist (n : Name) : MetaM Bool := do
  let .some T := ConstantInfo.type <$> (← getEnv).find? n | pure true
  forallTelescope T (fun xs _ => do
    let ts ← (← xs.mapM inferType).mapM whnf
    if ts.contains (.sort .zero) then return false else return true
    ) true
  -- do this in some sort of pre-process and cache way in final version


/-
Note:
We avoid using thms that have no props (proofs) as args as forward steps.
Don't know if this is truely necessary, but this could favor loops: consider for
example Nat.succ (perhaps blacklist only those with no prop ards *and* non-prop return ?).
Also if there are many elements of non-prop arg type (ex: ℕ),then we get too many options ?
-/

partial def sampleForwCoreWB (proof : Expr) : MetaM (List (SampleActionType × Name × List Expr)) := do
  match proof with
  | .lam _ _ _ _ => return []
  | _ =>
    let rw? ← extractRWall_main proof
    match rw? with
    | [] =>
      let (x,args?,_) ← extractApply_main proof
      match x with
      | .some n =>
          if ← primitiveForwardBlacklist n
          then
            let argst ← args?.mapM inferType
            return  [(.ofF,n,argst)]
          else return []
      | _ => return []
    | _ =>
      let big ← rw?.foldlM (fun sofar rw =>
      match rw with
      | .ofThm a x b => do
          if ← primitiveForwardBlacklist x
          then
            let argst ← (a :: b).mapM inferType
            return (.ofFrw,x, argst):: sofar
          else
            return sofar
      | _ => return sofar
      ) []
      return big

def sampleForwStepsWB (fuel : Nat) (proof : Expr) : MetaM (List preSampleTypeRaw) :=
  let rec sampleEach (g : Expr) (seen : List Expr) (done : List preSampleTypeRaw) : List Expr → List Expr → MetaM (List preSampleTypeRaw)
    | t :: ts, T :: Ts => do
        let sam ← sampleForwCoreWB t
        let step : List preSampleTypeRaw := sam.map (fun (k,n,c) => ⟨k,n,g, seen ++ Ts ++ c⟩)
        sampleEach g (T :: seen) (step ++ done) ts Ts
    | _,_ => return done
  do
    let goal ← inferType proof
    let (todos,subproofs) ← subproofs fuel proof
    let mut res := []
    for sp in subproofs do
      let Ts ← sp.mapM inferType
      let step ← sampleEach goal [] [] sp Ts
      res := step ++ res
    return res



partial def sampleForwCore (proof : Expr) : MetaM (List (SampleActionType × Name × List Expr)) := do
  match proof with
  | .lam _ _ _ _ => return []
  | _ =>
    let rw? ← extractRWall_main proof
    match rw? with
    | [] =>
      let (x,args?,_) ← extractApply_main proof
      match x with
      | .some n =>
            let argst ← args?.mapM inferType
            return  [(.ofF,n,argst)]
      | _ => return []
    | _ =>
      let big ← rw?.foldlM (fun sofar rw =>
      match rw with
      | .ofThm a x b => do
            let argst ← (a :: b).mapM inferType
            return (.ofFrw,x, argst):: sofar
      | _ => return sofar
      ) []
      return big

def sampleForwSteps (fuel : Nat) (proof : Expr) : MetaM (List Expr × List preSampleTypeRaw) :=
  let rec sampleEach (g : Expr) (seen : List Expr) (done : List preSampleTypeRaw) : List Expr → List Expr → MetaM (List preSampleTypeRaw)
    | t :: ts, T :: Ts => do
        let sam ← sampleForwCore t
        let step : List preSampleTypeRaw := sam.map (fun (k,n,c) => ⟨k,n,g, seen ++ Ts ++ c⟩)
        sampleEach g (T :: seen) (step ++ done) ts Ts
    | _,_ => return done
  do
    let goal ← inferType proof
    let (todos,subproofs) ← subproofs fuel proof
    let mut res := []
    for sp in subproofs do
      let Ts ← sp.mapM inferType
      let step ← sampleEach goal [] [] sp Ts
      res := step ++ res
    return (todos, res)



def dig (proof : Expr) : MetaM (List Expr) := do
  match proof with
  | .lam _ _ _ _ => return []
  | _ =>
    let rw? ← extractRWall_main proof
    match rw? with
    | [] =>
      let (_,args?,_) ← extractApply_main proof
      return args?
    | _ =>
      let big := rw?.foldl (fun sofar rw =>
      match rw with
      | .ofThm a _ b => (a :: (b ++ sofar))
      | .ofLocal a => a :: sofar
      | _ => sofar
      ) []
      return big

partial def digDepth (proof : Expr) : MetaM Nat :=
  let rec go (done : List Nat) : List (Nat × Expr) → MetaM (List Nat)
    | [] => return done
    | (n,p) :: xs => do
      let dug ← dig p
      if dug.isEmpty
      then
        go (n :: done) xs
      else
        go done ((dug.map (n+1,·)) ++ xs)
  do
    let depths ← go [] [(0,proof)]
    return (match depths.maximum? with | .some w => w | _ => 0)


partial def sampleForw (fuel : Nat) (proof : Expr) : MetaM (List Expr × List preSampleTypeRaw) :=
  let rec go (done : List preSampleTypeRaw) (td : List Expr) : List Expr → MetaM (List Expr × List preSampleTypeRaw)
    | [] => return (td,done)
    | x :: xs => do
      let depth ← digDepth x
      if depth < fuel
      then
        go done td xs
      else
        let (todos,res) ← sampleForwSteps fuel x
        let next ← dig x
        go (res ++ done) (todos ++ td) (next ++ xs)
  go [] [] [proof]


partial def sampleForwAll (fuel : Nat) (proof : Expr) : MetaM (List preSampleTypeRaw) :=
  let rec go (done : List preSampleTypeRaw) : List (Expr × LocalContext) → MetaM (List preSampleTypeRaw)
    | [] => return done
    | (x,ctx) :: xs => do
      withLCtx ctx (← getLocalInstances) do
        lambdaLetTelescope x
          (fun _ head => do
              let (td,res) ← sampleForw fuel head
              let here ← getLCtx
              go (res ++ done) ((td.map (·,here)) ++ xs)
          )
  go [] [(proof, {})]




partial def SampleForw (fuel : Nat) (proof : Expr) : MetaM (List Expr × List SampleTypeRaw) :=
  let rec go (done : List SampleTypeRaw) (td : List Expr) : List Expr → MetaM (List Expr × List SampleTypeRaw)
    | [] => return (td,done)
    | x :: xs => do
      let depth ← digDepth x
      if depth < fuel
      then
        go done td xs
      else
        let (todos,pres) ← sampleForwSteps fuel x
        let Ltx ← getLCtx
        let res ← pres.mapM (fun ⟨k,n,g,c⟩ => do
          let ltx ← c.foldlM (fun s x => do
            let fvarId ← mkFreshFVarId
            return s.mkLocalDecl fvarId n x .default
            ) Ltx
          let (g',c') := translateLocalContext' ltx g
          return ⟨k,n,g',c'⟩)
        let next ← dig x
        go (res ++ done) (todos ++ td) (next ++ xs)
  go [] [] [proof]

partial def SampleForwAll (fuel : Nat) (proof : Expr) : MetaM (List SampleTypeRaw) :=
  let rec go (done : List SampleTypeRaw) : List (Expr × LocalContext) → MetaM (List SampleTypeRaw)
    | [] => return done
    | (x,ctx) :: xs => do
      withLCtx ctx (← getLocalInstances) do
        lambdaLetTelescope x
          (fun _ head => do
              let (td,res) ← SampleForw fuel head
              let here ← getLCtx
              go (res ++ done) ((td.map (·,here)) ++ xs)
          )
  go [] [(proof, {})]



partial def sampleBackCore (proof : Expr) : MetaM (List (SampleActionType × Name × List Expr)) := do
  match proof with
  | .lam _ _ _ _ => return []
  | _ =>
    let rw? ← extractRWall_main proof
    match rw? with
    | [] =>
      let (x,argst,_) ← extractApply_main proof
      match x with
      | .some n => return  [(.ofB,n,argst)]
      | _ => return []
    | _ =>
      let big ← rw?.foldlM (fun sofar rw =>
      match rw with
      | .ofThm a x b => return (.ofBrw,x, (a :: b)):: sofar
      | _ => return sofar
      ) []
      return big


def sampleBackSteps (fuel : Nat) (proof : Expr) : MetaM (List Expr × List preSampleTypeRaw) := do
  let goal ← inferType proof
  let res ← sampleBackCore proof
  let mut R : List preSampleTypeRaw := []
  let mut T := []
  for (k,n,as) in res do
    let pre ← as.mapM (subproofs fuel)
    let (td,sbs) := pre.unzip
    T := td.join :: T
    let sps := (sbs.lPi_make'.tailD [])
    for ctx in sps do
      let ts ← (ctx.mapM inferType)
      R := ⟨k,n,goal,ts⟩ :: R
  return (T.join, R)

partial def sampleBack (fuel : Nat) (proof : Expr) : MetaM (List Expr × List preSampleTypeRaw) :=
  let Fuel := fuel+1
  let rec go (done : List preSampleTypeRaw) (td : List Expr) : List Expr → MetaM (List Expr × List preSampleTypeRaw)
    | [] => return (td, done)
    | x :: xs => do
      let depth ← digDepth x
      if depth < Fuel
      then
        go done td xs
      else
        let (ntd,res) ← sampleBackSteps fuel x
        let next ← dig x
        go (res ++ done) (ntd ++ td) (next ++ xs)
  go [] [] [proof]



partial def sampleBackAll (fuel : Nat) (proof : Expr) : MetaM (List preSampleTypeRaw) :=
  let rec go (done : List preSampleTypeRaw) : List (Expr × LocalContext) → MetaM (List preSampleTypeRaw)
    | [] => return done
    | (x,ctx) :: xs => do
      withLCtx ctx (← getLocalInstances) do
        lambdaLetTelescope x
          (fun _ head => do
              let (td,res) ← sampleBack fuel head
              let here ← getLCtx
              go (res ++ done) ((td.map (·,here)) ++ xs)
          )
  go [] [(proof, {})]

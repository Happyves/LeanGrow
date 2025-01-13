
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


partial def subproofs (fuel : Nat) (proof : Expr) : MetaM (List (List Expr)) := do
  dbg_trace s!"Looking at {← ppExpr proof}"
  if fuel = 0
  then
    return [[proof]]
  else
    match proof with
    | .lam _ _ _ _ => return [[]]
    | _ =>
      let rw? ← extractRWall_main proof
      match rw? with
      | [] =>
        let (_,args?,np) ← extractApply_main proof
        match np ++ args? with -- else apps using no further props aren't recognized
        | [] =>
          return [[proof]]
        | _ =>
          if args?.isEmpty
          then
            return [[proof]]
          else
            let ctxs ← args?.mapM (subproofs (fuel - 1))
            return [proof] :: (ctxs.lPi_make'.tailD []) -- tail because lPi_make' will always start with []
      | _ =>
          let big ← rw?.foldlM (fun sofar rw => do
          match rw with
          | .ofLocal next =>
              let ctxs ← [next].mapM (subproofs (fuel - 1))
              return (ctxs) ++ sofar
          | .ofThm a _ b =>
              let ctxs ← (a :: b).mapM (subproofs (fuel - 1))
              return (ctxs) ++ sofar
          | .none => return sofar
          ) []
          return [proof] :: (big.lPi_make'.tailD [])


partial def sampleCore (proof : Expr) : MetaM (List (Name × List Expr)) := do
  match proof with
  | .lam _ _ _ _ => return []
  | _ =>
    let rw? ← extractRWall_main proof
    match rw? with
    | [] =>
      let (x,args?,_) ← extractApply_main proof
      match x with
      | .some n => return  [(n,args?)]
      | _ => return []
    | _ =>
      let big := rw?.foldl (fun sofar rw =>
      match rw with
      | .ofThm a x b => (x, (a :: b)):: sofar
      | _ => sofar
      ) []
      return big

def sampleForwSteps (fuel : Nat) (proof : Expr) : MetaM (List preSampleTypeRaw) := do
  let goal ← inferType proof
  let subproofs ← subproofs fuel proof
  sorry


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
  then return [[]]
  else
    match proof with
    | .lam _ _ _ _ => return [[]]
    | _ =>
      let prop ← inferType proof
      let rw? ← extractRWall_main proof
      match rw? with
      | [] =>
        dbg_trace s!"no rw"
        let (_,args?) ← extractApply_main proof
        match args? with
        | [] =>
          dbg_trace s!"no apply"
          let prop ← inferType proof
          dbg_trace s!"none returning {← ppExpr prop}"
          return [[prop]]
        | _ =>
          dbg_trace s!"yes apply"
          let ctxs ← args?.mapM (contextualize (fuel - 1))
          dbg_trace s!"apply returning {← ([prop] :: (ctxs.lPi_make)).mapM (fun x => x.mapM ppExpr)}"
          return [prop] :: (ctxs.lPi_make)
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
          dbg_trace s!"rw returning {← ([prop] :: (big.lPi_make)).mapM (fun x => x.mapM ppExpr)}"
          return [prop] :: (big.lPi_make)


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
  if fuel = 0
  then return [[]]
  else
    match proof with
    | .lam _ _ _ _ => return [[]]
    | _ =>
      let prop ← inferType proof
      let (_,args?) ← extractApply_main proof
      match args? with
      | [] =>
        let rw? ← extractRWall_main proof
        match rw? with
        | [] =>
          let prop ← inferType proof
          return [[prop]]
        | _ =>
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
          return [prop] :: (big.lPi_make)
      | _ =>
        let ctxs ← args?.mapM (contextualize (fuel - 1))
        return [prop] :: (ctxs.lPi_make)

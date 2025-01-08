
import LeanGrow.F.EnvironmentManagement.SampleRegular.API

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

def dig_step (proof : Expr) : MetaM (List Expr) :=
  match proof with
  | .app _ _ => do
    let as := proof.getAppArgs
    let mut L := []
    for e in as do
      match e with
      | .fvar _ => continue
      | _ =>
        let T ← inferType e
        let TT ← inferType T
        if TT.isProp
        then L := e :: L
    return L
  | _ => return []

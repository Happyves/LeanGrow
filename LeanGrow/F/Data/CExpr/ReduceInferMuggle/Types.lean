
import LeanGrow.F.Data.CExpr.Types
import LeanGrow.F.Utils.Trie.CTrie
import LeanGrow.F.Data.CExpr.ReduceInferMuggle.ConstInfo

open Lean


structure FixCtx where
  gnodeTypes : List (Array CExpr)
  gnodeTypesHandler : Nat → (Nat × Nat)
  ltxTypes : List (Nat × Array EmbedData)
  current : Option (Array EmbedData)
  cstData : CTrie CstInfo
  deriving Inhabited

inductive FlowType where
| failed
| Whnf_1
| InferType_1
| cInferAppType_1
| cInferAppType_2
| cInferAppType_3
| cInferProjType_1
| cInferProjType_2
| cInferProjType_3
| cInferProjType_4
| cInferLambdaType_1
| cInferLambdaType_2
deriving Inhabited, BEq, Repr


inductive ArgType where
| ofCExpr (_ : CExpr)
| ofList (_ : List CExpr)
| ofName (_ : Name)
| ofNat (_ : Nat)
| ofBinInfo (_ : BinderInfo)
deriving Inhabited, BEq, Repr


structure FlowState where
  insts : List (FlowType × List CExpr) -- instruction and bvarCtx
  args : List ArgType
deriving Inhabited, BEq, Repr

def FailedState : FlowState := ⟨[],[]⟩

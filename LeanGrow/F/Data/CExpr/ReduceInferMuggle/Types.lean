
import LeanGrow.F.Data.CExpr.Types
import LeanGrow.F.Utils.Trie.CTrie
import LeanGrow.F.Data.CExpr.ReduceInferMuggle.ConstInfo

open Lean Meta Match


structure FixCtx where
  gnodeTypes : List (Array CExpr)
  gnodeTypesHandler : Nat → (Nat × Nat)
  ltxTypes : List (Nat × Array EmbedData)
  current : Option (Array EmbedData)
  cstData : CTrie CstInfo
  deriving Inhabited

inductive FlowType where
| Whnf_1
| Whnf_2
| Whnf_3
| Whnf_4
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
| getLevel_1
| getLevel_2
| cInferForallType_1
| cInferForallType_2
| cInferForallType_3
| cInferForallType_4
| cInferForallType_5
| myForallBoundedTelescope_1
| myForallBoundedTelescope_2
| reduceMatcher?_1
| reduceMatcher?_2
| reduceMatcher?_3
| reduceMatcher?_4
| toCtorWhenK_1
| toCtorWhenK_2
| toCtorWhenStructure_1
| toCtorWhenStructure_2
| reduceRec_1
| reduceRec_2
| reduceRec_3
| reduceRec_4
| reduceQuotRec_1
| reduceQuotRec_2
| reduceQuotRec_3
deriving Inhabited, BEq, Repr


inductive ReduceMatcherResult where
  | reduced (val : CExpr)
  | stuck   (val : CExpr)
  | notMatcher
  | partialApp
deriving Inhabited, BEq, Repr


inductive ArgType where
| ofCExpr (_ : CExpr)
| ofList (_ : List CExpr)
| ofName (_ : Name)
| ofListName (_ : List Name)
| ofNat (_ : Nat)
| ofBinInfo (_ : BinderInfo)
| ofLevel (_ : Level)
| ofListLevel (_ : List Level)
| ofReduceMatcherResult (_ : ReduceMatcherResult)
| ofConstructorVal (_ : ConstructorVal)
| ofMatcherInfo (_ : MatcherInfo)
| ofInductiveVal (_ : InductiveVal)
| ofcRecursorVal (_ : cRecursorVal)
| ofQuotVal (_ : QuotVal)
deriving Inhabited, BEq, Repr


structure FlowState where
  insts : List (FlowType × List CExpr) -- instruction and bvarCtx
  args : List ArgType
deriving Inhabited, BEq, Repr

def FailedState : FlowState := ⟨[],[]⟩

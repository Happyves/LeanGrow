
import LeanGrow.F.Data.CExpr.ReduceInferMuggle.Whnf
import LeanGrow.F.Data.CExpr.ReduceInferMuggle.Infer


open Lean


partial def Flow (fctx : FixCtx) (st: FlowState) : FlowState :=
  match st.insts with
  | [] => st
  | nx :: _ =>
    match nx.1 with
    | .Whnf_1 => Flow fctx (Whnf_1 st)
    | .Whnf_2 => Flow fctx (Whnf_2 fctx st)
    | .Whnf_3 => Flow fctx (Whnf_3 st)
    | .Whnf_4 => Flow fctx (Whnf_4 fctx st)
    | .InferType_1 => Flow fctx (InferType_1 fctx st)
    | .cInferAppType_1 => Flow fctx (cInferAppType_1 st)
    | .cInferAppType_2 => Flow fctx (cInferAppType_2 st)
    | .cInferAppType_3 => Flow fctx (cInferAppType_3 st)
    | .cInferProjType_1 => Flow fctx (cInferProjType_1 st)
    | .cInferProjType_2 => Flow fctx (cInferProjType_2 fctx st)
    | .cInferProjType_3 => Flow fctx (cInferProjType_3 st)
    | .cInferProjType_4 => Flow fctx (cInferProjType_4 st)
    | .cInferLambdaType_1 => Flow fctx (cInferLambdaType_1 st)
    | .cInferLambdaType_2 => Flow fctx (cInferLambdaType_2 st)
    | .getLevel_1 => Flow fctx (getLevel_1 st)
    | .getLevel_2 => Flow fctx (getLevel_2 st)
    | .cInferForallType_1 => Flow fctx (cInferForallType_1 st)
    | .cInferForallType_2 => Flow fctx (cInferForallType_2 st)
    | .cInferForallType_3 => Flow fctx (cInferForallType_3 st)
    | .cInferForallType_4 => Flow fctx (cInferForallType_4 st)
    | .cInferForallType_5 => Flow fctx (cInferForallType_5 st)
    | .myForallBoundedTelescope_1 => Flow fctx (myForallBoundedTelescope_1 st)
    | .myForallBoundedTelescope_2 => Flow fctx (myForallBoundedTelescope_2 st)
    | .reduceMatcher?_1 => Flow fctx (reduceMatcher?_1 fctx st)
    | .reduceMatcher?_2 => Flow fctx (reduceMatcher?_2 st)
    | .reduceMatcher?_3 => Flow fctx (reduceMatcher?_3 st)
    | .reduceMatcher?_4 => Flow fctx (reduceMatcher?_4 st)
    | .toCtorWhenK_1 => Flow fctx (toCtorWhenK_1 st)
    | .toCtorWhenK_2 => Flow fctx (toCtorWhenK_2 fctx st)
    | .toCtorWhenStructure_1 => Flow fctx (toCtorWhenStructure_1 fctx st)
    | .toCtorWhenStructure_2 => Flow fctx (toCtorWhenStructure_2 st)
    | .reduceRec_1 => Flow fctx (reduceRec_1 st)
    | .reduceRec_2 => Flow fctx (reduceRec_2 st)
    | .reduceRec_3 => Flow fctx (reduceRec_3 st)
    | .reduceRec_4 => Flow fctx (reduceRec_4 st)
    | .reduceQuotRec_1 => Flow fctx (reduceQuotRec_1 st)
    | .reduceQuotRec_2 => Flow fctx (reduceQuotRec_2 st)
    | .reduceQuotRec_3 => Flow fctx (reduceQuotRec_3 fctx st)


def CExpr.whnf (fctx : FixCtx) (on : CExpr) : CExpr :=
  let ⟨_, args⟩ := Flow fctx ⟨[(.Whnf_1,[])], [.ofCExpr on]⟩
  match  args with
  | .ofCExpr res :: _ => res
  | _ => .failed

def CExpr.inferType (fctx : FixCtx) (on : CExpr) : CExpr :=
  let ⟨_, args⟩ := Flow fctx ⟨[(.InferType_1,[])], [.ofCExpr on]⟩
  match  args with
  | .ofCExpr res :: _ => res
  | _ => .failed

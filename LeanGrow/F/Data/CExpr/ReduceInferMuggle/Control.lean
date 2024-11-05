
import LeanGrow.F.Data.CExpr.ReduceInferMuggle.Whnf
import LeanGrow.F.Data.CExpr.ReduceInferMuggle.Infer
import LeanGrow.F.Utils.Tracing



open Lean


partial def Flow (fctx : FixCtx) (st: FlowState) : FlowState :=
  with_lTrace TraceFlags.off in
  match st.insts with
  | [] => st
  | nx :: _ =>
    match nx.1 with
    | .Whnf_1 => let res := Flow fctx (Whnf_1 st) ; lTrace TraceFlags.zero & s!"Whnf_1\nCall : {repr st}\nReturn:\n{repr res}\n\n" & res
    | .Whnf_2 => let res := Flow fctx (Whnf_2 fctx st) ; lTrace TraceFlags.zero & s!"Whnf_2\nCall : {repr st}\nReturn:\n{repr res}\n\n" & res
    | .Whnf_3 => let res := Flow fctx (Whnf_3 st) ; lTrace TraceFlags.zero & s!"Whnf_3\nCall : {repr st}\nReturn:\n{repr res}\n\n" & res
    | .Whnf_4 => let res := Flow fctx (Whnf_4 st) ; lTrace TraceFlags.zero & s!"Whnf_4\nCall : {repr st}\nReturn:\n{repr res}\n\n" & res
    | .Whnf_5 => let res := Flow fctx (Whnf_5 fctx st) ; lTrace TraceFlags.zero & s!"Whnf_5\nCall : {repr st}\nReturn:\n{repr res}\n\n" & res
    | .InferType_1 => let res := Flow fctx (InferType_1 fctx st) ; lTrace TraceFlags.one & s!"InferType_1\nCall : {repr st}\nReturn:\n{repr res}\n\n" & res
    | .cInferAppType_1 => let res := Flow fctx (cInferAppType_1 st) ; lTrace TraceFlags.two & s!"cInferAppType_1\nCall : {repr st}\nReturn:\n{repr res}\n\n" & res
    | .cInferAppType_2 => let res := Flow fctx (cInferAppType_2 st) ; lTrace TraceFlags.two & s!"cInferAppType_2\nCall : {repr st}\nReturn:\n{repr res}\n\n" & res
    | .cInferAppType_3 => let res := Flow fctx (cInferAppType_3 st) ; lTrace TraceFlags.two & s!"cInferAppType_3\nCall : {repr st}\nReturn:\n{repr res}\n\n" & res
    | .cInferProjType_1 => let res := Flow fctx (cInferProjType_1 st) ; lTrace TraceFlags.three & s!"cInferProjType_1\nCall : {repr st}\nReturn:\n{repr res}\n\n" & res
    | .cInferProjType_2 => let res := Flow fctx (cInferProjType_2 fctx st) ; lTrace TraceFlags.three & s!"cInferProjType_2\nCall : {repr st}\nReturn:\n{repr res}\n\n" & res
    | .cInferProjType_3 => let res := Flow fctx (cInferProjType_3 st) ; lTrace TraceFlags.three & s!"cInferProjType_3\nCall : {repr st}\nReturn:\n{repr res}\n\n" & res
    | .cInferProjType_4 => let res := Flow fctx (cInferProjType_4 st) ; lTrace TraceFlags.three & s!"cInferProjType_4\nCall : {repr st}\nReturn:\n{repr res}\n\n" & res
    | .cInferLambdaType_1 => let res := Flow fctx (cInferLambdaType_1 st) ; lTrace TraceFlags.four & s!"cInferLambdaType_1\nCall : {repr st}\nReturn:\n{repr res}\n\n" & res
    | .cInferLambdaType_2 => let res := Flow fctx (cInferLambdaType_2 st) ; lTrace TraceFlags.four & s!"cInferLambdaType_2\nCall : {repr st}\nReturn:\n{repr res}\n\n" & res
    | .getLevel_1 => let res := Flow fctx (getLevel_1 st) ; lTrace TraceFlags.five & s!"getLevel_1\nCall : {repr st}\nReturn:\n{repr res}\n\n" & res
    | .getLevel_2 => let res := Flow fctx (getLevel_2 st) ; lTrace TraceFlags.five & s!"getLevel_2\nCall : {repr st}\nReturn:\n{repr res}\n\n" & res
    | .cInferForallType_1 => let res := Flow fctx (cInferForallType_1 st) ; lTrace TraceFlags.six & s!"cInferForallType_\nCall : {repr st}\nReturn::\n{repr res}\n\n" & res
    | .cInferForallType_2 => let res := Flow fctx (cInferForallType_2 st) ; lTrace TraceFlags.six & s!"cInferForallType_2\nCall : {repr st}\nReturn:\n{repr res}\n\n" & res
    | .cInferForallType_3 => let res := Flow fctx (cInferForallType_3 st) ; lTrace TraceFlags.six & s!"cInferForallType_3\nCall : {repr st}\nReturn:\n{repr res}\n\n" & res
    | .cInferForallType_4 => let res := Flow fctx (cInferForallType_4 st) ; lTrace TraceFlags.six & s!"cInferForallType_4\nCall : {repr st}\nReturn:\n{repr res}\n\n" & res
    | .cInferForallType_5 => let res := Flow fctx (cInferForallType_5 st) ; lTrace TraceFlags.six & s!"cInferForallType_5\nCall : {repr st}\nReturn:\n{repr res}\n\n" & res
    | .myForallBoundedTelescope_1 => let res := Flow fctx (myForallBoundedTelescope_1 st) ; lTrace TraceFlags.seven & s!"myForallBoundedTelescope_1\nCall : {repr st}\nReturn:\n{repr res}\n\n" & res
    | .myForallBoundedTelescope_2 => let res := Flow fctx (myForallBoundedTelescope_2 st) ; lTrace TraceFlags.seven & s!"myForallBoundedTelescope_2\nCall : {repr st}\nReturn:\n{repr res}\n\n" & res
    | .reduceMatcher?_1 => let res := Flow fctx (reduceMatcher?_1 fctx st) ; lTrace TraceFlags.eight & s!"reduceMatcher?_1\nCall : {repr st}\nReturn:\n{repr res}\n\n" & res
    | .reduceMatcher?_2 => let res := Flow fctx (reduceMatcher?_2 st) ; lTrace TraceFlags.eight & s!"reduceMatcher?_2\nCall : {repr st}\nReturn:\n{repr res}\n\n" & res
    | .reduceMatcher?_3 => let res := Flow fctx (reduceMatcher?_3 st) ; lTrace TraceFlags.eight & s!"reduceMatcher?_3\nCall : {repr st}\nReturn:\n{repr res}\n\n" & res
    | .reduceMatcher?_4 => let res := Flow fctx (reduceMatcher?_4 st) ; lTrace TraceFlags.eight & s!"reduceMatcher?_4\nCall : {repr st}\nReturn:\n{repr res}\n\n" & res
    | .toCtorWhenK_1 => let res := Flow fctx (toCtorWhenK_1 st) ; lTrace TraceFlags.nine & s!"toCtorWhenK_1\nCall : {repr st}\nReturn:\n{repr res}\n\n" & res
    | .toCtorWhenK_2 => let res := Flow fctx (toCtorWhenK_2 fctx st) ; lTrace TraceFlags.nine & s!"toCtorWhenK_2\nCall : {repr st}\nReturn:\n{repr res}\n\n" & res
    | .toCtorWhenStructure_1 => let res := Flow fctx (toCtorWhenStructure_1 fctx st) ; lTrace TraceFlags.ten & s!"toCtorWhenStructure_1\nCall : {repr st}\nReturn:\n{repr res}\n\n" & res
    | .toCtorWhenStructure_2 => let res := Flow fctx (toCtorWhenStructure_2 st) ; lTrace TraceFlags.ten & s!"toCtorWhenStructure_2\nCall : {repr st}\nReturn:\n{repr res}\n\n" & res
    | .reduceRec_1 => let res := Flow fctx (reduceRec_1 st) ; lTrace TraceFlags.eleven & s!"reduceRec_1\nCall : {repr st}\nReturn:\n{repr res}\n\n" & res
    | .reduceRec_2 => let res := Flow fctx (reduceRec_2 st) ; lTrace TraceFlags.eleven & s!"reduceRec_2\nCall : {repr st}\nReturn:\n{repr res}\n\n" & res
    | .reduceRec_3 => let res := Flow fctx (reduceRec_3 st) ; lTrace TraceFlags.eleven & s!"reduceRec_3\nCall : {repr st}\nReturn:\n{repr res}\n\n" & res
    | .reduceRec_4 => let res := Flow fctx (reduceRec_4 st) ; lTrace TraceFlags.eleven & s!"reduceRec_4\nCall : {repr st}\nReturn:\n{repr res}\n\n" & res
    | .reduceQuotRec_1 => let res := Flow fctx (reduceQuotRec_1 st) ; lTrace TraceFlags.twelve & s!"reduceQuotRec_1\nCall : {repr st}\nReturn:\n{repr res}\n\n" & res
    | .reduceQuotRec_2 => let res := Flow fctx (reduceQuotRec_2 st) ; lTrace TraceFlags.twelve & s!"reduceQuotRec_2\nCall : {repr st}\nReturn:\n{repr res}\n\n" & res
    | .reduceQuotRec_3 => let res := Flow fctx (reduceQuotRec_3 fctx st) ; lTrace TraceFlags.twelve & s!"reduceQuotRec_3\nCall : {repr st}\nReturn:\n{repr res}\n\n" & res


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


import LeanGrow.F.Data.CExpr.API
import Lean.Meta.Match

open Lean Meta

#check getMatcherInfoCore?


inductive CExpr_ReduceMatcherResult where
  | reduced (val : Expr)
  | stuck   (val : Expr)
  | notMatcher
  | partialApp


def CExpr.reduceMatcher? (env : Environment) (e : CExpr) : CExpr_ReduceMatcherResult :=
  let (h,args) := CExpr.getApp e
  match h with
  | .const n lvl =>
      match getMatcherInfoCore? env n with
      | .some info =>
            let prefixSz := info.numParams + 1 + info.numDiscrs
            if args.size < prefixSz + info.numAlts
            then
              .partialApp
            else
              match env.find? n with
              |

      | _ => .notMatcher
  | _ => .notMatcher

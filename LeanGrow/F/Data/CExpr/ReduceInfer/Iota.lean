
import LeanGrow.F.Data.CExpr.API
import LeanGrow.F.Data.CExpr.ReduceInfer.Magic
import LeanGrow.F.Data.CExpr.ReduceInfer.BetaZeta
import Lean

open Lean Meta

#check getMatcherInfoCore?


inductive CExpr_ReduceMatcherResult where
  | reduced (val : CExpr)
  | stuck   (val : CExpr)
  | notMatcher
  | partialApp

def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n+2 => (fib (n+1)) + (fib n)

#print fib.match_1

elab "testing" : command => do
  let env ← getEnv
  let ext := Lean.Meta.Match.Extension.extension.getState env
  let f1 := env.find? `fib.match_1
  let f2 := ext.map.find? `fib.match_1
  IO.println s!"{f1.isSome} and {repr f2}"

-- testing




def myForallBoundedTelescope (gnodeTypes : List (Array CExpr)) (gnodeTypesHandler : Nat → (Nat × Nat))
  (ltxTypes : List (Array EmbedData)) (current : Option (Array EmbedData))
  (cstData : CTrie CstInfo) (bvarCtx : List CExpr)
  (auxAppType : CExpr) : Nat → CExpr × List CExpr
  | 0 => (auxAppType, bvarCtx)
  | n+1 =>
    match auxAppType with
    | .forallE _ t b _ => myForallBoundedTelescope gnodeTypes gnodeTypesHandler ltxTypes current cstData (t :: bvarCtx) b n
    | _ =>
        let tryharder := cexprWhnf gnodeTypes gnodeTypesHandler ltxTypes current cstData bvarCtx auxAppType
        match tryharder with
        | .forallE _ t b _ => myForallBoundedTelescope gnodeTypes gnodeTypesHandler ltxTypes current cstData (t :: bvarCtx) b n
        | _ => (.failed, []) -- because we don't expect failure ??


def CExpr.reduceMatcher? (gnodeTypes : List (Array CExpr)) (gnodeTypesHandler : Nat → (Nat × Nat))
  (ltxTypes : List (Array EmbedData)) (current : Option (Array EmbedData))
  (cstData : CTrie CstInfo) (bvarCtx : List CExpr)
  (e : CExpr) : CExpr_ReduceMatcherResult :=
  let (h,args) := CExpr.getApp e
  match h with
  | .const n lvl =>
      match cstData.find? n.toString with
      | .some (.mat paras _ val info) =>
            let prefixSz := info.numParams + 1 + info.numDiscrs
            if args.length < prefixSz + info.numAlts
            then
              .partialApp
            else
              let f := CExpr.instantiateLevelParams val paras lvl
              let auxApp := CExpr.mkApp f (args.take (prefixSz))
              let auxAppType := cexprInferType gnodeTypes gnodeTypesHandler ltxTypes current cstData bvarCtx auxApp
              let (_,BV) := myForallBoundedTelescope gnodeTypes gnodeTypesHandler ltxTypes current cstData bvarCtx auxAppType info.numAlts
              let auxAppNew := cexprWhnf gnodeTypes gnodeTypesHandler ltxTypes current cstData
                BV (CExpr.mkApp auxApp ((List.range info.numAlts).map (CExpr.bvar)).reverse)
              let (H,AS) := CExpr.getApp auxAppNew
              match H with
              | .bvar I =>
                  let result := CExpr.mkApp (args.get! (prefixSz + (info.numAlts - 1 - I))) AS
                  let result' := CExpr.mkApp result (args.drop (prefixSz + info.numAlts))
                  .reduced (CExpr.beta result')
              | _ => .stuck auxApp
      | _ => .notMatcher
  | _ => .notMatcher


#print Nat.add.eq_1

#check (1+1)

#check Subarray



/-
Copyright (c) 2026 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/


import LeanGrow.Src.SampleGenScore.Delab.Basic
import LeanGrow.Src.SampleGenScore.Delab.Rewrite
import LeanGrow.Src.SampleGenScore.Delab.Subst
import LeanGrow.Src.SampleGenScore.Delab.ContraExFalso
import LeanGrow.Src.SampleGenScore.Delab.ObtainRcasesBycases
import LeanGrow.Src.SampleGenScore.Delab.Matcher
import LeanGrow.Src.SampleGenScore.Delab.Simp
import LeanGrow.Src.SampleGenScore.Delab.CongrConvert
import LeanGrow.Src.SampleGenScore.Delab.Calc
import LeanGrow.Src.SampleGenScore.Delab.WfBrec

open Lean Meta



def delabSample
  (preProcessed : CTrie SimpCongrTheorem)
  (e : Expr) (l1 : LocalContext) (l2 : LocalInstances)
  : MetaM (Prod5 (List FVarId) (List SubProof) (Option Expr) LocalContext LocalInstances) := do
  mtracing
  mtrace on .zero with s!" looking at  {← PpExpr e l1 l2}"
  match e with
  | .app .. =>
    let appH := e.getAppFn'
    let appA := e.getAppArgs
    let .mk rwlif rwRes delZet l1 l2 ← delabSample_Rewrite_core appH appA l1 l2
    match rwRes with
    | .some rwRes =>
      mtrace on .zero with s!" success of rw with:\n · Types : {← rwRes.mapM (fun x => do PpExpr (← InferType x l1 l2) l1 l2)} \n · Terms : {← rwRes.mapM (fun x => do PpExpr x l1 l2)}"
      return .mk rwlif (rwRes.map .raw) delZet l1 l2
    | .none =>
      let simpR ← delab_simpGoal l1 l2 preProcessed e [] #[]
      match simpR with
      | .some l1 l2 simpRes _ _ nt =>
        mtrace on .zero with s!" success of simp"
        return .mk [] [.simp (cleanBetaTopTypes simpRes ) nt (e.getFVarIds)] .none l1 l2
      | .none =>
        let .mk congLif congRes l1 l2 ← delabSample_CongrConvert_core e l1 l2
        match congRes with
        | .some R =>
          mtrace on .zero with s!" success of congr with:\n · Types : {← R.mapM (fun x => do PpExpr (← InferType x l1 l2) l1 l2)} \n · Terms : {← R.mapM (fun x => do PpExpr x l1 l2)}"
          return .mk congLif (R.map .raw) .none l1 l2
        | .none =>
          let .mk indRes l1 l2 ← delabSample_ObtRCaseIndCase_core e l1 l2
          match indRes with
          | .some indRes =>
            mtrace on .zero with s!" success of ind with:\n · Types : {← indRes.mapM (fun x => do PpExpr (← InferType x l1 l2) l1 l2)} \n · Terms : {← indRes.mapM (fun x => do PpExpr x l1 l2)}"
            return .mk [] (indRes.map .raw) .none l1 l2
          | .none =>
            let .mk substRes l1 l2 ← delabSample_subst_core appH appA l1 l2
            match substRes with
            | .some substRes=>
              mtrace on .zero with s!" success of subst with:\n · Types : {← substRes.mapM (fun x => do PpExpr (← InferType x l1 l2) l1 l2)} \n · Terms : {← substRes.mapM (fun x => do PpExpr x l1 l2)}"
              return .mk [] (substRes.map .raw) .none l1 l2
            | .none =>
              let resCon ← delabSample_Contradiction_core appH appA l1 l2
              match resCon with
              | .some l =>
                  mtrace on .zero with s!" success of contra"
                  return .mk [] (l.map .raw) .none l1 l2
              | .none =>
                let resEF ← delabSample_ExFalso_core appH appA
                match resEF with
                | .some r =>
                  mtrace on .zero with s!" success of exfalso"
                  return .mk [] [.raw r] .none l1 l2
                | .none =>
                    let resNC ← delabSample_noConfusion_core appH appA l1 l2
                    match resNC with
                    | .some l =>
                        mtrace on .zero with s!" success of noConfusion"
                        return .mk [] (l.map .raw) .none l1 l2
                    | .none =>
                      let resAC ← delabSample_Acyclic_core appH appA
                      match resAC with
                      | .some l =>
                          mtrace on .zero with s!" success of acyclic"
                          return .mk [] ([.raw l]) .none l1 l2
                      | .none =>
                        let .mk resInj l1 l2 ← delabSample_Injection_core e l1 l2
                        match resInj with
                        | .some l =>
                            mtrace on .zero with s!" success of injection"
                            return .mk [] (l.map .raw) .none l1 l2
                        | .none =>
                            let .mk resMat l1 l2 ← delabSample_Matcher_core appH appA l1 l2
                            match resMat with
                            | .some l =>
                                mtrace on .zero with s!" success of matcher"
                                return .mk [] (l.map .raw) .none l1 l2
                            | .none =>
                                let wfbrec ← delabSample_WfBrec_core appH
                                if wfbrec
                                then
                                  mtrace on .zero with s!" success of wf-induction or brec-induciton"
                                  return .mk [] [] .none l1 l2
                                else
                                  let resCalc ← delabSample_Calc_core appH appA
                                  match resCalc with
                                  | .some resCalc =>
                                    mtrace on .zero with s!" success of calc"
                                    return .mk [] (resCalc.map .raw) .none l1 l2
                                  | _ =>
                                    let .mk lif sub delZet l1 l2 ← delabSample_AssertDefineRevert_core appH appA l1 l2
                                    mtrace on .zero with s!" success of revert ; rervert :\n · Types : {← sub.mapM (fun x => do PpExpr (← InferType x l1 l2) l1 l2)} \n · Terms : {← sub.mapM (fun x => do PpExpr x l1 l2)}\n · lifted : {repr lif}"
                                    return .mk lif (sub.map .raw) delZet l1 l2
  | .letE n t v b _ =>
    let .mk lif sub l1 l2 ← delabSample_HaveLet_core n t v b l1 l2
    mtrace on .zero with s!" have/let :\n · Types : {← PpExpr (← InferType sub l1 l2) l1 l2} \n · Terms : {← PpExpr sub l1 l2}\n · lifted : {repr lif}"
    return .mk (match lif with | .some fv => [fv] | _ => []) ([.raw sub]) .none l1 l2
  | .lam .. =>
    let .mk resInj l1 l2 ← delabSample_Injection_core e l1 l2
    match resInj with
    | .some l =>
        mtrace on .zero with s!" success of injection"
        return .mk [] (l.map .raw) .none l1 l2
    | .none =>
        return .mk [] [] .none l1 l2
  | .fvar .. =>
    return .mk [] [] (.some e) l1 l2
  | _ =>
    return .mk [] [] .none l1 l2 -- todo

#check 1

-- #exit

def delabDig
  (preProcessed : CTrie SimpCongrTheorem)
  (e : Expr) (l1 : LocalContext) (l2 : LocalInstances)
  : MetaM (Prod6 (Option Expr) (List FVarId) (List SubProof) (List SubProof) LocalContext LocalInstances) := do
  mtracing
  mtrace on .zero with s!" looking at  {← PpExpr e l1 l2}"
  match e with
  | .app .. =>
    let appH := e.getAppFn'
    let appA := e.getAppArgs
    let rwRes ← delabDig_Rewrite_core appH appA l1 l2
    match rwRes with
    | .some rwRes =>
      mtrace on .zero with s!" success of rw with:\n · Types : {← rwRes.mapM (fun x => do PpExpr (← InferType x l1 l2) l1 l2)} \n · Terms : {← rwRes.mapM (fun x => do PpExpr x l1 l2)}"
      return .mk .none [] (rwRes.map .raw) [] l1 l2
    | .none =>
      let simpR ← delab_simpGoal l1 l2 preProcessed e [] #[]
      match simpR with
      | .some l1 l2 simpRes simpLift extL nt =>
        mtrace on .zero with s!" success of simp"
        let usedFv := (e.getFVarIds)
        let haves := simpLift.foldl (fun x y => (SubProof.simp (cleanBetaTopTypes y) .none usedFv) :: x) []
        let haves := extL.foldl (fun x y => (.raw y) :: x) haves
        return .mk .none [] [.simp (cleanBetaTopTypes simpRes) nt usedFv] haves l1 l2
      | .none =>
        let .mk congLif congRes l1 l2 ← delabDig_CongrConvert_core e l1 l2
        match congRes with
        | .some R =>
          mtrace on .zero with s!" success of congr with:\n · Types : {← R.mapM (fun x => do PpExpr (← InferType x l1 l2) l1 l2)} \n · Terms : {← R.mapM (fun x => do PpExpr x l1 l2)}"
          return .mk .none [] (R.map .raw) (congLif.map .raw) l1 l2
        | .none =>
          let .mk indRes l1 l2 ← delabDig_ObtRCaseIndCase_core e l1 l2
          match indRes with
          | .some indRes =>
            mtrace on .zero with s!" success of ind with:\n · Types : {← indRes.mapM (fun x => do PpExpr (← InferType x l1 l2) l1 l2)} \n · Terms : {← indRes.mapM (fun x => do PpExpr x l1 l2)}"
            return .mk .none [] (indRes.map .raw) [] l1 l2
          | .none =>
            let .mk substRes l1 l2 ← delabSample_subst_core appH appA l1 l2
            match substRes with
            | .some substRes =>
              mtrace on .zero with s!" success of subst with:\n · Types : {← substRes.mapM (fun x => do PpExpr (← InferType x l1 l2) l1 l2)} \n · Terms : {← substRes.mapM (fun x => do PpExpr x l1 l2)}"
              return .mk .none [] (substRes.map .raw) [] l1 l2
            | .none =>
              let resCon ← delabSample_Contradiction_core appH appA l1 l2
              match resCon with
              | .some l =>
                  mtrace on .zero with s!" success of contra"
                  return .mk .none [] (l.map .raw) [] l1 l2
              | .none =>
                let resEF ← delabSample_ExFalso_core appH appA
                match resEF with
                | .some r =>
                  mtrace on .zero with s!" success of exfalso"
                  return .mk .none [] [.raw r] [] l1 l2
                | .none =>
                    let resNC ← delabSample_noConfusion_core appH appA l1 l2
                    match resNC with
                    | .some l =>
                        mtrace on .zero with s!" success of noconf"
                        return .mk .none [] (l.map .raw) [] l1 l2
                    | .none =>
                      let resAC ← delabSample_Acyclic_core appH appA
                      match resAC with
                      | .some l =>
                          mtrace on .zero with s!" success of acyclic"
                          return .mk .none [] ([.raw l]) [] l1 l2
                      | .none =>
                        let .mk resInj l1 l2 ← delabSample_Injection_core e l1 l2
                        match resInj with
                        | .some l =>
                            mtrace on .zero with s!" success of injection"
                            return .mk .none [] (l.map .raw) [] l1 l2
                        | .none =>
                            let .mk resMat l1 l2 ← delabDig_Matcher_core appH appA l1 l2
                            match resMat with
                            | .some l =>
                                mtrace on .zero with s!" success of match"
                                return .mk .none [] (l.map .raw) [] l1 l2
                            | .none =>
                                let .mk resWfB l1 l2 ← delabDig_WfBrec_core [] appH appA l1 l2
                                match resWfB with
                                | .some br wfbLif =>
                                  return .mk .none wfbLif (br.map .raw) [] l1 l2
                                | _ =>
                                  let resCalc ← delabSample_Calc_core appH appA
                                  match resCalc with
                                  | .some resCalc =>
                                    mtrace on .zero with s!" success of calc"
                                    return .mk .none [] (resCalc.map .raw) [] l1 l2
                                  | _ =>
                                    let .mk lif sub haves l1 l2 ← delabDig_AssertDefineRevert_core appH appA l1 l2
                                    mtrace on .zero with s!" rervert :\n · Types : {← sub.mapM (fun x => do PpExpr (← InferType x l1 l2) l1 l2)} \n · Terms : {← sub.mapM (fun x => do PpExpr x l1 l2)}\n · lifted : {repr lif}"
                                    return .mk .none lif (sub.map .raw) (haves.map .raw) l1 l2
  | .letE n t v b _ =>
    let .mk lif sub haves l1 l2 ← delabDig_HaveLet_core n t v b l1 l2
    mtrace on .zero with s!" have/let :\n · Types : {← PpExpr (← InferType sub l1 l2) l1 l2} \n · Terms : {← PpExpr sub l1 l2}\n · lifted : {repr lif}"
    return .mk (.some t) (match lif with | .some fv => [fv] | _ => []) ([.raw sub]) (match haves with | .some e => [.raw e] | _ => []) l1 l2
  | .lam .. =>
    let .mk resInj l1 l2 ← delabSample_Injection_core e l1 l2
    match resInj with
    | .some l =>
        mtrace on .zero with s!" success of injection"
        return .mk .none [] (l.map .raw) [] l1 l2
    | .none =>
        return .mk .none [] [] [] l1 l2
  | _ =>
    return .mk .none [] [] [] l1 l2 -- todo


#check 1



partial def delabTopBack
  (preProcessed : CTrie SimpCongrTheorem) (conjable : CTrie (List Nat))
  (e : Expr) (l1 : LocalContext) (l2 : LocalInstances) (havelift : List FVarId)
  : MetaM (Prod4 (List FVarId) SampleData LocalContext LocalInstances) := do
  mtracing
  mtrace on .zero with s!" looking at  {← PpExpr e l1 l2}"
  match e with
  | .app .. =>
    let appH := e.getAppFn'
    let appA := e.getAppArgs
    let rwRes ← delabSample_Rewrite_topBack conjable appH appA l1 l2
    match rwRes with
    | .none =>
      let simpR ← delab_simpGoal l1 l2 preProcessed e [] #[]
      let simpS ← (do
        match simpR with
        | .some l1 l2 simpRes _ _ _ =>
          match ← simpProof_topDelab simpRes with
          | .some x y => return OptionProd4.some l1 l2 x y
          | .none => return .none
        | .none => return .none)
      match simpS with
      | .some l1 l2 lif n =>
        mtrace on .zero with s!" success of simp with thm {n}"
        return .mk (lif ++ havelift) .none l1 l2
        -- **Debt** we used to report `.thm n`, but in special cases
        -- the goal has dons't match the theorems result...
        -- For example, we got a `false_and` at at goal that wasn't False,
        -- because simp uses `False.elim`, in List.injOn_insertIdx_index_of_notMem
      | .none =>
        let .mk congLif congRes l1 l2 ← delabSample_CongrConvert_core e l1 l2
        match congRes with
        | .some _ =>
          mtrace on .zero with s!" success of congr"
          return .mk (congLif ++havelift) .none l1 l2
        | .none =>
          let indRes ← delabSample_ObtRCaseIndCase_topBack e
          match indRes with
          | .none =>
            let .mk substRes l1 l2 ← delabSample_subst_core appH appA l1 l2
            match substRes with
            | .some _ =>
              mtrace on .zero with s!" success of subst, bad sample"
              return .mk havelift .none l1 l2
            | .none =>
              let resCon ← delabSample_Contradiction_core appH appA l1 l2
              match resCon with
              | .some _ =>
                  mtrace on .zero with s!" success of contra"
                  return .mk havelift .none l1 l2
              | .none =>
                let resEF ← delabSample_ExFalso_core appH appA
                match resEF with
                | .some _ =>
                  mtrace on .zero with s!" success of exfalso"
                  return .mk havelift .none l1 l2
                | .none =>
                    let resNC ← delabSample_noConfusion_core appH appA l1 l2
                    match resNC with
                    | .some _ =>
                        mtrace on .zero with s!" success of noConf"
                        return .mk havelift .none l1 l2
                    | .none =>
                      let resAC ← delabSample_Acyclic_core appH appA
                      match resAC with
                      | .some _ =>
                          mtrace on .zero with s!" success of acyclic"
                          return .mk havelift .none l1 l2
                      | .none =>
                        let .mk resInj l1 l2 ← delabSample_Injection_core e l1 l2
                        match resInj with
                        | .some _ =>
                            mtrace on .zero with s!" success of injection"
                            return .mk havelift .none l1 l2
                        | .none =>
                          let .mk resMat l1 l2 ← delabSample_Matcher_top appH l1 l2
                          if resMat
                          then
                            mtrace on .zero with s!" success of matcher"
                            return .mk havelift .none l1 l2
                          else
                            let wfbrec ← delabSample_WfBrec_core appH
                            if wfbrec
                            then
                              mtrace on .zero with s!" success of wf-induction or brec-induciton"
                              return .mk havelift .none l1 l2
                            else
                              let resCalc ← delabSample_Calc_top l1 l2 appH appA
                              match resCalc with
                              | .some resCalc =>
                                mtrace on .zero with s!" success of calc"
                                return .mk havelift resCalc l1 l2
                              | _ =>
                              mtrace on .zero with s!" calling delab for apply & revert"
                              let r ← delabSample_AssertDefineRevert_top conjable appH appA l1 l2
                              return .mk havelift r l1 l2
          | r =>
            mtrace on .zero with s!" success of ind with {repr r}"
            return .mk havelift r l1 l2
    | .some r =>
      mtrace on .zero with s!" success of rw with {repr r}"
      return .mk havelift r l1 l2
  | .letE _ t v b _ =>
    let desambig ← mkFreshId
    let .mk nfv l1 l2 ← WithLetDecl (`lamLetLike ++ desambig) t v l1 l2
    let letB := Expr.instantiateBetaRevRange b 0 1 #[(.fvar nfv)]
    delabTopBack preProcessed conjable letB l1 l2 (nfv :: havelift)
  | .lam .. => throwError "[delabTop] expected to have run lamdaTelescop before"
  | _ =>
    return .mk [] .none l1 l2-- todo

#check 1


def delabTopForw
  (preProcessed : CTrie SimpCongrTheorem)
  (e : Expr) (l1 : LocalContext) (l2 : LocalInstances)
  : MetaM (Prod4 SampleData (List Expr) LocalContext LocalInstances) := do
  mtracing
  mtrace on .zero with s!" looking at  {← PpExpr e l1 l2}"
  match e with
  | .app .. =>
    let appH := e.getAppFn'
    let appA := e.getAppArgs
    let rwRes ← delabSample_Rewrite_topForw appH appA l1 l2
    match rwRes with
    | .none =>
      let simpR ← delab_simpGoal l1 l2 preProcessed e [] #[]
      let simpS ← (do
        match simpR with
        | .some l1 l2 simpRes _ ext _ =>
          match ← simpProof_topDelab simpRes with
          | .some lif n => return OptionProd4.some l1 l2 n (ext.foldl (fun x y => y :: x) (lif.map Expr.fvar))
          | .none => return .none
        | .none => return .none)
      match simpS with
      | .some l1 l2 n ext =>
        mtrace on .zero with s!" success of simp with thm {n}"
        return .mk .none ext l1 l2
        -- refer to TopBack
      | .none =>
        let .mk _ congRes l1 l2 ← delabSample_CongrConvert_core e l1 l2
        match congRes with
        | .some _ =>
          mtrace on .zero with s!" success of congr"
          return .mk .none [] l1 l2
        | .none =>
          let resMat ← delabSample_ObtRCaseIndCase_topForw e
          if resMat
          then
            mtrace on .zero with s!" success of induction"
            return .mk .none [] l1 l2
          else
              let .mk substRes l1 l2 ← delabSample_subst_core appH appA l1 l2
              match substRes with
              | .some _ =>
                mtrace on .zero with s!" success of subst, bad sample"
                return .mk .none [] l1 l2
              | .none =>
                let resCon ← delabSample_Contradiction_core appH appA l1 l2
                match resCon with
                | .some _ =>
                    mtrace on .zero with s!" success of contra"
                    return .mk .none [] l1 l2
                | .none =>
                  let resEF ← delabSample_ExFalso_core appH appA
                  match resEF with
                  | .some _ =>
                    mtrace on .zero with s!" success of exfalso"
                    return .mk .none [] l1 l2
                  | .none =>
                      let resNC ← delabSample_noConfusion_core appH appA l1 l2
                      match resNC with
                      | .some _ =>
                          mtrace on .zero with s!" success of noConf"
                          return .mk .none [] l1 l2
                      | .none =>
                        let resAC ← delabSample_Acyclic_core appH appA
                        match resAC with
                        | .some _ =>
                            mtrace on .zero with s!" success of acyclic"
                            return .mk .none [] l1 l2
                        | .none =>
                          let .mk resInj l1 l2 ← delabSample_Injection_core e l1 l2
                          match resInj with
                          | .some _ =>
                              mtrace on .zero with s!" success of injection"
                              return .mk .none [] l1 l2
                          | .none =>
                              let .mk resMat l1 l2 ← delabSample_Matcher_top appH l1 l2
                              if resMat
                              then
                                mtrace on .zero with s!" success of matcher"
                                return .mk .none [] l1 l2
                              else
                                let wfbrec ← delabSample_WfBrec_core appH
                                if wfbrec
                                then
                                  mtrace on .zero with s!" success of wf-induction or brec-induciton"
                                  return .mk .none [] l1 l2
                                else
                                  let resCalc ← delabSample_Calc_top l1 l2 appH appA
                                  match resCalc with
                                  | .some resCalc =>
                                    mtrace on .zero with s!" success of calc"
                                    return .mk resCalc [] l1 l2
                                  | _ =>
                                    mtrace on .zero with s!" calling delab for apply & revert"
                                    let r ← delabSample_AssertDefineRevert_top .empty appH appA l1 l2
                                    return .mk r [] l1 l2
    | .some .none =>
      mtrace on .zero with s!" recognized rw, but not thm-rw"
      return .mk .none [] l1 l2
    | .some (.some r ini) =>
      mtrace on .zero with s!" success of rw with {repr r}"
      return .mk (.thm r) [ini] l1 l2
  | _ =>
    return .mk .none [] l1 l2-- todo


def delabTopForw_withHyps
  (preProcessed : CTrie SimpCongrTheorem)
  (e : Expr) (l1 : LocalContext) (l2 : LocalInstances)
  : MetaM (Prod4 SampleData (List Expr) LocalContext LocalInstances) := do
  mtracing
  mtrace on .zero with s!" looking at  {← PpExpr e l1 l2}"
  match e with
  | .app .. =>
    let appH := e.getAppFn'
    let appA := e.getAppArgs
    let rwRes ← delabSample_Rewrite_topForw_withHyps appH appA l1 l2
    match rwRes with
    | .none =>
      let simpR ← delab_simpGoal l1 l2 preProcessed e [] #[]
      let simpS ← (do
        match simpR with
        | .some l1 l2 simpRes _ ext _ =>
          match ← simpProof_topDelab simpRes with
          | .some lif n => return OptionProd4.some l1 l2 n (ext.foldl (fun x y => y :: x) (lif.map Expr.fvar))
          | .none => return .none
        | .none => return .none)
      match simpS with
      | .some l1 l2 n ext =>
        mtrace on .zero with s!" success of simp with thm {n}"
        return .mk .none ext l1 l2
        -- refer to TopBack
      | .none =>
        let .mk _ congRes l1 l2 ← delabSample_CongrConvert_core e l1 l2
        match congRes with
        | .some _ =>
          mtrace on .zero with s!" success of congr"
          return .mk .none [] l1 l2
        | .none =>
          let resMat ← delabSample_ObtRCaseIndCase_topForw e
          if resMat
          then
            mtrace on .zero with s!" success of induction"
            return .mk .none [] l1 l2
          else
              let .mk substRes l1 l2 ← delabSample_subst_core appH appA l1 l2
              match substRes with
              | .some _ =>
                mtrace on .zero with s!" success of subst, bad sample"
                return .mk .none [] l1 l2
              | .none =>
                let resCon ← delabSample_Contradiction_core appH appA l1 l2
                match resCon with
                | .some _ =>
                    mtrace on .zero with s!" success of contra"
                    return .mk .none [] l1 l2
                | .none =>
                  let resEF ← delabSample_ExFalso_core appH appA
                  match resEF with
                  | .some _ =>
                    mtrace on .zero with s!" success of exfalso"
                    return .mk .none [] l1 l2
                  | .none =>
                      let resNC ← delabSample_noConfusion_core appH appA l1 l2
                      match resNC with
                      | .some _ =>
                          mtrace on .zero with s!" success of noConf"
                          return .mk .none [] l1 l2
                      | .none =>
                        let resAC ← delabSample_Acyclic_core appH appA
                        match resAC with
                        | .some _ =>
                            mtrace on .zero with s!" success of acyclic"
                            return .mk .none [] l1 l2
                        | .none =>
                          let .mk resInj l1 l2 ← delabSample_Injection_core e l1 l2
                          match resInj with
                          | .some _ =>
                              mtrace on .zero with s!" success of injection"
                              return .mk .none [] l1 l2
                          | .none =>
                              let .mk resMat l1 l2 ← delabSample_Matcher_top appH l1 l2
                              if resMat
                              then
                                mtrace on .zero with s!" success of matcher"
                                return .mk .none [] l1 l2
                              else
                                let wfbrec ← delabSample_WfBrec_core appH
                                if wfbrec
                                then
                                  mtrace on .zero with s!" success of wf-induction or brec-induciton"
                                  return .mk .none [] l1 l2
                                else
                                  let resCalc ← delabSample_Calc_top l1 l2 appH appA
                                  match resCalc with
                                  | .some resCalc =>
                                    mtrace on .zero with s!" success of calc"
                                    return .mk resCalc [] l1 l2
                                  | _ =>
                                    mtrace on .zero with s!" calling delab for apply & revert"
                                    let .mk r a ← delabSample_AssertDefineRevert_top_withHyps appH appA l1 l2
                                    return .mk r a l1 l2
    | .some .none =>
      mtrace on .zero with s!" recognized rw, but not thm-rw"
      return .mk .none [] l1 l2
    | .some (.some r ini) =>
      mtrace on .zero with s!" success of rw with {repr r}"
      return .mk (.thm r) ini l1 l2
  | _ =>
    return .mk .none [] l1 l2-- todo

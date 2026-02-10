
/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import LeanGrowBeta.Data.SetTrie.Specialize
import LeanGrowBeta.Search.IntroTree.Types
import LeanGrowBeta.Search.BackTree.Types
import LeanGrowBeta.Search.Score.Regularisation
import LeanGrowBeta.Core.GeneralisePaIn.Types

import LeanGrowBeta.Core.Induction.Detection
import LeanGrowBeta.Core.Induction.FunctionalInd
import LeanGrowBeta.Core.Induction.ElimInd
import LeanGrowBeta.Core.Induction.StructuralInd

import LeanGrowBeta.Core.Embedding.EmbedQueryBackRW


open Lean Meta


#check 1

structure TacticSupportDataConfig where
  linarithCooldown : Nat
  ccCooldown : Nat
deriving Inhabited, BEq, Repr


structure TacticSupportDataState where
  linarithCooldown : Nat
  ccCooldown : Nat
deriving Inhabited, BEq, Repr


inductive ForwMetaData where
| other
| intro
| std (thmName : String)
| recu (thmName : String)
deriving Inhabited, Repr, BEq


structure BackCandData where
  thmData : ThmFormat
  arg_lvls : Array Level
  todo_lvls : List Nat
  arg_exprs : Array Expr
  todo_expr : ListProd Nat Expr
  targetGoal : Nat
  rwdata : OptionProd3 rwDirs Expr (List FVarId)
  ta : ListProd3 Nat Nat Expr
  la : ListProd3 Nat Nat Level
  md : BackStepMetadata
deriving Inhabited


structure ForwCandData where
  isProp : Bool
  type : Expr
  term : Expr
  UGinds : List Nat
  md : ForwMetaData
deriving Inhabited




structure StatisticsAndTraces where
  randomNats : Array Nat
  failuresWithRecovery : List String
deriving Inhabited, Repr, BEq


structure ScoreType where
  back : Float
  forw : Float
  spe : Float
deriving Inhabited, Repr, BEq


def ForwMetaData.ofBackStepMetadata : BackStepMetadata → ForwMetaData
  | .std n => .std n
  | .recu n => .recu n
  | _ => .other


structure SearchState (IndexColType : Type _) where
  stdForwTimer : Nat := 0
  id_gen_forw : Nat := 0
  id_gen_back : Nat := 0
  id_gen_goal : Nat := 0
  id_gen_uni : Nat := 0
  id_gen_apass : Nat := 0
  cycleAddForw : ListProd Nat Expr
  cycleAddBack : ListProd Nat Expr
  backTree : BackTree
  introTree : IntroTree IndexColType
  uNodes : Array Nat
  goalSpawn : Array (OptionProd Nat Nat)
  unif_assign : Array ((ListProd3 Nat Nat Expr) × (ListProd3 Nat Nat Level))
    -- indexed by uni_id, tnode assignements, level tnode assignements
  unif_claches : ListProd Nat (List Nat)
  depsCache : Array (List LocalDecl)
    -- indexed by u-g-inds ; contains decls that dependen on the indexes ugnode ; needed for induction and rw

  thm_data : Array ThmFormat
  thmData : CTrie (Array ThmFormat)
  stdBackPaIn : PaIn IndexColType
  stdForwSetTrie : SetTrie ThmFormat (PaIn IndexColType)
  stdForwSetTrie_idxToThmIdx : Array Nat
  rwBackPaIn : PaIn IndexColType
  rwForwPaIn : PaIn IndexColType
  thmNameToHypIdx : CTrie IndexColType
  ugnodeToThmIdx : (RBMap Nat Nat instOrdNat.compare)
  thmIdxToUGnode : (RBMap Nat Nat instOrdNat.compare)
    /- Initially, this should be the data loaded to mirror imports ;
    However, we plan to add local theorems (∀ or = hyps). We should add them
    with a dummy module name in `thmData`, append the thm format to `thm_data`
    and hyps via `stdForwSetTrie_idxToThmIdx` and use the rbmaps to translate,
    if necessary.
    For integration of results comming from local thms, we'll always have to check
    that the integration makes sense, for example that a local ∀-hyp used in forward
    step doesn't have hyp as arg that isn't an ncestor in the IntroTree.
    -/

  id_gen_cand : Nat
  backCandScores : ListProd5 Nat BackCandData Nat ScoreType (List (CSetTrie IndexColType Nat))
    -- cand id, data expected by `embedBackPreIntegrate`, timer, raw score, remaining feature branches
    -- don't forget to add hight depth score to initial score
  forwCandScores : ListProd6 Nat ForwCandData Nat ScoreType (CPaIn IndexColType) (List (CSetTrie IndexColType Nat))
    -- cand id, forw data, timer, raw score, goal-score pain (not supposed to change) remaining feature branches
    -- don't forget to add hight depth score to initial score
  inductCandScores : ListProd6 Nat Nat TargetType Nat Expr Float
    -- cand id, timer, target, taget-goal-id, target-goal-type, score

  forwHeights : Array Nat -- indexed by g-u-ids
  goalHeights : Array Nat -- indexed by goal-ids
  forwDepths : Array depthForwData
  backDepths : Array depthBackData

  forwMetadata : Array ForwMetaData -- indexed by g-u-ids

  -- TODO
  tacticSupportData : TacticSupportDataState
  statisticsAndTraces : StatisticsAndTraces
deriving Inhabited




structure SearchConfig where
  sandboxMode : Bool

  revCountMax : Nat
  sinkRevCutOff : Nat

  addBatchSize : Nat
  splitBatches : Bool
  backBatchSize : Nat
  forwBatchSize : Nat
  induBatchSize : Nat

  regulariser_fH : Float → Nat → Float
  regulariser_bH : Float → Nat → Float
  regulariser_fD : Float → Nat → Float
  regulariser_bD : Float → Nat → Float
  baseLocalThmScore : Float
  sandboxModThmScore : Float
  cachelessThmScore : Float
  customRegulariser_back : Float → Nat → BackCandData → (SearchState (List Nat)) →  Float
  customRegulariser_forw : Float → Nat → ForwCandData → (SearchState (List Nat)) → Float
  customRegulariser_indu : Float → Nat → TargetType → (SearchState (List Nat)) → Float

  thmPatternScores : CTrie (Prod3 (CPaIn (List Nat)) (CSetTrie (List Nat) Nat) (CSetTrie (List Nat) Nat))
  funrecus : CTrie FunRecursorCache
  elimrecus : CTrie (List RecursorCache)
  recuSubpatternScores : CTrie (CPaIn (List Nat))

  default_relevance_timer : Nat
  stdForwPeriod : Nat

  tacticSupport : Bool
  tacticSupportData : TacticSupportDataConfig
deriving Inhabited




abbrev GrowIM (IndexColType : Type _) := ReaderT SearchConfig $ StateRefT (SearchState IndexColType) MetaM

variable {IndexColType : Type _}

@[always_inline]
instance : Monad (GrowIM IndexColType) := let i := inferInstanceAs (Monad (GrowIM IndexColType)); { pure := i.pure, bind := i.bind }

instance {α}: Inhabited (GrowIM IndexColType α) where
  default := fun _ _ => default

abbrev GrowM := GrowIM (List Nat)

instance : MonadLift GrowM MetaM where
  monadLift := fun test => Prod.fst <$> (test default |>.run default)

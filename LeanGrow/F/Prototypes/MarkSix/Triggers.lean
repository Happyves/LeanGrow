

import LeanGrow.F.Prototypes.MarkSix.trTypes


#check 1




def BackGuns : List (FixCtx → TriggerState → CExpr → TriggerState) := []

def pullBackTriggers (init : TriggerState) (fctx : FixCtx) (goal : CExpr) : TriggerState :=
  let rec pow (sofar : TriggerState) : List (FixCtx → TriggerState → CExpr → TriggerState) → TriggerState
    | [] => sofar
    | x :: xs => pow (x fctx sofar goal) xs
  pow init BackGuns


def ForwGuns : List (FixCtx → TriggerState → CExpr → TriggerState) := []

def pullForwTriggers (init : TriggerState) (fctx : FixCtx) (goal : CExpr) : TriggerState :=
  let rec pow (sofar : TriggerState) : List (FixCtx → TriggerState → CExpr → TriggerState) → TriggerState
    | [] => sofar
    | x :: xs => pow (x fctx sofar goal) xs
  pow init ForwGuns


/-
Can't handle the massive debt.
Esstentially, we run these triggers on every new goal and every forward step.
They can produce new goals, new backsteps, new gnodes, unifications etc.
Introduction, reduction and induction should become truggers.
We should reapply triggers on the new goals added by triggers: for example, when
applying induction, we expect the new induction step goal to be a ∀, that we'll
want to run intro on...

-/

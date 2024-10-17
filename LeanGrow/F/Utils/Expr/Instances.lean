

import Lean
import Mathlib

open Lean Elab Term Meta SynthInstance


-- The following corresponds to type-class resolution
#check synthesizeInstMVarCore
-- it is used by other, similar function, such as
#check synthesizeInstMVarCore
-- which in turn is used in the inner workings of the following (look for it in the folder)
#check elabApp

-- Its main work is done by
#check trySynthInstance
-- which is in turn based on
#check synthInstance?
-- There, we see that the first step of typeclass resolution is to look for instances
-- in the local context (instances among the assumptions, essentially), using
#check getLocalInstances
-- If none are found, we bring out the big guns
#check SynthInstance.main

--The type class resolution procedure is explained in https://arxiv.org/pdf/2001.04301.pdf
-- we'll look at the implementation of the procedure explained in this paper

open SynthInstance

-- In the search,
#print GeneratorNode
#print ConsumerNode

-- We'll work in a state monad in which the state stores
#check SynthM
-- the generator stack
#check State.generatorStack
-- the reslover stack
#check State.resumeStack

-- the core function is
#check main
-- which does some processing arround
#check synth
-- Which is repeated cheking of
#check step
-- which tries to return the optional value of
#check getResult

-- In `step`, we try (unless the generator stack is empty)
#check generate
-- until the resolver stack is empty, at which stage we perform
#check resume

-- `generate` will use
#check tryResolve
-- to try the instance of a generator node for showing the goal, possibly creating subgoals
-- which it stores in a cosumer node, which is then stored in the context after some processing, with
#check consume

-- `consume` also produces new subgoals with
#check newSubgoal
-- which may produce nwe generator nodes with
#check mkGeneratorNode?
-- by searching for new instances using
#check getInstances

-- The latter will actually load all declared instances from the environement,
-- which are sttored in a discrimination tree, useing
#check getGlobalInstancesIndex
-- where retireval is done with
#check DiscrTree.getUnify



#check Lean.Declaration


instance myInstance : Inhabited Nat where
  default := 42

#check myInstance



def test_myInstance : CoreM Unit := do
  let .some (info) := (← getEnv).find? `myInstance | throwError "ahh 1"
  let todo :=
    match info with
    | .axiomInfo _ => "axiom"
    | .defnInfo _ => "definition"
    | .thmInfo _ => "thm"
    | _ => "other"
  IO.println todo


#eval test_myInstance


#check DefinitionVal
-- no instances here...

#check Elab.Command.elabDeclaration


#check Frontend.processCommand

#check Environment

#check Lean.Meta.isGlobalInstance

def testinQuery : CoreM Unit := do
  let env ← getEnv
  let isit? := Lean.Meta.isGlobalInstance env `instAddNat --`myInstance
  IO.println isit?

#eval testinQuery

#synth Add Nat

#check instAddNat

#check AddCommMonoid

#check Nat.instAddCommMonoid
-- ↑ infer_instance

--#print Nat.instAddCommMonoid
-- one of the two, probably ↓, causes overflow, as it tries to synthesise a nonexistent instance ?
--#check inferInstance

set_option pp.all true in
#reduce Nat.instAddCommMonoid


#check AddLeftCancelSemigroup.toAddSemigroup

def testinIfToInEnv : CoreM Unit := do
  let env ← getEnv
  let .some i := env.constants.find? `AddLeftCancelSemigroup.toAddSemigroup | throwError "ahh 1"
  match i with
  | .defnInfo _ => IO.println "def"
  | _ => IO.println "other"

#eval testinIfToInEnv
-- interesting... I don't think recusors are stored in env, but projections of instances are

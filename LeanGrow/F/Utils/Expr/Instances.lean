

import Lean

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

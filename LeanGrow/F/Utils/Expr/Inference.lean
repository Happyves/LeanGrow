
import Lean

open Lean Meta

#check inferType
-- often in form ↑, implemented as ↓
#check inferTypeImp


-- For constants,
#check_failure inferConstType
-- gets the `ConstantInfo` and runs `Lean.Expr.instantiateLevelParams` on the type

-- mvars and fvars just get looked up in the context
#check_failure inferFVarType
#check_failure inferMVarType
-- it throws an error if the expression contains a bound variable
-- (because these should occur only in λ or ∀, which are handled separately)

-- lietrals have types
#check Literal.type

-- sorts are just turned into their successor
#check mkLevelSucc


-- For applications, we split them into head and array of args:
#check_failure inferAppType
-- we infer the head type and perform what's in essence the following :
-- get ∀ body, replace bvars by corresponding arg in it.
-- Since the type may, for some cursed reason be something like `∀ x, (fun _ => ∀ y, z)  42`
-- we must try to reduce with `whnf`, instanciating before this, as instanciation affects bvar order...


-- For projections,
#check_failure inferProjType
-- the type of the body is recursively infered (we expect it to be a structure) and reduced with whnf.
-- We then get the head of that type, which we expect to be an inductive one with a single constructor,
-- which we extract via:
#check matchConstStruct
-- we then check that the number of parameters from the induct-info matches that in the actual expression.
-- Next, we consider the type of the constructor applied to the parameters, which we infer via `inferAppType`
-- It should be of the form `mk : ∀ x, ∀ y, ...` where the ∀ types are the types of the projections
-- so we repeatedly normlise with `whnf`, extract the body, instantiate it with the projection corresponding
-- to that binder (ex.: `∀ x : α, ∀ h : p x, Sub α p` for subtypes), until we've arrived at the desired index,
-- at which stage we stop, normlise with `whnf`, and return the *type* of the forall.
-- Note the administartive use of:
#check Lean.Expr.consumeTypeAnnotations


-- λ and let are both handled by:
#check_failure inferLambdaType
-- It runs
#check lambdaLetTelescope
-- with calls to inferType. Then, with all the types infered, it makes a ∀ telescope with
#check mkForallFVars
-- The process can be described as adding free variables to the context and replacing the bvars
-- in the body.

-- ∀ is similar to λ, and is at
#check_failure inferForallType
-- we essentiall apply
#check getLevel
-- which infers the type, reduces it and expects a sort,
-- on the binders and head. Then we fold
#check mkLevelIMax'
-- to get successive imaxes of levels, and clean up the final level with
#check Level.normalize
-- (to that we have to infer the type of x before feeding it to `getLevel`, as its an fvar)


-- note that the file also contains a lot of API on other inference tasks, like:
#check isProp

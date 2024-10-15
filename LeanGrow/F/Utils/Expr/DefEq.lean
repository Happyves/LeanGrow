/-
Copyright (c) 2024 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import Lean

open Lean Meta


/- In Lean, unification is directly linked to testing for definitional equality.
An important consequence is that testing for defeq may assign metavariables, so one
should use some form of backtracking if one wishes to deal with unification failure.
There are defeq from the C++ kernel:-/
#check isDefEq
-- which is based on
#check isExprDefEqAux
-- And a seemingly experimental version written in Lean itself
#check isExprDefEqAuxImpl
-- which we'll study

-- The procedure first tries two easier and faster versions
#check_failure isDefEqQuick -- private
#check_failure isDefEqProofIrrel -- private
-- These may return a result signalling inconclusiveness, at which state we bring out the big guns
-- First we repeat whnf reduction until none is possible, and then instantiate metavariables, with
#check whnfCore
#check instantiateMVars
-- We maintain a cache that we quieriy via
#check_failure mkCacheKey --private
#check_failure getCachedResult --private
-- If this fails, we get the hammer:
#check_failure isExprDefEqExpensive --private


-- `isDefEqProofIrrel` will check if we're dealing with propositions using
#check isProofQuick
-- after which it infers the propositions with the C++ Kernel's
#check inferType
-- followed by a test for equality of these proposition with the C++ Kernel's
#check isExprDefEqAux
-- By proof irrelevance (we consider two proofs of the same proposition equal), the two
-- proofs should be equal if their proposition-types are.
-- Note to self : It seems that proof irrelevance is encoded in the C++ Kernel type-checking ???

-- `isDefEqQuick` is a more involved one.
-- It first gets rid of *useless* `let` delcarations with
#check_failure consumeLet --private
-- and then tries syntactic equality for literals, equality for sorts with
#check isLevelDefEqAux
-- equality for expressions with binders via
#check_failure isDefEqBindingAux -- private
-- which is again based on the C++ Kernel's defeq
-- and finally it also tries syntactic equality for non `let` bound fvars and `isDefEqProofIrrel` if the latter fails

-- In other cases it runs
#check_failure isDefEqQuickOther --private
-- This will test for equality up to eta reduction (f = fun x => f x) with
#check_failure etaEq -- private
-- ↑ essentially goes through binders and checks that the final body is a application evaluated
-- in bound variables in the right order, with a head not containing any free variables

-- In another step, handles the cases of `?m a₁ ... aₙ = v` via
#check_failure processAssignment --private
-- which is based on
#check checkAssignment
-- which tries to set `?m := fun fvars => v[fvars]` so that `?m a₁ ... aₙ = v` works out


-- Finally, we take a quick look at `isExprDefEqExpensive`
-- It tries a lot of different methods
#check_failure isDefEqEta
#check_failure isDefEqDelta

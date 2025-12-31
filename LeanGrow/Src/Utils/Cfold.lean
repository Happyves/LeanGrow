/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import Lean.Elab.SyntheticMVars
import Lean.Meta.Reduce

open Lean Elab

elab "cfold " t:term : term => do
  let e ← Term.elabTermAndSynthesize t  .none
  Meta.reduce e

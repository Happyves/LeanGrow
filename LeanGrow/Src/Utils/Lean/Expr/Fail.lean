
/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import Lean.Expr

open Lean

def failExpr (err : String) : Expr := .lit (.strVal err)

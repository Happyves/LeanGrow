/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import LeanGrow.Src.Search.Types

open Lean Meta

@[inline]
def updateDepsCachesPreCompNoMonad {IndexColType : Type _} (l1 : LocalContext) (l2 : LocalInstances)
  (gu_fv : FVarId)  (st : SearchState IndexColType) : MetaM (SearchState IndexColType) := do
  return {st with depsCache := ← DepCache.addGU st.depsCache gu_fv l1 l2}

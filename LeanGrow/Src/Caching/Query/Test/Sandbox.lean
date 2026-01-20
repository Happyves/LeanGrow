
import LeanGrow.Src.Caching.Query.Sandbox

open Lean Meta


def inSandboxS_rwBackPaIn_pp
  (thms : Array Name) : MetaM Unit :=
    inSandboxS thms <| fun _ data => do
      let inds := data.rwBackPaIn.getIndicesS
      for i in inds do
        let thm := data.thm_data[i.toNat]!
        thm.mctx.loadNoCo
      let res ← data.rwBackPaIn.ppS (← getLCtx) (← getLocalInstances) [] 0
      IO.println res

#check 1

def inSandboxS_stdBackPaIn_pp
  (thms : Array Name) : MetaM Unit :=
    inSandboxS thms <| fun _ data => do
      let inds := data.stdBackPaIn.getIndicesS
      for i in inds do
        let thm := data.thm_data[i.toNat]!
        thm.mctx.loadNoCo
      let res ← data.stdBackPaIn.ppS (← getLCtx) (← getLocalInstances) [] 0
      IO.println res

#check 1


def sandbox_1 := #[`Nat.add_comm, `Nat.zero_add, `Nat.succ_add]

-- tracing_mode .std
-- tracing_flags [(`buildCachDataForCore.inner, TracingFlags.all), (`buildCachDataForCore.go, TracingFlags.all)]

-- #eval inSandboxS_rwBackPaIn_pp sandbox_1

-- #eval inSandboxS_stdBackPaIn_pp sandbox_1

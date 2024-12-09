
import Qq
import Lean

import Mathlib.Algebra.Group.Defs

#check 1

open Qq

#eval q(List.append [1,2])

#eval q(@add_comm Rat)
#eval q(@add_comm (List Type))
#eval q(Rat)

open Lean

#check ConstantInfo


def test (n : Name) : CoreM Unit := do
  let env ← getEnv
  let data := env.constants.find! n
  IO.print s!"{repr data.type}"

#eval test `add_comm

#eval test `Rat

def add_comm_spe := @add_comm ℤ

def test' (n : Name) : CoreM Unit := do
  let env ← getEnv
  let data := env.constants.find! n
  IO.print s!"{repr data.value!}"

#eval test' `add_comm_spe

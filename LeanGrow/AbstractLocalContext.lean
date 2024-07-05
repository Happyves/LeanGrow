
import Lean

open Lean


/-
The idea is to abstract types/sorts and instances on them, in a local context.
To perform `grow` we first generalise the local context, so that theorems that are
polymorphic in nature may apply. Seeing as in the final output, we only compose a
theorem with the default arguments, this will work in the initial local context, as
implicit arguments and instances will be synthesied anyway.
-/

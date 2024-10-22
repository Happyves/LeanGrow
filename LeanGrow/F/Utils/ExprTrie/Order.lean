
import Lean.Level

open Lean

/-
make ordring on them, so that queries become faster (?), simlarly to what we did for Tries


or instead, instead of list of branch types, make an array of the type `Array (Option ExprTrieType)`
who's size will be exactly the number of constructors of the branch type, so that we can refer to a
branch type by an index and checking that its entry isn't `.none`, rather then by searching a list.
Since all entries of the array must have the same type, we use a type that encompasses all the data
of branch types, and uses default values at the entries it deosnt have
-/

structure ExprTrieType where
  idx : Nat
  tag : Nat
  indices : List Nat
  level : Level
  name : Name
  link_1 : Nat
  link_2 : Nat
  link_3 : Nat

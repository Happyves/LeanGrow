
/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

partial def String.joinA (a : Array String) : String :=
  let rec go (i : Nat) (sofar : String) : String :=
    if i == 0 then (a[0]! ++ sofar) else go (i-1) (a[i]! ++ sofar)
  go (a.size - 1) ""


partial def String.intercalateA (s : String) (a : Array String) : String :=
  let rec go (i : Nat) (sofar : String) : String :=
    if i == 0 then (a[0]! ++ s ++ sofar) else go (i-1) (a[i]! ++ s ++ sofar)
  go (a.size - 1) ""


partial def String.isSuffixOf (suf main : String) : Bool :=
  let rec go (i j : Nat) : Bool :=
    if i == 0
    then (Pos.Raw.get suf 0 == Pos.Raw.get main ⟨j⟩)
    else
      if (Pos.Raw.get suf ⟨i⟩ == Pos.Raw.get main ⟨j⟩)
      then go (i-1) (j-1)
      else false
  go (suf.endPos.byteIdx) (main.endPos.byteIdx)


def Blank (ind : Nat) : String :=
  .mk (List.replicate ind ' ')

def BlankJump (ind : Nat) {α : Sort _} (l : List α) (print : α → String) : String :=
  (Blank ind) ++ (String.intercalate ("\n"++ (Blank ind)) (l.map print))

def BlankJumpM (ind : Nat) {m : (Type _ → Type _)} [Monad m] {α : Sort _} (l : List α) (print : α → m String) : m String :=
  return (Blank ind) ++ (String.intercalate ("\n"++ (Blank ind)) (← l.mapM print))

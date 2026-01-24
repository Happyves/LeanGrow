
/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/


instance : Repr ByteArray where
  reprPrec := fun a _ =>
    match String.fromUTF8? a with
    | .none => "⟨failed UTF8⟩"
    | .some msg => msg

def ByteArray.exactRepr : Repr ByteArray where
  reprPrec := fun a _ => "⟨" ++ (repr a.data) ++ "⟩"

@[inline]
def ByteArray.beq_expl (A B : ByteArray) : Bool :=
  let rec help (A B : ByteArray) : Nat → Bool
      | 0 => true
      | n+1 => if A.get! n == B.get! n then help A B n else false
  if A.size == B.size
  then
    help A B A.size
  else
    false

@[inline]
unsafe def ByteArray.beq_expl' (A B : ByteArray) : Bool :=
  let rec help (A B : ByteArray) (i : USize) : Bool :=
    if i < A.usize
    then
      if A.uget i lcProof == B.uget i lcProof then help A B (i+1) else false
    else true
  if A.size == B.size
  then
    help A B 0
  else
    false

instance : BEq ByteArray where
  beq := fun a b => a.beq_expl b

/-- From left to right-/
@[inline]
partial def ByteArray.getLongestMatch (l r : ByteArray) : Nat :=
  let rec go (i : Nat) : Bool → Nat
    | true => go (i+1) (if (i+1) < l.size && (i+1) < r.size then l.get! (i+1) == r.get! (i+1) else false)
    | false => i
  go 0 (if 0 < l.size && 0 < r.size then l.get! 0 == r.get! 0 else false)

/-- From left to right, n excluded-/
@[inline]
partial def ByteArray.drop' (A : ByteArray) (n : Nat) : ByteArray :=
  let dif := (A.size - n)
  let toFill : Array UInt8 := Array.replicate dif 0
  let rec go (sofar : Array UInt8) (i : Nat) : Nat → Array UInt8
    | 0 => sofar
    | m+1 => go (sofar.set! i (A[(i+n)]!)) (i+1) (m)
  ⟨go toFill 0 (dif)⟩


/-- From left to right, n excluded-/
@[inline]
partial def ByteArray.drop (A : ByteArray) (n : Nat) : ByteArray :=
  A.copySlice (n) empty (n) A.size


@[inline]
partial def ByteArray.getLongestMatch_wOffset (off : Nat) (l r : ByteArray) : Nat :=
  let rec go (i : Nat) : Bool → Nat
    | true => go (i+1) (if (off+i+1) < l.size && (i+1) < r.size then l.get! (off+i+1) == r.get! (i+1) else false)
    | false => i
  go 0 (if off < l.size && 0 < r.size then l.get! off == r.get! 0 else false)

@[inline]
partial def ByteArray.getLongestMatch_wOffsets (l r : ByteArray)(ol or : Nat) : Nat :=
  let rec go (i : Nat) : Bool → Nat
    | true => go (i+1) (if (ol+i+1) < l.size && (or+i+1) < r.size then l.get! (ol+i+1) == r.get! (or+i+1) else false)
    | false => i
  go 0 (if ol < l.size && or < r.size then l.get! ol == r.get! or else false)

/-- From left to right, n excluded-/
@[inline]
partial def ByteArray.take' (A : ByteArray) (n : Nat) : ByteArray :=
  let toFill : Array UInt8 := Array.replicate n 0
  let rec go (sofar : Array UInt8) (i : Nat) : Nat → Array UInt8
    | 0 => sofar
    | m+1 => go (sofar.set! i (A.get! (i))) (i+1) (m)
  ⟨go toFill 0 n⟩

/-- From left to right, n excluded-/
@[inline]
partial def ByteArray.take (A : ByteArray) (n : Nat) : ByteArray :=
  A.copySlice 0 empty 0 (n)



@[inline]
partial def ByteArray.lex_compare_basic (A B: ByteArray) : Ordering :=
  let rec go (l r : Nat) : Ordering :=
    let a := A.get! l
    let b := B.get! r
    match Ord.compare a b with
    | .lt => .lt
    | .eq =>
        if (l+1 < A.size) && (r+1 < B.size)
        then
          go (l+1) (r+1)
        else
          .eq
    | .gt => .gt
  go 0 0


inductive DirOrdering where
| lt | gt | eqB | eqL (_ : Nat) | eqR (_ : Nat)
deriving Inhabited, BEq, Repr



@[inline]
partial def ByteArray.lex_compare (A B: ByteArray) : DirOrdering :=
  let rec go (l r : Nat) : DirOrdering :=
    let a := A.get! l
    let b := B.get! r
    match Ord.compare a b with
    | .lt => .lt
    | .eq =>
        if (l+1 ≥ A.size)
        then
          if (r+1 ≥ B.size)
          then
            .eqB
          else
            .eqR (r+1)
        else
          if (r+1 ≥ B.size)
          then
            .eqL (l+1)
          else
            go (l+1) (r+1)
    | .gt => .gt
  go 0 0

@[inline]
partial def ByteArray.lex_compare_wOffset_left (off : Nat) (A B: ByteArray) : DirOrdering :=
  let rec go (l r : Nat) : DirOrdering :=
    let a := A.get! l
    let b := B.get! r
    match Ord.compare a b with
    | .lt => .lt
    | .eq =>
        if (l+1 ≥ A.size)
        then
          if (r+1 ≥ B.size)
          then
            .eqB
          else
            .eqR (r+1)
        else
          if (r+1 ≥ B.size)
          then
            .eqL (l+1)
          else
            go (l+1) (r+1)
    | .gt => .gt
  go off 0

@[inline]
partial def ByteArray.lex_compare_wOffset_right (off : Nat) (A B: ByteArray) : DirOrdering :=
  let rec go (l r : Nat) : DirOrdering :=
    let a := A.get! l
    let b := B.get! r
    match Ord.compare a b with
    | .lt => .lt
    | .eq =>
        if (l+1 ≥ A.size)
        then
          if (r+1 ≥ B.size)
          then
            .eqB
          else
            .eqR (r+1)
        else
          if (r+1 ≥ B.size)
          then
            .eqL (l+1)
          else
            go (l+1) (r+1)
    | .gt => .gt
  go off 0


@[inline]
def ByteArray.insertAt! (as : ByteArray) (i : Nat) (a : UInt8) : ByteArray :=
  ⟨as.data.insertIdx! i a⟩



@[inline]
def ByteArray.matchSingle (s : ByteArray) (A : Array ByteArray) : Option Nat :=
  let rec go : Nat → Option Nat
    | 0 => .none
    | n+1 =>
        let c := A[n]!
        let com := ByteArray.getLongestMatch s c
        if com == 0
        then
          if c.get! 0 < s.get! 0
          then .none
          else go n
        else
          .some n
  go A.size


@[inline]
def ByteArray.matchSingle_wOffset (s : ByteArray) (off : Nat) (A : Array ByteArray) : Option Nat :=
  let rec go : Nat → Option Nat
    | 0 => .none
    | n+1 =>
        let c := A[n]!
        let com := ByteArray.getLongestMatch_wOffsets s c off 0
        if com == 0
        then
          if c.get! 0 < s.get! off
          then .none
          else go n
        else
          .some n
  go A.size


structure matchMultiOut where
  left : Nat
  right : Nat
  common : Nat
deriving Inhabited, BEq, Repr


@[inline]
partial def ByteArray.matchMulti (L R : Array ByteArray) : List (matchMultiOut) :=
  let rec go (l r : Nat) (done :  List (matchMultiOut)) : List (matchMultiOut) :=
    if (l < L.size) && (r < R.size)
    then
      let a := L[l]!
      let b := R[r]!
      let com := ByteArray.getLongestMatch a b
        if com == 0
        then
          if a.get! 0 < b.get! 0
          then go (l+1) r done
          else go l (r+1) done
        else
          go (l+1) (r+1) (⟨l,r, com⟩  :: done)
    else
      done
  go 0 0 []

inductive matType where
| ins (_ : Nat) | hit (idx : Nat) (com : Nat)
deriving Inhabited, BEq, Repr


@[inline]
def ByteArray.matchSingleHits_wOffset (s : ByteArray) (off : Nat) (A : Array ByteArray) : matType :=
  let rec go : Nat → matType
    | 0 => .ins 0
    | N@(n+1) =>
        let c := A[n]!
        let com := ByteArray.getLongestMatch_wOffsets s c off 0
        if com == 0
        then
          if c.get! 0 < s.get! off
          then .ins N
          else go n
        else
          .hit n com
  go A.size


@[inline]
partial def ByteArray.isPrefix (pre main : ByteArray) : Bool :=
  let rec go (i : Nat) : Bool :=
    if i == pre.size
    then true
    else
      if pre.get! i == main.get! i
      then go (i+1)
      else false
  go 0


@[inline]
partial def ByteArray.getPrefix (main : ByteArray) : ByteArray :=
  let rec go (i : Nat) (sf : Array UInt8) : Array UInt8 :=
    if i == main.size
    then sf
    else
      let c := main.get! i
      if c == 46
      then sf
      else go (i+1) (sf.push c)
  ⟨go 0 #[]⟩


@[inline]
def ByteArray.shrink (A : ByteArray) (n : Nat) : ByteArray :=
  {A with data := A.data.shrink n}

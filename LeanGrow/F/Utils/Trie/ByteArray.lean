
instance : Repr ByteArray where
  reprPrec := fun a _ => repr a.data

partial def ByteArray.getLongestMatch (l r : ByteArray) : Nat :=
  let rec go (i : Nat) : Bool → Nat
    | true => go (i+1) (if (i+1) < l.size && (i+1) < r.size then l.get! (i+1) == r.get! (i+1) else false)
    | false => i
  go 0 (if 0 < l.size && 0 < r.size then l.get! 0 == r.get! 0 else false)



partial def ByteArray.drop (A : ByteArray) (n : Nat) : ByteArray :=
  let dif := (A.size - n)
  let toFill : Array UInt8 := Array.mkArray dif 0
  let rec go (sofar : Array UInt8) (i : Nat) : Nat → Array UInt8
    | 0 => sofar
    | m+1 => go (sofar.set! i (A.get! (i+n))) (i+1) (m)
  ⟨go toFill 0 (dif)⟩


partial def ByteArray.getLongestMatch_wOffset (off : Nat) (l r : ByteArray) : Nat :=
  let rec go (i : Nat) : Bool → Nat
    | true => go (i+1) (if (off+i+1) < l.size && (i+1) < r.size then l.get! (off+i+1) == r.get! (i+1) else false)
    | false => i
  go 0 (if off < l.size && 0 < r.size then l.get! off == r.get! 0 else false)


partial def ByteArray.take (A : ByteArray) (n : Nat) : ByteArray :=
  let toFill : Array UInt8 := Array.mkArray n 0
  let rec go (sofar : Array UInt8) (i : Nat) : Nat → Array UInt8
    | 0 => sofar
    | m+1 => go (sofar.set! i (A.get! (i))) (i+1) (m)
  ⟨go toFill 0 n⟩


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


import Lean.Data

open Lean Data


instance : Repr ByteArray where
  reprPrec := fun a _ => repr a.data



partial def ByteArray.getLongestMatch (l r : ByteArray) : Nat :=
  let rec go (i : Nat) : Bool → Nat
    | true => go (i+1) (if (i+1) < l.size && (i+1) < r.size then l.get! (i+1) == r.get! (i+1) else false)
    | false => i
  go 0 (if 0 < l.size && 0 < r.size then l.get! 0 == r.get! 0 else false)

#eval ByteArray.getLongestMatch ⟨#[1,2,1]⟩ ⟨#[1,2,2]⟩
#eval ByteArray.getLongestMatch ⟨#[1,2,1]⟩ ⟨#[1,1,2]⟩
#eval ByteArray.getLongestMatch ⟨#[2,2,1]⟩ ⟨#[1,2,2]⟩
#eval ByteArray.getLongestMatch ⟨#[1,2,1]⟩ ⟨#[]⟩
#eval ByteArray.getLongestMatch ⟨#[1,2,1]⟩ ⟨#[1,2,1]⟩


partial def ByteArray.drop (A : ByteArray) (n : Nat) : ByteArray :=
  let dif := (A.size - n)
  let toFill : Array UInt8 := Array.mkArray dif 0
  let rec go (sofar : Array UInt8) (i : Nat) : Nat → Array UInt8
    | 0 => sofar
    | m+1 => go (sofar.set! i (A.get! (i+n))) (i+1) (m)
  ⟨go toFill 0 (dif)⟩

#eval ByteArray.drop ⟨#[1,2,3]⟩ 0
#eval ByteArray.drop ⟨#[1,2,3]⟩ 1
#eval ByteArray.drop ⟨#[1,2,3]⟩ 2
#eval ByteArray.drop ⟨#[1,2,3]⟩ 3

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

#eval ByteArray.take ⟨#[1,2,3]⟩ 0
#eval ByteArray.take ⟨#[1,2,3]⟩ 1
#eval ByteArray.take ⟨#[1,2,3]⟩ 2
#eval ByteArray.take ⟨#[1,2,3]⟩ 3



inductive CTrie (α : Type) where
  | leaf : Option α → CTrie α
  | node1 : Option α → ByteArray → CTrie α → CTrie α
  | node : Option α → Array ByteArray → Array (CTrie α) → CTrie α
deriving Repr


namespace CTrie
variable {α : Type}

def empty : CTrie α := leaf none

instance : EmptyCollection (CTrie α) :=
  ⟨empty⟩

instance : Inhabited (CTrie α) where
  default := empty



partial def upsert (t : CTrie α) (s : ByteArray) (f : Option α → α) : Trie α :=
  let go (i : Nat) : CTrie α → CTrie α
    | .leaf v =>
          if i < s.size
          then
            .node1 v (s.drop i) (.leaf (f .none))
          else
            .leaf (f v)
    | .node1 v c t =>
          if i < s.size
          then
            let j := ByteArray.getLongestMatch_wOffset i s c
            let nc := c.drop j
            let add := s.drop (i+j)
            let join := c.take j
            .node1 .none join (.node .none #[nc,add] #[.node1 v nc t, .node1 .none add (.leaf (f .none))])
          else
            .node1 (f v) c t
    | .node v cs ts =>
          if i < s.size
          then
            sorry
            -- Todo: for each branch, look for longest match.
            -- If non-zero, modify at that branch as in `.node1` and stop.
            -- if zero everwhere, append to `.node`
          else
            .node (f v) cs ts
  go 0 t


#check String.toUTF8

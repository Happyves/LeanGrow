
--import Batteries.Data.Array.Basic


def Array.mapF [Inhabited α] [Inhabited β] (A : Array α) (f : α → β) : Array β :=
  let new := Array.mkArray A.size default
  (List.range A.size).foldl (fun a i => a.set! i (f (A.get! i))) new


def Array.mapFI [Inhabited α] [Inhabited β] (A : Array α) (f : α → Nat → β) : Array β :=
  let new := Array.mkArray A.size default
  (List.range A.size).foldl (fun a i => a.set! i (f (A.get! i) i)) new


def Array.assignOrFail [BEq α] (i : Nat) (v : α) (A : Array (Option α)) : Option (Array (Option α)) :=
  match A.get! i with
  | .none => .some (A.set! i v)
  | .some w => if v == w then .some A else .none


def Array.maxI' [Inhabited α] (gt : α → α → Bool) (A : Array α) : α :=
  let rec go (sofar : α) : Nat → α
    | 0 => sofar
    | n+1 =>
        let a := (A.get! n)
        if gt a sofar
        then go a n
        else go sofar n
  go default A.size

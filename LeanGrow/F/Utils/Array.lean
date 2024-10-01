


def Array.mapF [Inhabited α] [Inhabited β] (A : Array α) (f : α → β) : Array β :=
  let new := Array.mkArray A.size default
  (List.range A.size).foldl (fun a i => a.set! i (f (A.get! i))) new


def Array.mapFI [Inhabited α] [Inhabited β] (A : Array α) (f : α → Nat → β) : Array β :=
  let new := Array.mkArray A.size default
  (List.range A.size).foldl (fun a i => a.set! i (f (A.get! i) i)) new

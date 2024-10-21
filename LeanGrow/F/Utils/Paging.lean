
#check 1



def PageingSet
  (pages : List (Array α)) (pages_handler : Nat → (Nat × Nat)) (page_size : Nat) (filler : α)
  (loc : Nat) (val : α) : List (Array α) :=
  let (p,i) := pages_handler loc
  let rec modOrAddMod : Nat → List (Array α) → List (Array α)
    | n+1, here :: more => here :: (modOrAddMod n more)
    | n+1, [] => (Array.mkArray page_size filler) :: (modOrAddMod n [])
    | 0, [] => [(Array.mkArray page_size filler).set! i val]
    | 0, mod :: more => (mod.set! i val) :: more
  modOrAddMod p pages

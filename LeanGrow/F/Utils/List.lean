



-- # Sorting


def List.orderedContains {α : Type _} [BEq α] (r : α → α → Prop) [DecidableRel r] (a : α) : List α → Bool
| [] => false
| x :: l => if r x a then (if x == a then true else (List.orderedContains r a l)) else false

def List.orderedInsertOrLeave [BEq α] (r : α → α → Prop) [DecidableRel r] (a : α) : List α → List α
  | [] => [a]
  | b :: l => if r a b then (if a == b then b :: l else a :: b :: l) else b :: List.orderedInsertOrLeave r a l

def List.orderedEraseOrLeave [BEq α] (r : α → α → Prop) [DecidableRel r] (a : α) : List α → List α
  | [] => []
  | b :: l => if r a b then (if a == b then l else b :: l) else b :: List.orderedEraseOrLeave r a l


-- # noOrder

def List.insertOrLeave [BEq α] (a : α) : List α → List α
  | [] => [a]
  | b :: l => if a == b then b :: l else b :: List.insertOrLeave a l

/-- Assumes the list has no duplicates of the elemenent to be erased-/
def List.eraseOrLeave [BEq α] (a : α) : List α → List α
  | [] => []
  | b :: l => if a == b then l else b :: List.eraseOrLeave a l


-- # headD_tail

def List.headD_tail (l : List α) (default : α) : α × List α :=
  match l with
  | [] => (default, [])
  | h :: t => (h,t)


-- # reduce or fail

def List.reduceOptionOrFail : List (Option α) →  Option (List α)
| [] => .some []
| .some x :: l => (x :: ·) <$> (List.reduceOptionOrFail l)
| .none :: _ => .none


def List.findModify (p : α → Bool) (modify : α → α) : List α → List α
| [] => []
| x :: l => if p x then (modify x) :: l else x :: (List.findModify p modify l)


-- # intersect

def List.orderedIntersect [BEq α] (r : α → α → Prop) [DecidableRel r] (a b : List α) : List α :=
  let rec go (inter : List α) : List α → List α → List α
    | [], _ => inter
    | _, [] => inter
    | ah :: aT , bh :: bT =>
        if r ah bh
        then
          if ah == bh
          then go (ah :: inter) aT bT
          else go inter aT (bh :: bT)
        else go inter (ah :: aT) bT
  (go [] a b).reverse

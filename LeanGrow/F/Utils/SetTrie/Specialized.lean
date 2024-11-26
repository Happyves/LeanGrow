
import LeanGrow.F.Utils.SetTrie.Build
import LeanGrow.F.Utils.Trie.Sorted
import LeanGrow.F.Utils.ExprTrieRWez.Unify

#check 1

-- with β as a Trie or as a CExprTrie

def SetTrieT (α : Type _) := SetTrie α (CTrie Unit)

def SetTrieC (α : Type _) := SetTrie α (CExprTrie Nat)

def SetTrieN (α : Type _) := SetTrie α (List Nat) -- ordered lists for cluster ids


def SetTrieT.find_keys (c : List (SetTrieT α)) : CTrie Nat :=
  SetTrie.find_keys c CTrie.empty (fun t sofar => CTrie.merge_count (CTrie.merge_count_initialise t) sofar)

def SetTrieC.find_keys (c : List (SetTrieC α)) : List (Nat × CExpr) := -- (occs, cexpr)
  let rec help (count : Nat) (ref : CExpr) : List (CExpr × List Nat) → Nat
    | (ce, _) :: more =>
        if ce == ref
        then help (Nat.succ count) ref more -- could replace `more` with `[]` if we're sure expression appear only once in CExprTrie
        else help (count) ref more
    | _ => count
  SetTrie.find_keys c [] (fun t sofar =>
    let build := CExprTrie.buildAtLink t 0 (· ≤ ·)
    sofar.map (fun (c,ref) => (help c ref build, ref))
    )

def SetTrieN.find_keys (c : List (SetTrieN α)) : List (Nat × Nat) := -- (occs, ids)
  let rec help (inc_id : Nat) : List (Nat × Nat) → List (Nat × Nat)
  | [] => []
  | x :: xs => if x.2 < inc_id then x :: (help inc_id xs) else (if x.2 = inc_id then (Nat.succ x.1,x.2) :: xs else x :: xs)
  SetTrie.find_keys c [] (fun t sofar => t.foldl (fun x y => help y x) sofar)



def SetTrieT.split_on_split (c : List (SetTrieT α)) (key : String) :
  List (SetTrieT α) × List (SetTrieT α) :=
    SetTrie.split_on_split c key CTrie.find?

def SetTrieC.split_on_split (c : List (SetTrieC α)) (key : CExpr) :
  List (SetTrieC α) × List (SetTrieC α) :=
    SetTrie.split_on_split c key (fun x y =>
      match CExprTrie.find? x y (· ≤ ·) with
      | [] => .some ()
      | _ => .none
      )


-- specializing these may be useless

def SetTrieT.split_on (c : List (SetTrieT α)) (key : String) : List (SetTrieT α) :=
  SetTrie.split_on c key CTrie.find? (CTrie.ofList [(key,())])

def SetTrieC.split_on (c : List (SetTrieC α)) (key : CExpr) : List (SetTrieC α) :=
    SetTrie.split_on c key (fun x y =>
      match CExprTrie.find? x y (· ≤ ·) with
      | [] => .some ()
      | _ => .none
      )
      (CExprTrie.ofList (· ≤ ·) [(0,key)])


def SetTrieT.delete_key_or_leave (k : String) (T : SetTrieT α) : SetTrieT α :=
  SetTrie.delete_key_or_leave k (CTrie.delete) T


def SetTrieC.delete_key_or_leave (k : CExpr) (T : SetTrieC α) : SetTrieC α :=
  SetTrie.delete_key_or_leave k (sorry) T


def SetTrieT.split_greedy_exact_hitting_set (c : List (SetTrieT α)) : List (SetTrieT α) :=
  SetTrie.split_greedy_exact_hitting_set
    CTrie.empty (fun t sofar => CTrie.merge_count (CTrie.merge_count_initialise t) sofar)
    CTrie.find_max CTrie.find? CTrie.delete (fun key => CTrie.ofList [(key,())]) c


def SetTrieC.split_greedy_exact_hitting_set (c : List (SetTrieC α)) : List (SetTrieC α) :=
  let rec help (count : Nat) (ref : CExpr) : List (CExpr × List Nat) → Nat
    | (ce, _) :: more =>
        if ce == ref
        then help (Nat.succ count) ref more -- could replace `more` with `[]` if we're sure expression appear only once in CExprTrie
        else help (count) ref more
    | _ => count

  SetTrie.split_greedy_exact_hitting_set
    [] (fun t sofar =>
    let build := CExprTrie.buildAtLink t 0 (· ≤ ·)
    sofar.map (fun (c,ref) => (help c ref build, ref))
    )
    sorry
    (fun x y =>
      match CExprTrie.find? x y (· ≤ ·) with
      | [] => .some ()
      | _ => .none
      )
    sorry
    (fun key => CExprTrie.ofList (· ≤ ·) [(0,key)]) c

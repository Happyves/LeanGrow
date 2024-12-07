
import LeanGrow.F.Utils.SetTrie.Build
import LeanGrow.F.Utils.SetTrie.Query
import LeanGrow.F.Utils.Trie.Sorted
--import LeanGrow.F.Utils.ExprTrieRWez.Unify
import LeanGrow.F.Utils.CExprTrie.Merge
import LeanGrow.F.Utils.CExprTrie.Delete


#check 1


-- # CTrie

def SetTrieT (α : Type _) := SetTrie α (CTrie Unit)

def SetTrieT.make [Inhabited α] (l : List (CTrie Unit)) : SetTrieT α :=
  SetTrie.make (CTrie.empty : CTrie Nat) (CTrie.empty : CTrie Unit)
    (fun t sofar => CTrie.merge_count (CTrie.merge_count_initialise t) sofar)
    CTrie.find_maxes CTrie.difference CTrie.find_max CTrie.find? CTrie.delete
    (fun key => CTrie.ofList [(key,())]) CTrie.merge l

def SetTrieT.query (Q : CTrie Unit) (T : SetTrieT α) : List α :=
  SetTrie.query (fun t Q => CTrie.CountCommon t Q = CTrie.size t) Q T


-- # CExprTrie

def SetTrieC (α : Type _) := SetTrie α CExprTrie

def SetTrieC.make [Inhabited α] (l : List CExprTrie) : SetTrieC α :=
  SetTrie.make' CExprTrie.dead CExprTrie.merge! CExprTrie.count CExprTrie.find_maxes
    CExprTrie.difference CExprTrie.find_max (fun x y =>  match CExprTrie.find? y x with | [] => .none | _ :: _ => .some ())
    CExprTrie.deleteCExpr (fun ce => CExprTrie.insert ce 1 .dead) l


def SetTrieC.query (Q : CExprTrie) (T : SetTrieC α) : List α :=
  SetTrie.query CExprTrie.contains Q T



-- # Lists of nats

def SetTrieN (α : Type _) := SetTrie α (List Nat) -- unordered lists for cluster ids

def SetTrieN.make [Inhabited α] (l : List (List Nat)) : SetTrieN α :=
  let rec find_maxes (empty? : Bool) (done : List Nat) (max : Nat) : List (Nat × Nat) → Option ((List Nat) × Nat)
    | [] => if empty? then .none else .some (done,max)
    | nx :: more =>
        match compare nx.1 max with
        | .gt => find_maxes false [nx.2] nx.1 more
        | .eq => find_maxes false (nx.2 :: done) max more
        | .lt => find_maxes false done max more
  let rec find_max (empty? : Bool) (done : Nat) (max : Nat) : List (Nat × Nat) → Option (Nat × Nat)
    | [] => if empty? then .none else .some (done,max)
    | nx :: more =>
        match compare nx.1 max with
        | .gt => find_max false nx.2 nx.1 more
        | _ => find_max false done max more
  SetTrie.make ([] : List (Nat × Nat)) ([] : List Nat) -- ←↓ (occs, id)
    (fun t sofar => t.foldl (fun x y => x.findModifyAdd (fun z => z.2 == y) (fun z => (z.1+1,z.2)) (1,y)) sofar)
    (find_maxes true [] 0) (fun x y => y.foldl (fun a b => a.erase b) x) (find_max true 0 0)
    (fun l x => l.find? (fun y => y == x)) List.erase (fun n => [n]) List.append l


def SetTrieN.query (Q : List Nat) (T : SetTrieN α) : List α :=
  let rec contains (t Q : List Nat) : Bool :=
    match t with
    | [] => true
    | nx :: more => if Q.contains nx then contains more Q else false
  SetTrie.query contains Q T


/-
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
-/

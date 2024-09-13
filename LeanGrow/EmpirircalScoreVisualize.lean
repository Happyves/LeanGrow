

import LeanGrow.Caches.EmpScoreSmol

open Lean Data


#check LinkTreeTop
#check g_LinkTreeTop

#check empirical_score_data

#check Trie.find?

-- Yeahhhh ....
-- partial def Trie.tBSfind? (t : Trie (tBS α)) (s : String) : Option α :=
--   let rec loop
--     | i, .leaf val =>
--       if i < s.utf8ByteSize then
--         .none
--       else
--         match val with
--         | .some (.ofVal v) => .some v
--         | .some (.ofPoint p) => Trie.tBSfind? p (String.drop s i)
--         | .none => .none
--     | i, .node1 val c' t' =>
--       if h : i < s.utf8ByteSize then
--         let c := s.getUtf8Byte i h
--         if c == c'
--         then loop (i + 1) t'
--         else none
--       else
--         match val with
--         | .some (.ofVal v) => .some v
--         | .some (.ofPoint p) => Trie.tBSfind? p (String.drop s i)
--         | .none => .none
--     | i, .node val cs ts =>
--       if h : i < s.utf8ByteSize then
--         let c := s.getUtf8Byte i h
--         match cs.findIdx? (· == c) with
--         | none   => none
--         | some idx => loop (i + 1) (ts.get! idx)
--       else
--         match val with
--         | .some (.ofVal v) => .some v
--         | .some (.ofPoint p) => Trie.tBSfind? p (String.drop s i)
--         | .none => .none
--   loop 0 t

partial def Trie.tBSfind?_aux (s : ByteArray) (idx : Nat) :  Trie (tBS α) → Option α
| .leaf (.some (.ofVal x)) => if idx = s.size - 1 then .some x else .none
| .leaf (.some (.ofPoint x)) => Trie.tBSfind?_aux s idx x
| .leaf .none => .none
| .node1 x a t => if idx < s.size then (if a == s.get! idx then Trie.tBSfind?_aux s (idx+1) t else .none) else (match x with | .some (.ofVal y) => .some y | _ => .none)
| .node x as ts => if idx < s.size then (match as.findIdx? (· == s.get! idx) with | .some i => Trie.tBSfind?_aux s (idx+1) (ts.get! i) | _ => .none) else (match x with | .some (.ofVal y) => .some y | _ => .none)

-- fails too :<
def Trie.tBSfind? (s : String) :  Trie (tBS α) → Option α :=
  fun T => Trie.tBSfind?_aux s.toAsciiByteArray 0 T




partial def Trie.destratify : Trie (tBS α) → Trie α
| .leaf x =>
      match x with
      | .some (.ofPoint p) => Trie.destratify p
      | .some (.ofVal x) => .leaf (.some x)
      | _ => .leaf .none
| .node1 x a t =>
      match x with
      | .some (.ofVal x) => .node1 (.some x) a (Trie.destratify t)
      | .none => .node1 .none a (Trie.destratify t)
      | _ => .leaf .none -- shouldn't happen
| .node x as ts =>
      match x with
      | .some (.ofVal x) => .node (.some x) as (ts.map Trie.destratify)
      | .none => .node .none as (ts.map Trie.destratify)
      | _ => .leaf .none


--#exit

elab "visualize" : command => do
  let thm := `eq_comm -- should be *used* in Mathlib.Data.List.Basic
  let .some entry := Trie.find? (Trie.destratify empirical_score_data) thm.toString | throwError "aaahhh 1"
  let hyp_cl := RBNode.fold (fun sofar k v => Id.run do
        let .some (_,C) := Lsclu_from_qt_all.find? (fun x => x.1 == k) | return sofar
        let h_namez := ((C.map pdata.sink_cst_names).map (Trie.print_keys ⟨#[]⟩)).join
        let g_namez := ((C.map pdata.goal_cst_names ).map (Trie.print_keys ⟨#[]⟩)).join
        return (s!"Hyp-cluster {k}, with value {v}\nHN : {String.intercalate ", " h_namez}\nGN : {String.intercalate ", " g_namez}") :: sofar
      ) [] entry.hyp_cl
  let g_cl := RBNode.fold (fun sofar k v => Id.run do
        let .some (_,C) := g_Lsclu_from_qt_all.find? (fun x => x.1 == k) | return sofar
        let namez := ((C.map gdata.name_list).map (Trie.print_keys ⟨#[]⟩)).join
        return (s!"Goal-cluster {k}, with value {v}\nN : {String.intercalate ", " namez}") :: sofar
      ) [] entry.hyp_cl
  logInfo (String.intercalate "\n\n" (hyp_cl ++ g_cl))

#check List.append_eq_has_append

visualize

#eval Trie.print_keys ⟨#[]⟩ empirical_score_data

partial def Trie.print_keys_tBS (cache : ByteArray) : Trie (tBS α) → List String
| .leaf x =>
    match x with
    | .some (.ofPoint p) => Trie.print_keys_tBS cache p
    | .some (.ofVal _) => [String.fromUTF8 cache (by sorry)]
    | _ => []
| .node1 x a c =>
    let go := Trie.print_keys_tBS (cache.push a) c
    match x with
    | .some (.ofPoint p) => Trie.print_keys_tBS cache p
    | .some (.ofVal _) => (String.fromUTF8 cache (by sorry)) :: go
    | _ => go
| .node x as cs =>
    let go :=
      Id.run do
        let mut res := []
        for z in (List.range as.size) do
          res :=  (Trie.print_keys_tBS (cache.push (as.get! z)) (cs.get! z)) :: res
        return res
    match x with
    | .some (.ofPoint p) => Trie.print_keys_tBS cache p
    | .some (.ofVal _) => (String.fromUTF8 cache (by sorry)) :: (List.join go)
    | _ => (List.join go)

#eval Trie.print_keys_tBS ⟨#[]⟩ empirical_score_data

#eval Trie.print_keys ⟨#[]⟩ (Trie.destratify empirical_score_data)

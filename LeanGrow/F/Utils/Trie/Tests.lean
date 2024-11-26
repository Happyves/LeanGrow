
import LeanGrow.F.Utils.Trie.ByteArray
import LeanGrow.F.Utils.Trie.CTrie
import LeanGrow.F.Utils.Trie.Sorted



open Lean Data

#eval ByteArray.getLongestMatch ⟨#[1,2,1]⟩ ⟨#[1,2,2]⟩
#eval ByteArray.getLongestMatch ⟨#[1,2,1]⟩ ⟨#[1,1,2]⟩
#eval ByteArray.getLongestMatch ⟨#[2,2,1]⟩ ⟨#[1,2,2]⟩
#eval ByteArray.getLongestMatch ⟨#[1,2,1]⟩ ⟨#[]⟩
#eval ByteArray.getLongestMatch ⟨#[1,2,1]⟩ ⟨#[1,2,1]⟩


#eval ByteArray.drop ⟨#[1,2,3]⟩ 0
#eval ByteArray.drop ⟨#[1,2,3]⟩ 1
#eval ByteArray.drop ⟨#[1,2,3]⟩ 2
#eval ByteArray.drop ⟨#[1,2,3]⟩ 3


#eval ByteArray.take ⟨#[1,2,3]⟩ 0
#eval ByteArray.take ⟨#[1,2,3]⟩ 1
#eval ByteArray.take ⟨#[1,2,3]⟩ 2
#eval ByteArray.take ⟨#[1,2,3]⟩ 3


def test_list : List (String × Nat) := [("ban", 42),("banana", 37),("bandana", 69), ("bahamas", 2)]

#eval CTrie.ofList test_list

#eval CTrie.find? (CTrie.ofList test_list) "bahamas"
#eval CTrie.find? (CTrie.ofList test_list) "ban"
#eval CTrie.find? (CTrie.ofList test_list) "banana"
#eval CTrie.find? (CTrie.ofList test_list) "bandana"
#eval CTrie.find? (CTrie.ofList test_list) "trains"

#eval Array.insertAt! #[1,2,3] 1 42
#eval Array.insertAt! #[1,2,3] 3 42
#eval Array.insertAt! #[1,2,3] 0 42

#eval CTrie.ofList_sorted test_list

#eval CTrie.toList (CTrie.ofList_sorted test_list)

#eval CTrie.sorted_find? (CTrie.ofList_sorted test_list) "bahamas"
#eval CTrie.sorted_find? (CTrie.ofList_sorted test_list) "ban"
#eval CTrie.sorted_find? (CTrie.ofList_sorted test_list) "banana"
#eval CTrie.sorted_find? (CTrie.ofList_sorted test_list) "bandana"
#eval CTrie.sorted_find? (CTrie.ofList_sorted test_list) "trains"

def test_list_2 : List (String × Nat) := [("ban", 42),("bad", 37),("bandana", 69), ("bar", 2)]

def test_list_3 : List (String × Nat) := [("ban", 42),("banana", 37),("bandana", 666), ("bahamas", 2)]


#eval (CTrie.ofList_sorted test_list_2)
#eval (CTrie.ofList_sorted test_list)
#eval (CTrie.ofList_sorted test_list_3)

#eval CTrie.CountCommon (CTrie.ofList_sorted test_list) (CTrie.ofList_sorted test_list_2)
#eval CTrie.CountCommon (CTrie.ofList_sorted test_list) (CTrie.ofList_sorted test_list_3)
#eval CTrie.CountCommon (CTrie.ofList_sorted test_list) {}

#eval CTrie.CountCommon' (CTrie.ofList_sorted test_list) (CTrie.ofList_sorted test_list_2)
#eval CTrie.CountCommon' (CTrie.ofList_sorted test_list) (CTrie.ofList_sorted test_list_3)
#eval CTrie.CountCommon' (CTrie.ofList_sorted test_list) {}

#eval CTrie.intersect_val (CTrie.ofList_sorted test_list) (CTrie.ofList_sorted test_list_2)
#eval CTrie.intersect_val (CTrie.ofList_sorted test_list) (CTrie.ofList_sorted test_list_3)
#eval CTrie.intersect_val (CTrie.ofList_sorted test_list) {}

#eval CTrie.intersect (CTrie.ofList_sorted test_list) (CTrie.ofList_sorted test_list_2)
#eval CTrie.intersect (CTrie.ofList_sorted test_list) (CTrie.ofList_sorted test_list_3)
#eval CTrie.intersect (CTrie.ofList_sorted test_list) {}

#eval CTrie.toList (CTrie.intersect (CTrie.ofList_sorted test_list) (CTrie.ofList_sorted test_list_2))
#eval CTrie.toList (CTrie.intersect (CTrie.ofList_sorted test_list) (CTrie.ofList_sorted test_list_3))
#eval CTrie.toList (CTrie.intersect (CTrie.ofList_sorted test_list) {})


#eval (CTrie.merge (CTrie.ofList_sorted test_list) (CTrie.ofList_sorted test_list_2))
#eval (CTrie.merge (CTrie.ofList_sorted test_list) (CTrie.ofList_sorted test_list_3))
#eval (CTrie.merge (CTrie.ofList_sorted test_list) {})


#eval CTrie.toList (CTrie.merge (CTrie.ofList_sorted test_list) (CTrie.ofList_sorted test_list_2))
#eval CTrie.toList (CTrie.merge (CTrie.ofList_sorted test_list) (CTrie.ofList_sorted test_list_3))
#eval CTrie.toList (CTrie.merge (CTrie.ofList_sorted test_list) {})

#eval (CTrie.difference (CTrie.ofList_sorted test_list) (CTrie.ofList_sorted test_list_2))
#eval (CTrie.difference (CTrie.ofList_sorted test_list) (CTrie.ofList_sorted test_list_3))
#eval (CTrie.difference (CTrie.ofList_sorted test_list) {})


#eval CTrie.toList (CTrie.difference (CTrie.ofList_sorted test_list) (CTrie.ofList_sorted test_list_2))
#eval CTrie.toList (CTrie.difference (CTrie.ofList_sorted test_list_2) (CTrie.ofList_sorted test_list))
#eval CTrie.toList (CTrie.difference (CTrie.ofList_sorted test_list) (CTrie.ofList_sorted test_list_3))
#eval CTrie.toList (CTrie.difference (CTrie.ofList_sorted test_list) {})

#eval CTrie.clean (CTrie.difference (CTrie.ofList_sorted test_list) (CTrie.ofList_sorted test_list_2))
-- used to have a useless .leaf .none that got cleaned
#eval CTrie.clean (CTrie.difference (CTrie.ofList_sorted test_list) (CTrie.ofList_sorted test_list_3))
#eval CTrie.toList (CTrie.clean (CTrie.difference (CTrie.ofList_sorted test_list) (CTrie.ofList_sorted test_list_2)))
#eval CTrie.toList (CTrie.clean (CTrie.difference (CTrie.ofList_sorted test_list) (CTrie.ofList_sorted test_list_3)))


#eval CTrie.enumerate 0 (CTrie.ofList_sorted test_list_2)
#eval CTrie.enumerate 0 (CTrie.ofList_sorted test_list)
#eval CTrie.enumerate 0 (CTrie.ofList_sorted test_list_3)

#eval CTrie.toList  (CTrie.merge_count (CTrie.merge_count_initialise (CTrie.ofList_sorted test_list)) (CTrie.merge_count_initialise  (CTrie.ofList_sorted test_list_2)))
#eval CTrie.toList  (CTrie.merge_count (CTrie.merge_count_initialise (CTrie.ofList_sorted test_list)) (CTrie.merge_count_initialise  (CTrie.ofList_sorted test_list_3)))
#eval CTrie.toList  (CTrie.merge_count (CTrie.merge_count_initialise (CTrie.ofList_sorted test_list)) {})

#eval CTrie.toList (CTrie.delete (CTrie.ofList_sorted test_list) "ban")
#eval CTrie.toList (CTrie.delete (CTrie.ofList_sorted test_list) "banana")

#eval CTrie.find_max  (CTrie.merge_count (CTrie.merge_count_initialise (CTrie.ofList_sorted test_list)) (CTrie.merge_count_initialise  (CTrie.ofList_sorted test_list_2)))
#eval CTrie.find_max  (CTrie.merge_count (CTrie.merge_count_initialise (CTrie.ofList_sorted test_list)) (CTrie.merge_count_initialise  (CTrie.ofList_sorted test_list_3)))
#eval CTrie.find_max  (CTrie.merge_count (CTrie.merge_count_initialise (CTrie.ofList_sorted test_list)) {})

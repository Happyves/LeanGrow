
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


#eval CTrie.sorted_find? (CTrie.ofList_sorted test_list) "bahamas"
#eval CTrie.sorted_find? (CTrie.ofList_sorted test_list) "ban"
#eval CTrie.sorted_find? (CTrie.ofList_sorted test_list) "banana"
#eval CTrie.sorted_find? (CTrie.ofList_sorted test_list) "bandana"
#eval CTrie.sorted_find? (CTrie.ofList_sorted test_list) "trains"

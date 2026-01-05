/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/


import LeanGrow.Src.Data.CTrie.Basic


open CTrie


#eval ByteArray.getLongestMatch ⟨#[1,2,1]⟩ ⟨#[1,2,2]⟩
#eval ByteArray.getLongestMatch ⟨#[1,2,1]⟩ ⟨#[1,1,2]⟩
#eval ByteArray.getLongestMatch ⟨#[2,2,1]⟩ ⟨#[1,2,2]⟩
#eval ByteArray.getLongestMatch ⟨#[1,2,1]⟩ ⟨#[]⟩
#eval ByteArray.getLongestMatch ⟨#[1,2,1]⟩ ⟨#[1,2,1]⟩


#eval ByteArray.exactRepr.reprPrec (ByteArray.drop ⟨#[1,2,3]⟩ 0) 0
#eval ByteArray.exactRepr.reprPrec (ByteArray.drop ⟨#[1,2,3]⟩ 1) 0
#eval ByteArray.drop ⟨#[1,2,3]⟩ 2
#eval ByteArray.drop ⟨#[1,2,3]⟩ 3


#eval ByteArray.take ⟨#[1,2,3]⟩ 0
#eval ByteArray.take ⟨#[1,2,3]⟩ 1
#eval ByteArray.take ⟨#[1,2,3]⟩ 2
#eval ByteArray.take ⟨#[1,2,3]⟩ 3


def pre_test_list_1 : List (String × Nat) :=
  [("ban", 42),("banana", 37),("bandana", 69), ("bahamas", 2)]

def test_list_1 : ListProd String Nat :=
  ListProd.ofListOfProd pre_test_list_1

#eval test_list_1

def ctrie_1 :=  CTrie.ofList test_list_1

#eval ctrie_1


def test_list_2 : ListProd String Nat := .cons "ban" 42 <| .cons "bad" 37 <| .cons "bandana" 69 <| .cons "bar" 2 .nil
def ctrie_2 :=  CTrie.ofList test_list_2

#eval ctrie_2

def test_list_3 : ListProd String Nat := .cons "ban" 42 <| .cons "banana" 37 <| .cons "bandana" 666 <| .cons "bahamas" 2 .nil
def ctrie_3 :=  CTrie.ofList test_list_3

#eval ctrie_3

#eval ctrie_1.toList
#eval ctrie_2.toList
#eval ctrie_3.toList


#eval CTrie.find? ctrie_1 "bahamas".toUTF8
#eval CTrie.find? ctrie_1 "ban".toUTF8
#eval CTrie.find? ctrie_1 "banana".toUTF8
#eval CTrie.find? ctrie_1 "bandana".toUTF8
#eval CTrie.find? ctrie_1 "trains".toUTF8


#eval ctrie_1.upsert "bahamas".toUTF8 (fun x => (· + 2) <$> x)
#eval CTrie.toList <| ctrie_1.upsert "bahamas".toUTF8 (fun x => (· + 2) <$> x)

#eval CTrie.insert ctrie_1 "baltic".toUTF8 13

#eval CTrie.delete ctrie_1 "ban".toUTF8
#eval CTrie.delete ctrie_1 "bahamas".toUTF8
#eval CTrie.delete ctrie_1 "baltic".toUTF8



#eval ctrie_1.map (fun x => (· + 2) <$> x)
#eval ctrie_1.map (fun x => if x % 2 == 0 then Option.none else .some (x+1))
#eval ctrie_1.map (fun x => if x % 2 == 1 then Option.none else .some (x+1))
#eval clean <| ctrie_1.map (fun x => if x % 2 == 1 then Option.none else .some (x+1))


#eval 42 + 37 + 69 + 2
#eval ctrie_1.fold 0 (fun _ val S => val + S)

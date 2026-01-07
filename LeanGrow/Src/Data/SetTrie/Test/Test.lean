
/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import LeanGrow.Src.Data.SetTrie.Specialize

open Lean


def set1 : CTrie Unit := CTrie.ofList <| ListProd.ofListOfProd <|
  [("ban",()),("banana",()),("bahamas",()),("banal",())]

def set2 : CTrie Unit := CTrie.ofList <| ListProd.ofListOfProd <|
  [("ban",()),("banana",()),("bahamas",()),("baila, baila me",())]

def set3 : CTrie Unit := CTrie.ofList <| ListProd.ofListOfProd <|
  [("bahamas",()),("banal",())]

def set4 : CTrie Unit := CTrie.ofList <| ListProd.ofListOfProd <|
  [("some",()),("thing",()),("different",()),("entirely",())]


def testST : SetTrieT Nat := SetTrieT.ofList <| ListProd.ofListOfProd <|
  [(set1,1),(set2,2),(set3,42),(set4,42)]


def printit : String := Id.run do
  SetTrie.pp 0
    (fun x => return s!"{toString x.toList}")
    (fun x => return toString x)
    testST

#eval IO.println printit
-- IO to handle line jumps

def set1' : CTrie Unit := CTrie.ofList <| ListProd.ofListOfProd <|
  [("ban",()),("banana",()),("bahamas",()),("banal",())]

def set2' : CTrie Unit := CTrie.ofList <| ListProd.ofListOfProd <|
  [("ban",()),("banana",()),("bahamas",()),("banal",())]

def set3' : CTrie Unit := CTrie.ofList <| ListProd.ofListOfProd <|
  [("bahamas",()),("banal",())]

def set4' : CTrie Unit := CTrie.ofList <| ListProd.ofListOfProd <|
  [("some",()),("thing",()),("different",()),("entirely",())]


def testST' : SetTrieT Nat := SetTrieT.ofList <| ListProd.ofListOfProd <|
  [(set1',1),(set2',2),(set3',42),(set4',42)]


def printit' : String := Id.run do
  SetTrie.pp 0
    (fun x => return s!"{toString x.toList}")
    (fun x => return toString x)
    testST'

#eval IO.println printit'
-- IO to handle line jumps


def q1 : CTrie Unit := CTrie.ofList <| ListProd.ofListOfProd <|
  [("ban",()),("banana",()),("bahamas",()),("banal",()),("some",()),("thing",()),("different",()),("entirely",())]

def q2 : CTrie Unit := CTrie.ofList <| ListProd.ofListOfProd <|
  [("ban",()),("baila, baila me",()),("banana",()),("bahamas",()),("banal",()),("some",()),("thing",())]


#eval SetTrieT.query q1 testST
#eval SetTrieT.query q1 testST'
#eval SetTrieT.query q2 testST
#eval SetTrieT.query q2 testST'



def s1 : CTrie Unit := CTrie.ofList <| ListProd.ofListOfProd <|
  [("a",()),("b",()),("x",())]

def s2 : CTrie Unit := CTrie.ofList <| ListProd.ofListOfProd <|
  [("a",()),("c",()),("x",())]

def s3 : CTrie Unit := CTrie.ofList <| ListProd.ofListOfProd <|
  [("c",()),("d",())]

def s4 : CTrie Unit := CTrie.ofList <| ListProd.ofListOfProd <|
  [("c",()),("e",()),("y",())]

def s5 : CTrie Unit := CTrie.ofList <| ListProd.ofListOfProd <|
  [("f",()),("e",()),("y",())]


def testST'' : SetTrieT Nat := SetTrieT.ofList <| ListProd.ofListOfProd <|
  [(s1,1),(s2,2),(s3,3),(s4,4),(s5,5)]


def printit'' : String := Id.run do
  SetTrie.pp 0
    (fun x => return s!"{toString x.toList}")
    (fun x => return toString x)
    testST''

#eval IO.println printit''

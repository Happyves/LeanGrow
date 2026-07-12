

import LeanGrow.Src.Data.SetTrie.Specialize


-- # Settries

/-
Motivation:

- Forward step in proof search: in our local context, which sets of theorem
  hypotheses do we have as subsets (so that we can get the theorems result!)

- Abstracted: family of target sets, query set, which target sets ⊆ query sets ?

- Settries: check if *common* subsets of target sets are in query set first first

-/


def s1 : CTrie Unit := CTrie.ofList <| ListProd.ofListOfProd <|
  ["a","b","x"].map (fun x => (x,()))

def s2 : CTrie Unit := CTrie.ofList <| ListProd.ofListOfProd <|
  ["a","c","x"].map (fun x => (x,()))

def s3 : CTrie Unit := CTrie.ofList <| ListProd.ofListOfProd <|
  ["c","d"].map (fun x => (x,()))

def s4 : CTrie Unit := CTrie.ofList <| ListProd.ofListOfProd <|
  ["c","e","y"].map (fun x => (x,()))

def s5 : CTrie Unit := CTrie.ofList <| ListProd.ofListOfProd <|
  ["f","e","y"].map (fun x => (x,()))


def testST : SetTrieT Nat := SetTrieT.ofList <| ListProd.ofListOfProd <|
  [(s1,1),(s2,2),(s3,3),(s4,4),(s5,5)]


def printit : IO Unit := IO.println <| Id.run do
    SetTrie.pp 0
      (fun x => return s!"{toString (x.toList.toListOfProd.map Prod.fst)}")
      (fun x => return toString x)
      testST

#eval printit


#eval testST.query <| CTrie.ofList <| ListProd.ofListOfProd <|
  ["a","b","c","x"].map (fun x => (x,()))

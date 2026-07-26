

import LeanGrow.Src.Data.SetTrie.Specialize
import LeanGrow.Src.Core.Embedding.TestTools_fullStd


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


#check Int.le_add_one

unsafe def test_2 := testForw #[`Init.Data.List.Basic, `Init.Data.List.Lemmas]

unsafe def test_2_1 := test_2 (.leaf (.mk #[0,1,2,3]))


With context g(a : Int) g(as : List Int) g(bs : List Int) g(h : a ∈ as) and objects run test_2_1


open Lean Meta

unsafe def exploreCaches_stdForwSetTrie
  (moduleNames : Array Name)
  : MetaM Unit := do
    loadCacheDataS_forTest moduleNames <| fun data => do
        SetTrieP.pp
          0 (fun x => do PaInG.ppS (← getLCtx) (← getLocalInstances) x [] 0)
          (fun v => do return (match v.name with | .inl v => v.toString | .inr v => v.name.toString))
          data.data.stdForwSetTrie


#eval exploreCaches_stdForwSetTrie #[`Init.Data.List.Basic, `Init.Data.List.Lemmas]

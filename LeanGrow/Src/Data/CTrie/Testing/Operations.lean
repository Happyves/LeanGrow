/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/


import LeanGrow.Src.Data.CTrie.Operations
import LeanGrow.Src.Data.CTrie.Testing.Basic


open CTrie

#eval ctrie_1.toList
#eval ctrie_2.toList
#eval ctrie_3.toList

#eval CTrie.intersect (fun x _ => x) ctrie_1 ctrie_2
#eval CTrie.intersect (fun x _ => x) ctrie_1 ctrie_3
#eval CTrie.intersect (fun x _ => x) ctrie_1 {}


#eval CTrie.CountCommon ctrie_1 ctrie_2
#eval CTrie.CountCommon ctrie_1 ctrie_3
#eval CTrie.CountCommon ctrie_1 {}

#eval CTrie.intersect_val ctrie_1 ctrie_2
#eval CTrie.intersect_val ctrie_1 ctrie_3
#eval CTrie.intersect_val ctrie_1 {}


#eval (CTrie.merge_count ctrie_1 ctrie_2)
#eval (CTrie.merge_count ctrie_1 ctrie_3)
#eval (CTrie.merge_count ctrie_1 {})

#eval (CTrie.difference ctrie_1 ctrie_2)
#eval (CTrie.difference ctrie_1 ctrie_3)
#eval (CTrie.difference ctrie_1 {})


#eval OptionProd.toOptionofProd <| CTrie.find_max  (CTrie.merge_count (CTrie.merge_count_initialise ctrie_1) (CTrie.merge_count_initialise  ctrie_2))
#eval OptionProd.toOptionofProd <| CTrie.find_max  (CTrie.merge_count (CTrie.merge_count_initialise ctrie_1) (CTrie.merge_count_initialise  ctrie_3))
#eval OptionProd.toOptionofProd <| CTrie.find_max  (CTrie.merge_count (CTrie.merge_count_initialise ctrie_1) {})

#eval OptionProd.toOptionofProd <| (CTrie.find_maxes (CTrie.merge_count (CTrie.merge_count_initialise ctrie_1) (CTrie.merge_count_initialise  ctrie_2)))
#eval OptionProd.toOptionofProd <| (CTrie.find_maxes (CTrie.merge_count (CTrie.merge_count_initialise ctrie_1) (CTrie.merge_count_initialise  ctrie_3)))
#eval OptionProd.toOptionofProd <| (CTrie.find_maxes (CTrie.merge_count (CTrie.merge_count_initialise ctrie_1) {}))


#check1

def dbg1 := CTrie.ofList <| .cons "HAdd.hadd" 1 <| .cons "HSub.hsub" 2 <| .cons "HMul.hmul" 2 .nil
def dbg2 := CTrie.ofList <| .cons "HAdd.hadd" 7 .nil

#eval (CTrie.merge (fun x y => x + y) dbg1 dbg2).toList

def dbg3 := CTrie.ofList <| .cons "ba" 1 .nil
def dbg4 := CTrie.ofList <| .cons "banjo" 2 .nil

#eval dbg3
#eval dbg4

#eval (CTrie.merge (fun x y => x + y) dbg3 dbg4).toList

def dbg5 := CTrie.ofList <| .cons "ba" 1 .nil
def dbg6 := CTrie.ofList <| .cons "banjo" 2 <| .cons "else" 2 .nil

#eval dbg5
#eval dbg6

#eval (CTrie.merge (fun x y => x + y) dbg6 dbg5).toList

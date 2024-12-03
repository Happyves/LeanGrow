
import LeanGrow.F.Utils.CExprTrie.Build
import LeanGrow.F.Utils.CExprTrie.Query
import LeanGrow.F.Utils.CExprTrie.Delete
import LeanGrow.F.Utils.CExprTrie.Unify
import LeanGrow.F.Utils.CExprTrie.BuildRW


open Lean

def test_list : List (Nat × CExpr) :=
  [(1, .app (.app (.const `a []) (.const `b [])) (.const `c [])),
   (4, .app (.app (.const `a []) (.const `b [])) (.const `d [])),
   (42, .app (.app (.const `a []) (.const `e [])) (.const `c [])),
   (37, .forallE `dummy (.const `x []) (.const `y []) .default)
  ]

#eval CExprTrie.ofList test_list
#eval CExprTrie.build (CExprTrie.ofList test_list)


#eval CExprTrie.find? (.app (.app (.const `a []) (.const `e [])) (.const `c [])) (CExprTrie.ofList test_list)

#eval CExprTrie.deleteCExpr (.app (.app (.const `a []) (.const `b [])) (.const `d [])) (CExprTrie.ofList test_list)
#eval CExprTrie.build (CExprTrie.deleteCExpr (.app (.app (.const `a []) (.const `b [])) (.const `d [])) (CExprTrie.ofList test_list))


#eval CExprTrie.unify_reconstruct (CExprTrie.unify_candidates (CExprTrie.ofList test_list) (.app (.lnode 0 (.ofBvar 42) .none) (.lnode 1 (.ofBvar 42) .none)))
#eval CExprTrie.unify_reconstruct (CExprTrie.unify_candidates (CExprTrie.ofList test_list) (.app (.lnode 0 (.ofBvar 42) .none) (.const `d [])))


#eval CExprTrie.find_occurences (.const `a []) (CExprTrie.ofList test_list)
#eval CExprTrie.find_occurences (.app (.const `a []) (.const `b [])) (CExprTrie.ofList test_list)



#eval CExprTrie.unify_occurences (.app (.const `a []) (.lnode 1 (.ofBvar 42) .none)) (CExprTrie.ofList test_list)
#eval CExprTrie.unify_occurences (.app (.lnode 0 (.ofBvar 42) .none) (.const `d [])) (CExprTrie.ofList test_list)
#eval CExprTrie.unify_occurences (.app (.lnode 0 (.ofBvar 42) .none) (.lnode 1 (.ofBvar 42) .none)) (CExprTrie.ofList test_list)


#eval CExprTrie.factor (CExprTrie.ofList test_list) 4 []
#eval CExprTrie.factor (CExprTrie.ofList test_list) 4 [.apf]
#eval CExprTrie.factor (CExprTrie.ofList test_list) 4 [.apf, .apf]
#eval CExprTrie.factor (CExprTrie.ofList test_list) 4 [.apf, .apa]
#eval CExprTrie.factor (CExprTrie.ofList test_list) 4 [.apa]

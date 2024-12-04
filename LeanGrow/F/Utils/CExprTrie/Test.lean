
import LeanGrow.F.Utils.CExprTrie.Build
import LeanGrow.F.Utils.CExprTrie.Query
import LeanGrow.F.Utils.CExprTrie.Delete
import LeanGrow.F.Utils.CExprTrie.Unify
import LeanGrow.F.Utils.CExprTrie.BuildRW
import LeanGrow.F.Utils.CExprTrie.Merge
import LeanGrow.F.Utils.CExprTrie.Intersect



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


def test_list' : List (Nat × CExpr) :=
  [(1, .app (.app (.const `a []) (.const `b [])) (.const `c [])),
   (2, .app (.app (.const `a []) (.const `b [])) (.const `d [])),
   (3, .app (.app (.const `a []) (.const `e [])) (.const `c [])),
   (4, .forallE `dummy (.const `x []) (.const `y []) .default)
  ]

def test_list_2 : List (Nat × CExpr) :=
  [(1, .app (.app (.const `a []) (.const `b [])) (.const `w [])),
   (2, .forallE `dummy (.const `x []) (.app (.bvar 0) (.const `y [])) .default),
   (3, .app (.app (.const `a []) (.const `b [])) (.const `d []))
  ]

#eval CExprTrie.build (CExprTrie.merge (CExprTrie.ofList test_list') (CExprTrie.ofList test_list_2) (fun n => n+4))


def test_list_3 : List (Nat × CExpr) :=
  [(1, .app (.app (.const `a []) (.const `b [])) (.const `w [])),
   (2, .app (.app (.const `a []) (.const `e [])) (.const `c []))
  ]

#eval CExprTrie.contains (CExprTrie.merge (CExprTrie.ofList test_list') (CExprTrie.ofList test_list_2) (fun n => n+4)) (CExprTrie.ofList test_list_3)
#eval CExprTrie.contains (CExprTrie.ofList test_list') (CExprTrie.ofList test_list_3)



#check 2

def printList (L : List α) (print : α → String) : String :=
  "[" ++ (String.intercalate "," (L.map print)) ++ "]"

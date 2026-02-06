


#check List.Perm


theorem test_1 : [1,2,3].Perm [3,2,1] := by
  constructor
  all_goals sorry


#print test_1


theorem test_2 : ∃ n, n = 42 := by
  constructor
  · exact  rfl

#print test_2

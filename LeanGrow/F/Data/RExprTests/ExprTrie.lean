

#check 1


/-
For rewriting:
Have rw constructor that points to a rewrite equivalence class, and contains
the indices of the expressions stored, as with lit const bvar etc...
To rinf `find?`,  run it as before on the main tree, returning a positive answer for
rw nodes, so that by intersecting the indices, we end up with: the possibly maching expressions,
the rest of the query expression to match together with the rerwite class pointer.
Then we simply try to `find?` the remaining term in the rewrite class.
-/



#check 1


/-
Should build the ltx cexprs from the LocalContext provided by the frontend.
**Important**: produce only CExpr.gnode (g for global ; name is very bad because we derive the global from the local context :<)

Note:
- maybe we can do this jsu as in `ofTypeExpr` by finding a way, in the frontend,
  to get the type of the theorem to be proven ?
-/

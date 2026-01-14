

import LeanGrow.Src.Caching.Query.TestTools


open Lean Meta


#check StructureInfo
#check mkProjection

#check ConstantInfo.inductInfo
#check isStructure


#check simpExtension


#check Ext.extExtension

#check getSimpTheorems
#check SimpTheorems


/-
Todo:
- check if Projs and simpthms are in env consants, add test to ImportExport
- better balcklisting for caching (no recursers etc...)
- test and debug

-/

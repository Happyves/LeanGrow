import Lake
open System Lake DSL

package LeanGrow where

require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "v4.25.0-rc2"

@[default_target]
lean_lib LeanGrow where
  --precompileModules := true --causes mathlib to rebuild ....

lean_exe buildMe where
  root := `LeanGrow.Exec.Main
  supportInterpreter := true


input_file Cffi.c where
  path := "LeanGrow" / "FFI" / "Cffi.c"
  text := true


target Cffi.o pkg : FilePath := do
  let srcJob ← Cffi.c.fetch
  let oFile := pkg.buildDir / "LeanGrow" / "FFI" / "Cffi.o"
  buildFileAfterDep oFile srcJob fun srcFile => do
      let flags := #["-I", toString (← getLeanIncludeDir), "-fPIC"]
      compileO oFile srcFile flags


target libCffi pkg : FilePath := do
  let ffiO ← Cffi.o.fetch
  let name := nameToStaticLib "Cffi"
  buildStaticLib (pkg.staticLibDir / name) #[ffiO]


lean_lib LeanGrow.FFI.Lffi where
  precompileModules := true
  moreLinkObjs := #[libCffi]

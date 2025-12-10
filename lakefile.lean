import Lake
open System Lake DSL

package LeanGrow where

require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "v4.25.0-rc2"

@[default_target]
lean_lib LeanGrow where
  precompileModules := true

lean_exe buildMe where
  root := `LeanGrow.Exec.Main
  supportInterpreter := true

lean_lib LeanGrow.FFI.FFI

input_file dummy.c where
  path := "LeanGrow" / "FFI" / "C" / "dummy.c"
  text := true

--input_file stuff.c where
--  path := "LeanGrow" / "FFI" / "C" / "stuff.c"
--  text := true

target dummy.o pkg : FilePath := do
  let srcJob ← dummy.c.fetch
  let oFile := pkg.buildDir / "LeanGrow" / "FFI" / "C" / "dummy.o"
  buildFileAfterDep oFile srcJob fun srcFile => do
      let flags := #["-I", toString (← getLeanIncludeDir), "-fPIC"]
      compileO oFile srcFile flags

--target stuff.o pkg : FilePath := do
--  let srcJob ← stuff.c.fetch
--  let oFile := pkg.buildDir / "LeanGrow" / "FFI" / "C" / "stuff.o"
--  buildO oFile srcJob #[] #["-fPIC"] "cc"
    -- fix this wrt above

target libdummy pkg : FilePath := do
  let ffiO ← dummy.o.fetch
  let name := nameToStaticLib "dummy"
  buildStaticLib (pkg.staticLibDir / name) #[ffiO]

--target libstuff pkg : FilePath := do
--  let ffiO ← stuff.o.fetch
--  let name := nameToStaticLib "stuff"
--  buildStaticLib (pkg.staticLibDir / name) #[ffiO]

lean_lib LeanGrow.FFI.Lean.Dummy where
  moreLinkObjs := #[libdummy]--, libstuff]

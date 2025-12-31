/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import LeanGrow.Src.Utils.Cfold
import Lean.Meta.Eval
import Lean.Elab

open Lean Elab Meta



inductive TracingFlags where
| zero | one | two | three | four | five | six | seven | eight | nine | ten | eleven | twelve | thirteen
deriving BEq, Inhabited, Repr

def TracingFlags.all : List TracingFlags := [.zero, .one, .two, .three, .four, .five, .six, .seven, .eight, .nine, .ten, .eleven, .twelve, .thirteen]

def TracingFlags.none : List TracingFlags := []

inductive TracingMode where
| off | std | hard
deriving BEq, Inhabited, Repr

structure TracingExt where
  mode : TracingMode
  traces : NameMap (List TracingFlags)
deriving Inhabited, Repr


initialize TracingExtImpl : EnvExtension TracingExt ← registerEnvExtension (pure ⟨.off, {}⟩)

def TracingMode.set {m} [MonadEnv m] (mode : TracingMode) : m Unit :=
  modifyEnv (fun env => TracingExtImpl.modifyState env (fun y => {y with mode := mode}))

elab "tracing_mode" m:term : command => unsafe Command.liftTermElabM do
  let M ← Term.elabTermAndSynthesize m  <| .some (.const `TracingMode [])
  let M ← evalExpr TracingMode (.const `TracingMode []) M
  M.set


@[inline] def tracingSetFalgs {m} [MonadEnv m] (flags : List (Name × List TracingFlags)) : m Unit :=
  let built := flags.foldl (fun B (n,f) => B.insert n f) {}
  modifyEnv (fun env => TracingExtImpl.modifyState env (fun y => {y with traces := built}))

elab "tracing_flags" m:term : command => unsafe Command.liftTermElabM do
  let T : Expr := (Expr.const `List [0]).app ((Expr.const `Prod [0,0]).app (.const `Lean.Name []) |>.app ((Expr.const `List [0]).app (.const `TracingFlags [])))
  let M ← Term.elabTermAndSynthesize m  <| .some T
  let M ← evalExpr (List (Name × List TracingFlags)) T M
  tracingSetFalgs M


def traceActive? {m} [Monad m] [MonadEnv m] (dec : Name) : m (TracingMode × List TracingFlags) := do
  let traceState := TracingExtImpl.getState (← getEnv)
  match traceState.mode with
  | m@.off => return (m,[])
  | m =>
      match traceState.traces.find? dec with
      | .none => return (m,[])
      | .some Fs => return (m,Fs)


macro "mtracing" : doElem =>
  let ltf := mkIdent `local_mtracing_active
  let ltm := mkIdent `local_mtracing_mode
  `(doElem|let ($ltf,$ltm) := traceActive? decl_name%)



open IO Process FS System

@[inline] def findLeanGrowTraceFile : IO Handle := do
  let here ← getCurrentDir
  let res := FilePath.join here (FilePath.toString "LeanGrow/Src/Caches")
  if ← res.pathExists
  then
    let res := FilePath.join here (FilePath.toString "LeanGrow/Src/Caches/OverflowTraces.txt")
    if ← res.pathExists
    then
      Handle.mk res Mode.append
    else
      Handle.mk res Mode.write
  else throw (IO.userError "[findLeanGrowTraceDir] The location of caches seems to have failed")

def traceHardMain (msg : String) : IO Unit := do
  let h ← findLeanGrowTraceFile
  h.putStrLn msg


def traceCondImpl {m} [Monad m] [MonadEnv m] (M : TracingMode) (Fs : List TracingFlags) (flag : TracingFlags) (condition : Bool) : m TracingMode := do
  match Fs with
  | _ :: _ =>
    if condition
    then
      if Fs.contains flag
      then return M
      else return .off
    else return .off
  | _ => return .off


macro "mtrace" "on" f:term "when" c:term "with" m:term : doElem => do
  let ltf := mkIdent `local_mtracing_active
  let ltm := mkIdent `local_mtracing_mode
  `(doElem| match ← traceCondImpl $ltm $ltf $f $c with
            | .off => pure ()
            | .std => let N := decl_name% ; dbg_trace (s!"[{N}] " ++ $m)
            | .hard => traceHardMain $m)

macro "mtrace" "on" f:term "with" m:term : doElem => do
  let ltf := mkIdent `local_mtracing_active
  let ltm := mkIdent `local_mtracing_mode
  `(doElem| match ← traceCondImpl $ltm $ltf l $f true with
            | .off => pure ()
            | .std => let N := decl_name% ; dbg_trace (s!"[{N}] " ++ $m)
            | .hard => traceHardMain $m)


macro "trace" "set" f:term "in" b:term : term =>
  let ltf := mkIdent `local_tracing_flags
  `((let $ltf := $f ; $b))


elab "trace" "on" f:term "with" m:term "in" b:term : term => do
  let ltf := mkIdent `local_tracing_flags
  let t ← `(term| (List.contains $ltf $f))
  let e ← Term.elabTermAndSynthesize t  .none
  let e ← Meta.reduce e
  match e with
  | .const n .. =>
      if n == `Bool.true
      then
        let final ← `(dbg_trace $m ; $b)
        Term.elabTermAndSynthesize final .none
      else
        if n == `Bool.false
        then
          let final ← `($b)
          Term.elabTermAndSynthesize final .none
        else
          throwError "[LeanGrow] error at elaboration for tracing"
  | _ => throwError "[LeanGrow] error at elaboration for tracing"


macro "trace" "on" f:term "when" c:term "with" m:term "in" b:term : term => do
  let ltf := mkIdent `local_tracing_flags
  let t ← `(term| (List.contains $ltf $f))
  `(let traceDummy := fun _ : Unit => $b ; if $t && $c then (dbg_trace $m ; traceDummy ()) else (traceDummy ()))

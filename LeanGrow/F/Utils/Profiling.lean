
import Lean
import Batteries.Lean.IO.Process
import Mathlib.Data.List.DropRight
import LeanGrow.F.Utils.IO

open Lean

def parse_stdout (out : String) : (Nat × Nat × Nat) :=
  let cs := out.data
  let min := List.take 2 (List.drop 1 cs)
  let sec := List.take 2 (List.drop 4 cs)
  let nano := List.rdrop (List.drop 7 cs) 2
  (String.toNat! ⟨min⟩, String.toNat! ⟨sec⟩, String.toNat! ⟨nano⟩)


def compute_time (start endit : (Nat × Nat × Nat)) : (Nat × Nat × Nat) :=
  let nano_s := ((start.1* 60) + start.2.1)*(10^9) + start.2.2
  let nano_e := ((endit.1* 60) + endit.2.1)*(10^9) + endit.2.2
  let dif := nano_e - nano_s
  let round_sec := dif / (10^9)
  let round_min := round_sec / 60
  (round_min,round_sec, dif)



def target_profile_storage := "/./home/yves/Desktop/CodeWorkspace/Lean4_General/LeanGrow/LeanGrow/Traces_Profiles/Profile.txt"


def profileCoreIO (msg : String) (term : IO α) : IO α := do
  let start ← IO.Process.runCmdWithInput "date" #["+\"%M %S %N\""]
  let y := fun _ : Unit => term
  let x ← y ()
  let endit ← IO.Process.runCmdWithInput "date" #["+\"%M %S %N\""]
  let T := compute_time (parse_stdout start) (parse_stdout endit)
  IO.FS.appendFile target_profile_storage s!"{msg} : min {T.1}, sec {T.2.1}, nano : {T.2.2}\n"
  return x

def profileCore (msg : String) (term : α) : IO α := do
  let start ← IO.Process.runCmdWithInput "date" #["+\"%M %S %N\""]
  let y := fun _ : Unit => term
  let x := y ()
  let endit ← IO.Process.runCmdWithInput "date" #["+\"%M %S %N\""]
  let T := compute_time (parse_stdout start) (parse_stdout endit)
  IO.FS.appendFile target_profile_storage s!"{msg} : min {T.1}, sec {T.2.1}, nano : {T.2.2}\n"
  return x

unsafe def profileMain {α : Type} [Inhabited α] (msg : String) (term : α) : α :=
  veryunsafeIO (profileCore msg term)


inductive ProfileFlags where
| zero | one | two | three | four | five | six | seven | eight | nine
deriving BEq, Inhabited, Repr

def ProfileFlags.all : List ProfileFlags := [.zero, .one, .two, .three, .four, .five, .six, .seven, .eight, .nine]

def ProfileFlags.off : List ProfileFlags := []

macro "gProfile" f:term "&" m:term "&" b:term : term =>
  set_option hygiene false in
  `((if (List.contains global_profiling_flags $f ) then (profileMain $m $b) else ($b)))

macro "lProfile" f:term "&" m:term "&" b:term : term =>
  set_option hygiene false in
  `((if (List.contains local_profilinging_flags $f ) then (profileMain $m $b) else ($b)))

macro "with_lProfile" f:term "in" b:term : term =>
  set_option hygiene false in
  `((let local_profilinging_flags := $f ; $b))

def global_profiling_flags := ProfileFlags.off

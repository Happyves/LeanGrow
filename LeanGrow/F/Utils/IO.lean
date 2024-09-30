

@[inline] def Except.get! {α : Type u} [Inhabited α] [ToString ε] : Except ε α → α
  | .ok x => x
  | .error e   => panic! s!"except raised error: {e}"

unsafe def veryunsafeIO {α : Type} [Inhabited α] (fn : IO α) : α := (unsafeIO fn).get!

def IO.FS.appendFile (fname : System.FilePath) (content : String) : IO Unit := do
  let h ← Handle.mk fname Mode.append
  h.putStr content

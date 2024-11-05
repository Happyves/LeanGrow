
inductive TraceFlags where
| zero | one | two | three | four | five | six | seven | eight | nine | ten | eleven | twelve | thirteen
deriving BEq, Inhabited, Repr

def TraceFlags.all : List TraceFlags := [.zero, .one, .two, .three, .four, .five, .six, .seven, .eight, .nine, .ten, .eleven, .twelve, .thirteen]

def TraceFlags.off : List TraceFlags := []

macro "gTrace" f:term "&" m:term "&" b:term : term =>
  set_option hygiene false in
  `((if (List.contains global_tracing_flags $f ) then (dbg_trace $m ; $b) else ($b)))

macro "lTrace" f:term "&" m:term "&" b:term : term =>
  set_option hygiene false in
  `((if (List.contains local_tracing_flags $f ) then (dbg_trace $m ; $b) else ($b)))

macro "with_lTrace" f:term "in" b:term : term =>
  set_option hygiene false in
  `((let local_tracing_flags := $f ; $b))


def global_tracing_flags := TraceFlags.off

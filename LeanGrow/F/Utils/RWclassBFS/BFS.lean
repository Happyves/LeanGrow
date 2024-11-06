

import LeanGrow.F.Utils.List



namespace BFS

open BFS


abbrev graph := List (Nat × List (Nat × Bool)) -- neighbour lists, with info in wich direction to take the edge

def graph_init (edge : Nat × Nat) : graph :=
  [(edge.1, [(edge.2, true)]), (edge.2, [(edge.1, false)])]


def graph_insert (g : graph) (edge : Nat × Nat) : graph :=
  let insert (vert nei : Nat) (dir : Bool) (on : graph): graph :=
    List.findModifyAdd (fun x => x.1 == vert) (fun (i,neis) => (i, (nei, dir) :: neis)) (vert,[(nei, dir)]) on
  insert edge.1 edge.2 true (insert edge.2 edge.1 false g)

def graph_ofList : List (Nat × Nat) → graph
  | [] => []
  | e :: more => graph_insert (graph_ofList more) e


def graph_neighbours (g : graph) (vert : Nat) : List (Nat × Bool) :=
  match (List.find? (fun x => x.1 == vert) g) with
  | .some (_,n) => n
  | _ => []


-- path : edge and true is this order or false if reverse
partial def bfs (source dest : Nat) (g : graph) : List ((Nat × Nat) × Bool) :=
  let rec find (done : List (Nat × Nat × Bool)) (frontier : List Nat) : (List (Nat × Nat × Bool)) := -- (dest, source, dir)
    match frontier with
    | [] => done
    | i :: more =>
        let ns := graph_neighbours g i
        match ns.find? (fun x => x.1 == dest) with
        | .some (_,d) => find ((dest,i,d) :: done) []
        | .none =>
            let toDone := ns.map (fun (n,d) => (n,i,d))
            let toFront := (ns.map (fun x => x.1)).filter (fun n => (List.find? (fun y => y.1 == n) done).isNone)
            find (toDone ++ done) (toFront ++ more)
  let nsIni := graph_neighbours g source
  let doneIni := nsIni.map (fun (n,d) => (n,source,d))
  let found := find doneIni (nsIni.map (fun x => x.1))
  let rec backtrack (sofar : List ((Nat × Nat) × Bool)) (back : Nat) : Bool → List ((Nat × Nat) × Bool)
    | true => sofar
    | false =>
        match found.find? (fun x => x.1 == back) with
        | .some (_,parent,d) =>
            let edge := if d then (parent, back) else (back,parent)
            let next := (edge, d) :: sofar
            if parent == source then (backtrack next 42 true) else (backtrack next parent false)
        | _ => [] -- shouldn't happen
  backtrack [] dest false



end BFS


-- # tests

open BFS

/-
four cycle moving lex-up

2 → 3
↑   ↑
1 → 4

-/
def myG := graph_ofList [(1,2), (2,3), (1,4), (4,3)]

#eval bfs 1 3 myG

#eval bfs 1 4 myG

--#eval bfs 3 2 myG
-- overflow :<

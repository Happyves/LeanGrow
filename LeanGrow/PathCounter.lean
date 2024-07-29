

import LeanGrow.Quadtree

open Lean



-- requires to drop last loop edge
def walk_counter (inner_trans : Array (List (Nat × Nat))) (fuel : Nat) (a b : Nat) : List (List (List (Nat × Nat))) :=
    match fuel with
    | 0 => [if a = b then [[(a,a)]] else []]
    | n+1 =>
      let sofar := walk_counter inner_trans n a b
      match inner_trans.get? a with
      | .some l =>
            let step := Id.run do
              let mut new := []
              for c in l.map Prod.fst do
                let sf := (walk_counter inner_trans n c b).headD []
                new := (sf.map ((a,c) :: ·)) :: new
              return new.join
            step :: sofar
      | _ => []

def four_cycle_with_unit_weights := #[[(1,1),(3,1)], [(0,1),(2,1)],[(1,1), (3,1)], [(2,1), (0,1)]]

#eval walk_counter four_cycle_with_unit_weights 2 0 2
#eval walk_counter four_cycle_with_unit_weights 3 0 3


def get_total_weight (inner_trans : Array (List (Nat × Nat))) (walks : List (List (List (Nat × Nat)))) : Nat :=
  let rec walk_len : List (Nat × Nat) → Nat
    | [] => 0
    | e :: r =>
        match inner_trans.get? e.1 with
        | .some nei => match nei.find? (fun (c,_) => c = e.2) with
                        | .some (_,v) => v + (walk_len r)
                        | _ => 0
        | _ => 0
  match walks with
  | [] => 0
  | w_o_len :: rest =>
      let uno := w_o_len.map walk_len
      let dos := uno.foldl (fun s x => s+x) 0
      dos + (get_total_weight inner_trans rest)

#eval get_total_weight four_cycle_with_unit_weights (walk_counter four_cycle_with_unit_weights 2 0 2)
#eval get_total_weight four_cycle_with_unit_weights  <| walk_counter four_cycle_with_unit_weights 3 0 3
-- because looping edges are given weight 0



def weighted_walk_counter (inner_trans hyp_goal_trans : Array (List (Nat × Nat))) : Nat → Nat → Nat :=
  let first (hyp_goal_trans : Array (List (Nat × Nat))) (hc gc : Nat) : Nat :=
    match hyp_goal_trans.get? hc with
    | .some l => match l.find? (fun (c,_) => c = gc) with
                | .some (_,v) => v
                | _ => 0
    | _ => 0
  let hyp_nei_of_goal (hyp_goal_trans : Array (List (Nat × Nat))) (gc : Nat) : List Nat :=
    Id.run do
      let mut nei := []
      let mut c := 0
      for gl in hyp_goal_trans do
        if (gl.map Prod.fst).contains gc then nei := c :: nei ; c := c+1 else  c := c+1
      return nei

  fun hc gc =>
    let hnei := hyp_nei_of_goal hyp_goal_trans gc
    let whnei := (hnei.map (first hyp_goal_trans · gc)).foldl (Nat.add) 0
    let inner := Id.run do
      let mut w := 0
      for n in hnei do
        let ws := walk_counter inner_trans 5 hc n
        let ww := get_total_weight inner_trans ws
        w := w + ww
      return w
    inner + whnei

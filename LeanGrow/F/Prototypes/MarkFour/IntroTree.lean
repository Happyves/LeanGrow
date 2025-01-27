

import LeanGrow.F.Data.CExpr.Types


open Lean


inductive IntroTree where
| leaf (gids : List Nat) (ltx : List (Nat × CExpr))
| node (gids : List Nat) (ltx : List (Nat × CExpr)) (kidsWdirs : List (List Nat × IntroTree))
deriving Inhabited, Repr, BEq


namespace IntroTree

partial def addStdBack (target_id id_gen_back : Nat) (T : IntroTree) : IntroTree :=
  let rec find (done : List (List Nat × IntroTree)) (go : IntroTree → IntroTree) : List (List Nat × IntroTree) → List (List Nat × IntroTree)
    | [] => done
    | (xl,xt) :: xs =>
        if xl.contains target_id
        then (id_gen_back :: xl, go xt) :: (done ++ xs)
        else find ((xl,xt) :: done) go xs
  match T with
  | .leaf gids ltx => .leaf (id_gen_back :: gids) ltx
  | .node gids ltx kidsWdirs =>
      if gids.contains target_id
      then .node (id_gen_back :: gids) ltx kidsWdirs
      else .node gids ltx (find [] (addStdBack target_id id_gen_back) kidsWdirs)


partial def addIntroBack (target_id id_gen_back : Nat) (new : List (Nat × CExpr)) (T : IntroTree) : IntroTree :=
  let rec find (done : List (List Nat × IntroTree)) (go : IntroTree → IntroTree) : List (List Nat × IntroTree) → List (List Nat × IntroTree)
    | [] => done
    | (xl,xt) :: xs =>
        if xl.contains target_id
        then (id_gen_back :: xl, go (xt)) :: (done ++ xs)
        else find ((xl,xt) :: done) go xs
  match T with
  | .leaf gids ltx => .node gids ltx [([id_gen_back], .leaf [id_gen_back] new)]
  | .node gids ltx kidsWdirs =>
      if gids.contains target_id
      then .node gids ltx (([id_gen_back], .leaf [id_gen_back] new) :: kidsWdirs)
      else .node gids ltx (find [] (addIntroBack target_id id_gen_back new) kidsWdirs)

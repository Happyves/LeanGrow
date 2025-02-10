

import LeanGrow.F.Data.CExpr.Types


open Lean


inductive IntroTree where
| leaf (gids : List Nat) (ltx : List (Nat × CExpr))
| node (gids : List Nat) (ltx : List (Nat × CExpr)) (kidsWdirs : List (List Nat × IntroTree))
deriving Inhabited, Repr, BEq


namespace IntroTree

partial def addStdBack (target_id : Nat) (newGs : List Nat) (T : IntroTree) : IntroTree :=
  let rec find (done : List (List Nat × IntroTree)) (go : IntroTree → IntroTree) : List (List Nat × IntroTree) → List (List Nat × IntroTree)
    | [] => done
    | (xl,xt) :: xs =>
        if xl.contains target_id
        then (newGs ++ xl, go xt) :: (done ++ xs)
        else find ((xl,xt) :: done) go xs
  match T with
  | .leaf gids ltx => .leaf (newGs ++ gids) ltx
  | .node gids ltx kidsWdirs =>
      if gids.contains target_id
      then .node (newGs ++ gids) ltx kidsWdirs
      else .node gids ltx (find [] (addStdBack target_id newGs) kidsWdirs)


partial def addIntroBack (target_id : Nat) (newGs : List Nat) (new : List (Nat × CExpr)) (T : IntroTree) : IntroTree :=
  let rec find (done : List (List Nat × IntroTree)) (go : IntroTree → IntroTree) : List (List Nat × IntroTree) → List (List Nat × IntroTree)
    | [] => done
    | (xl,xt) :: xs =>
        if xl.contains target_id
        then (newGs ++ xl, go (xt)) :: (done ++ xs)
        else find ((xl,xt) :: done) go xs
  match T with
  | .leaf gids ltx => .node gids ltx [(newGs, .leaf newGs new)]
  | .node gids ltx kidsWdirs =>
      if gids.contains target_id
      then .node gids ltx ((newGs, .leaf newGs new) :: kidsWdirs)
      else .node gids ltx (find [] (addIntroBack target_id newGs new) kidsWdirs)

partial def has? (ce : CExpr) (T : IntroTree) : Bool :=
  let rec go : List IntroTree → Bool
    | [] => false
    | nx :: more =>
        match nx with
        | .leaf _ ltx =>
            match ltx.find? (fun x => x.2 == ce) with
            | .none => go more
            | _ => true
        | .node _ ltx kidsWdirs =>
            match ltx.find? (fun x => x.2 == ce) with
            | .none => go ((kidsWdirs.map Prod.snd) ++ more)
            | _ => true
  go [T]


partial def addForw (gnode_id : Nat) (ce : CExpr) (goalIds : List Nat) (T : IntroTree) : IntroTree :=
  let rec find (gIdsam : Nat) (done : List (List Nat × IntroTree)) (go : IntroTree → IntroTree) : List (List Nat × IntroTree) → List (List Nat × IntroTree)
    | [] => done
    | (xl,xt) :: xs =>
        if xl.contains gIdsam
        then (xl, go (xt)) :: (done ++ xs)
        else find gIdsam ((xl,xt) :: done) go xs
  let rec go (gIdsam : Nat) : IntroTree → IntroTree
    | .leaf IDS ltx =>
        if IDS.contains gIdsam
        then .leaf IDS ((gnode_id, ce) :: ltx)
        else .leaf IDS ltx
    | .node IDS ltx kidsWdirs =>
        if IDS.contains gIdsam
        then .node IDS ((gnode_id, ce) :: ltx) kidsWdirs
        else .node IDS ltx (find gIdsam [] (go gIdsam) kidsWdirs)
  match goalIds with
  | [] => .leaf [] []
  | h :: _ => go h T


def addForws (On : List (Nat × CExpr × List Nat)) (T : IntroTree) : IntroTree :=
  On.foldl (fun sf (a,b,c) => sf.addForw a b c) T


partial def foldForwRW (fid : Nat) (T : IntroTree) (mod : Nat → List (Nat × CExpr) → Nat × List (Nat × CExpr) × List (Nat × Nat × CExpr))
  : Nat × IntroTree × List (Nat × CExpr) × List (Nat × Nat × CExpr) :=
  let rec go (f : Nat) : IntroTree → Nat × IntroTree × List (Nat × CExpr) × List (Nat × Nat × CExpr)
    | .leaf gids ltx =>
        let (nf,ngn,nas) := mod f ltx
        (nf, .leaf gids (ngn ++ ltx), ngn,nas)
    | .node gids ltx kidsWdirs =>
        let (lf,lgn,las) := mod f ltx
        let (nf,ngn,nas,nk) := kidsWdirs.foldl (fun (inf,ign,ias,ik) (dirs,kid) =>
          let (Inf,IT,Ign,Ias) := go inf kid
          (Inf,Ign ++ ign, Ias ++ias, (dirs,IT) :: ik)
          ) (lf,lgn,las, [])
        (nf, .node gids (ngn ++ ltx) nk, ngn, nas)
  go fid T

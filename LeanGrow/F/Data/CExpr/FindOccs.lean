
import LeanGrow.F.Data.CExpr.Types
import LeanGrow.F.Utils.List

open Lean


inductive OccInstruction where
| appl | appr
| lamt | lamb
| allt | allb
| lett | letv | letb
| proj
deriving BEq, Inhabited, Repr

def CExpr.find_occurences (of within : CExpr) : List (List OccInstruction) :=
  let rec go (current : CExpr) (sofar: List OccInstruction) : List (List OccInstruction) :=
    match current with
    | .app f a  =>
          if current == of
          then
            [sofar]
          else
            (go f (.appl :: sofar)) ++ (go a (.appr :: sofar))
    | .lam _ f a _ =>
          if current == of
          then
            [sofar]
          else
            (go f (.lamt :: sofar)) ++ (go a (.lamb :: sofar))
    | .forallE _ f a _ =>
          if current == of
          then
            [sofar]
          else
            (go f (.allt :: sofar)) ++ (go a (.allb :: sofar))
    | .letE _ f a z _ =>
          if current == of
          then
            [sofar]
          else
            (go f (.lett :: sofar)) ++ (go a (.letv :: sofar)) ++ (go z (.letv :: sofar))
    | .proj _ _ a  =>
          if current == of
          then
            [sofar]
          else
            (go a (.proj :: sofar))
    | _ =>
          if current == of
          then
            [sofar]
          else
            []
  go within []


def CExpr.modify_wOccIns (mod : CExpr → CExpr) : List OccInstruction → CExpr → CExpr
  | [], ce => mod ce
  | .appl :: more, .app f a => .app (CExpr.modify_wOccIns mod more f) a
  | .appr :: more, .app f a => .app f (CExpr.modify_wOccIns mod more a)
  | .lamt :: more, .lam n f a i => .lam n (CExpr.modify_wOccIns mod more f) a i
  | .lamb :: more, .lam n f a i => .lam n f (CExpr.modify_wOccIns mod more a) i
  | .allt :: more, .forallE n f a i => .forallE n (CExpr.modify_wOccIns mod more f) a i
  | .allb :: more, .forallE n f a i => .forallE n f (CExpr.modify_wOccIns mod more a) i
  | .lett :: more, .letE n f a z i => .letE n (CExpr.modify_wOccIns mod more f) a z i
  | .letv :: more, .letE n f a z i => .letE n f (CExpr.modify_wOccIns mod more a) z i
  | .letb :: more, .letE n f a z i => .letE n f a (CExpr.modify_wOccIns mod more z) i
  | .proj :: more, .proj n i e => .proj n i (CExpr.modify_wOccIns mod more e)
  | _, e => e

def testExpr_of : CExpr := .app (.const `a []) (.const `b [])


def testExpr_within : CExpr :=
  .app testExpr_of (.lam `n (.app testExpr_of (.const `c [])) (.app (.const `b []) (.const `a [])) .default)


#eval CExpr.find_occurences testExpr_of testExpr_within

#eval CExpr.modify_wOccIns (fun _ => (.const `d [])) [OccInstruction.appl, OccInstruction.lamt, OccInstruction.appr].reverse testExpr_within


inductive FindOccsState where
| eq | neq | jump (l : List (CExpr × List OccInstruction))

private def largest_match (of within : CExpr) : FindOccsState :=
  let rec go (sofar: List OccInstruction) : CExpr → CExpr → FindOccsState
    | .app f a, .app f' a' =>
          let rf := go (.appl :: sofar) f f'
          let ra := go (.appr :: sofar) a a'
          match rf , ra with
          | .eq, .eq => .eq
          | .jump L, .jump l => .jump (L ++ l)
          | _ , .jump l => .jump l
          | .jump l, _ => .jump l
          | _, _ => .neq
    | .lam _ f a _, .lam _ f' a' _ =>
          let rf := go (.lamt :: sofar) f f'
          let ra := go (.lamb :: sofar) a a'
          match rf , ra with
          | .eq, .eq => .eq
          | .jump L, .jump l => .jump (L ++ l)
          | _ , .jump l => .jump l
          | .jump l, _ => .jump l
          | _, _ => .neq
    | .forallE _ f a _, .forallE _ f' a' _  =>
          let rf := go (.allt :: sofar) f f'
          let ra := go (.allb :: sofar) a a'
          match rf , ra with
          | .eq, .eq => .eq
          | .jump L, .jump l => .jump (L ++ l)
          | _ , .jump l => .jump l
          | .jump l, _ => .jump l
          | _, _ => .neq
    | .letE _ f a z _, .letE _ f' a' z' _  =>
          let rf := go (.lett :: sofar) f f'
          let ra := go (.letv :: sofar) a a'
          let rz := go (.letb :: sofar) z z'
          match rf , ra, rz with
          | .eq, .eq , .eq => .eq
          | .jump L, .jump l, .jump l' => .jump (L ++ l ++ l')
          | .jump L, .jump l, _ => .jump (L ++ l)
          | .jump L, _, .jump l => .jump (L ++ l)
          | _, .jump L, .jump l => .jump (L ++ l)
          | _ , _, .jump l => .jump l
          | _, .jump l, _ => .jump l
          | .jump l, _, _ => .jump l
          | _, _, _ => .neq
    | .proj _ _ e, .proj _ _ e' => go (.proj :: sofar) e e'
    | .lit l, .lit L => if l == L then .eq else .neq
    | _, .lit _ => .neq
    | .const n _, .const N _ => if n == N then .eq else .neq
    | _, .const _ _ => .neq
    | .sort l, .sort L => if l == L then .eq else .neq
    | _, .sort _ => .neq
    | .bvar l, .bvar L => if l == L then .eq else .neq
    | _, .bvar _=> .neq
    | .lnode l _ t, .lnode L _ T => if l == L && t == T then .eq else .neq
    | _, .lnode _ _ _ => .neq
    | .gnode l _, .gnode L _ => if l == L then .eq else .neq
    | _, .gnode _ _ => .neq
    | ce, .app f' a' =>
          let rf := go (.appl :: sofar) ce f'
          let ra := go (.appr :: sofar) ce a'
          match rf , ra with
          | .eq, .eq => .jump ((f', .appl :: sofar) :: (a', .appr :: sofar) :: [])
          | .eq, .jump l => .jump ((f', .appl :: sofar) :: l)
          | .jump L, .eq => .jump ((a', .appr :: sofar) :: L)
          | .jump L, .jump l => .jump (L ++ l)
          | _ , .jump l => .jump l
          | .jump l, _ => .jump l
          | _, .eq => .jump [(a', .appr :: sofar)]
          | .eq, _ => .jump [(f', .appl :: sofar)]
          | _, _ => .jump []
    | ce, .lam _ f' a' _ =>
          let rf := go (.lamt :: sofar) ce f'
          let ra := go (.lamb :: sofar) ce a'
          match rf , ra with
          | .eq, .eq => .jump ((f', .lamt :: sofar) :: (a', .lamb :: sofar) :: [])
          | .eq, .jump l => .jump ((f', .lamt :: sofar) :: l)
          | .jump L, .eq => .jump ((a', .lamb :: sofar) :: L)
          | .jump L, .jump l => .jump (L ++ l)
          | _ , .jump l => .jump l
          | .jump l, _ => .jump l
          | _, .eq => .jump [(a', .lamb :: sofar)]
          | .eq, _ => .jump [(f', .lamt :: sofar)]
          | _, _ => .jump []
    | ce, .forallE _ f' a' _ =>
          let rf := go (.allt :: sofar) ce f'
          let ra := go (.allb :: sofar) ce a'
          match rf , ra with
          | .eq, .eq => .jump ((f', .allt :: sofar) :: (a', .allb :: sofar) :: [])
          | .eq, .jump l => .jump ((f', .allt :: sofar) :: l)
          | .jump L, .eq => .jump ((a', .allb :: sofar) :: L)
          | .jump L, .jump l => .jump (L ++ l)
          | _ , .jump l => .jump l
          | .jump l, _ => .jump l
          | _, .eq => .jump [(a', .lamb :: sofar)]
          | .eq, _ => .jump [(f', .allb :: sofar)]
          | _, _ => .jump []
    -- todo let and proj ; but largest_match is useless since flawed
    | _, r => .jump [(r, sofar)]
  go [] of within


/-
flaw:
within →  b a a a
of → b a a
will jump to b and miss the inner occurence
-/



partial def CExpr.find_occurences' (of within : CExpr) : List (List OccInstruction) :=
  let rec go (current : CExpr) (sofar: List OccInstruction) : List (List OccInstruction) :=
    let res := largest_match of current
    match res with
    | .eq => [sofar]
    | .neq => []
    | .jump next => (next.map (fun (ce, road) => go ce (sofar ++ road.reverse))).join
  go within []



--#eval CExpr.find_occurences' testExpr_of testExpr_within
-- overflow :<

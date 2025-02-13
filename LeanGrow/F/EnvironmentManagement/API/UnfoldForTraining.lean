
import Lean
import LeanGrow.F.EnvironmentManagement.SampleRegular.Types
--import LeanGrow.F.Utils.Trie.CTrie
import LeanGrow.F.Data.CExpr.API
import Init.Data.Array.Basic

open Lean Meta

/-
API to work with files to be used as training, but without considering them to be imported by grow,
There are two aspects to this:
- we do want to produce states, but for these states to not contain declarations from files that
  won't be imported
- we don't want to create states, but simply subproofs of substatements, in which we unfold the
  declarations of files that won't be imported, for the purpose of creating exercises for RL.
-/

def Array.reduceOption (a : Array (Option α)) : Array α := Array.filterMap id a -- versioning


def Option.map₂ (x y : Option α) (f : α → α → α) : Option α :=
  match x, y with
  | .some a, .some b => .some (f a b)
  | _, _ => .none

def Option.map₃ (x y z : Option α) (f : α → α → α → α) : Option α :=
  match x, y, z with
  | .some a, .some b, .some c => .some (f a b c)
  | _, _, _ => .none


partial def unfoldWrtEnv (allowed extEnv : ConstMap) (e : Expr) : Option Expr :=
  let rec go : Expr → Option Expr -- optimize
    | .app f a => Option.map₂ (go f) (go a) (.app · ·)
    | .lam n f a i => Option.map₂ (go f) (go a) (.lam n · · i)
    | .forallE n f a i => Option.map₂ (go f) (go a) (.forallE n · · i)
    | .letE n f a z i => Option.map₃ (go f) (go a) (go z) (.letE n · · · i)
    | .proj n i f => Option.map (.proj n i · ) (go f)
    | .mdata _ f => (go f)
    | .const n l =>
        match allowed.find? n with
        | .some _ => .some (.const n l)
        | .none =>
            match extEnv.find? n with
            | .some info =>
                match info with
                | .defnInfo v => go v.value
                | _ => .none
                -- Since this will be used on types, we fail if type contains proofs,
                -- or inductive declarations, for example, in which case the sample
                -- really isn't suitable anyway ?
            | .none => .none
    | x => x
  go e

#check Environment.constants

#check ConstantInfo



def translateForSample_training (allowed extEnv : ConstMap) (dict : List (FVarId × Nat)) (e : Expr) : Option CExpr :=
  let rec go : Expr → CExpr -- optimize
    | .app f a => .app (go f) (go a)
    | .lam n f a i => .lam n (go f) (go a) i
    | .forallE n f a i => .forallE n (go f) (go a) i
    | .letE n f a z i => .letE n (go f) (go a) (go z) i
    | .proj n i f => .proj n i (go f)
    | .mdata _ f => (go f)
    | .fvar id =>
        match dict.find? (fun x => x.1 == id) with
        | .some (_,mid) => .lnode mid (.ofFvar id) .none
        | .none => .failed
    | .bvar i => .bvar i
    | .mvar _ => .failed
    | .lit l => .lit l
    | .const n l =>
          let ok? := unfoldWrtEnv allowed extEnv (.const n l)
          match ok? with
          | .some e => e.toCExprF -- as it won't contain free vars
          | _ => .failed
    | .sort u => .sort u
  let res := go e
  if res.hasFailed then .none else .some res

def translateLocalContext_training (allowed extEnv : ConstMap) (ltx : LocalContext) (goal : Expr) : Option (CExpr × List (Nat × CExpr)) :=
  let Ltx := ltx.decls.toArray.reduceOption
  let (dict, mltx) := (Array.range (Ltx.size)).foldl
    (fun (d,l) i =>
      let decl := Ltx.get! (i)
      let T := translateForSample_training allowed extEnv d decl.type
      match T with
      | .some t => ((decl.fvarId, i) :: d, (i,t) :: l)
      | _ => ([],[])
      )
    ([],[])
  let G := translateForSample_training allowed extEnv dict goal
  match G with
  | .some g => .some (g,mltx) -- possibly empty context if there was a failure ?!?
  | _ => .none


-- TODO: Finally, we should discard samples, even if hyps and goal have passed unfolding,
-- if the theorem name of the sample is not among the allowed enviroenment!


/-
Actually, the above approach is kind of shit...
- For types containing proofs, experiment with replacing them with an fvar/gnode and
  adding a binding so that this new fvar/gnodes type is that of the proof (keep "unfold"
  on that type though)
- For inductive types and associated recursors, replace them with fvar/gnode who's type
  is thier type (ex : `Sort 1`), and recursors - though they should almost never appear
  in types - shouls also be abstracted this way
- Durring sampling, "skip" thms not in the actual environements.. or abstract them ...


Other aspects:
- check if proofs contain sorry, and if they do discard them entirely ?
-/

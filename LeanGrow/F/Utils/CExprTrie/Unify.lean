
import LeanGrow.F.Utils.CExprTrie.Types
import LeanGrow.F.Utils.List


open Lean

namespace CExprTrie

partial def build (T : CExprTrie) : List (CExpr × List Nat) :=
  match T with
  | .dead => []
  | .br lnodes gnodes bvars sorts consts lits apf apa _ laf laa _ alf ala _ lef lea lez _ projs =>
      let fs := CExprTrie.build apf
      let as := CExprTrie.build apa
      let app_res : List (CExpr × List Nat) :=
        (fs.foldl (fun x y =>
          (as.foldl (fun X Y =>
            let inter := List.orderedIntersect (· ≤ ·) y.2 Y.2
            match inter with
            | [] => X
            | _ => (.app y.1 Y.1, inter) :: X
            )
            []) :: x
          )
          []).join
      let fs := CExprTrie.build laf
      let as := CExprTrie.build laa
      let lam_res : List (CExpr × List Nat) :=
        (fs.foldl (fun x y =>
          (as.foldl (fun X Y =>
            let inter := List.orderedIntersect (· ≤ ·) y.2 Y.2
            match inter with
            | [] => X
            | _ => (.lam `dummy y.1 Y.1 .default, inter) :: X
              -- wonder whether this can cause problems...
              -- We should ignore name and Binderinfo everywhere too
            )
            []) :: x
          )
          []).join
      let fs := CExprTrie.build alf
      let as := CExprTrie.build ala
      let all_res : List (CExpr × List Nat) :=
        (fs.foldl (fun x y =>
          (as.foldl (fun X Y =>
            let inter := List.orderedIntersect (· ≤ ·) y.2 Y.2
            match inter with
            | [] => X
            | _ => (.forallE `dummy y.1 Y.1 .default, inter) :: X
            )
            []) :: x
          )
          []).join
      let fs := CExprTrie.build lef
      let as := CExprTrie.build lea
      let zs := CExprTrie.build lez
      let let_res : List (CExpr × List Nat) :=
        (fs.foldl (fun x y =>
          (as.foldl (fun X Y =>
            (zs.foldl (fun z Z =>
              let interim := List.orderedIntersect (· ≤ ·) y.2 Y.2
              let inter := List.orderedIntersect (· ≤ ·) Z.2 interim
              match inter with
              | [] => z
              | _ => (.letE `dummy y.1 Y.1 Z.1 true, inter) :: z
              )
            []) :: X
            )
            []).join :: x
          )
          []).join
      let proj_res : List (CExpr × List Nat) := (projs.map (fun x => (CExprTrie.build x.2.2.2).map (fun (a,b) => (.proj x.2.1 x.2.2.1 a, b)))).join
      let ln_res : List (CExpr × List Nat) := lnodes.map (fun (ind,i,t) => (.lnode i (.ofBvar 42) t, ind))
      let gn_res : List (CExpr × List Nat) := gnodes.map (fun (ind,i) => (.gnode i (.ofBvar 42), ind))
      let bv_res : List (CExpr × List Nat) := bvars.map (fun (ind,i) => (.bvar i, ind))
      let sort_res : List (CExpr × List Nat) := sorts.map (fun (ind,i) => (.sort i , ind))
      let lit_res : List (CExpr × List Nat) := lits.map (fun (ind,i) => (.lit i , ind))
      let const_res : List (CExpr × List Nat) := consts.map (fun (ind,n,l) => (.const n l, ind))
      app_res ++ lam_res ++ all_res ++ let_res ++ proj_res ++ ln_res ++ gn_res ++ bv_res ++ sort_res ++ lit_res ++ const_res


def done_prune
  (ind : List Nat) (done : List (Nat × List (CExpr × List Nat))) : List (Nat × List (CExpr × List Nat)) :=
  let rec process_inner (final : List (CExpr × List Nat)) : List (CExpr × List Nat) → List (CExpr × List Nat)
    | [] => final
    | (n,l) :: more =>
        match List.orderedIntersect (· ≤ ·) ind l with
        | [] => process_inner (final) more
        | I => process_inner ((n,I) :: final) more
  let rec process_outer (final : List (Nat × List (CExpr × List Nat))) : List (Nat × List (CExpr × List Nat)) → List (Nat × List (CExpr × List Nat))
    | [] => final
    | (n,l) :: more =>
        match process_inner [] l with
        | [] => process_outer final more
        | res => process_outer ((n,res) :: final) more
  process_outer [] done


partial def unify_candidates (T : CExprTrie) (ce : CExpr) : List (Nat × List (CExpr × List Nat)) :=
  let rec go (done : List (Nat × List (CExpr × List Nat))) : List (CExpr × CExprTrie) → List (Nat × List (CExpr × List Nat))
    | [] => done
    | (nx, link) :: more =>
        match nx with
        | .failed => []
        | .app f a =>
            match link with
            | .br _ _ _ _ _ _ apf apa _ _ _ _ _ _ _ _ _ _ _ _ =>
                go done ((f, apf) :: (a, apa) :: more)
            | _ => []
        | .lam _ f a _ =>
            match link with
            | .br _ _ _ _ _ _ _ _ _ laf laa _ _ _ _ _ _ _ _ _ =>
                go done ((f, laf) :: (a, laa) :: more)
            | _ => []
        | .forallE _ f a _ =>
            match link with
            | .br _ _ _ _ _ _ _ _ _ _ _ _ alf ala _ _ _ _ _ _ =>
                go done ((f, alf) :: (a, ala) :: more)
            | _ => []
        | .letE _ f a z _ =>
            match link with
            | .br _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lef lea lez _ _ =>
                go done ((f, lef) :: (a, lea) :: (z, lez) :: more)
            | _ => []
        | .proj n i e =>
            match link with
            | .br _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ projs =>
                let found := List.find? (fun x => x.2.1 == n && x.2.2.1 == i) projs
                match found with
                | .none => []
                | .some x => go done ((e, x.2.2.2) :: more)
            | _ => []
        --lnodes gnodes bvars sorts consts lits
        | .lnode l _ .none => -- tag .none means it does't originate from backward propagation
            let builds := CExprTrie.build link
            go ((l, builds) :: done) more
        | .lnode l _ t =>
            match link with
            | .br lnodes _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
                let found := List.find? (fun x => x.2.1 == l && x.2.2 == t) lnodes
                match found with
                | .none => []
                | .some x => go (done_prune x.1 done) more
            | _ => []
        | .gnode l _ =>
            match link with
            | .br _ gnodes _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
                let found := List.find? (fun x => x.2 == l) gnodes
                match found with
                | .none => []
                | .some x => go (done_prune x.1 done) more
            | _ => []
        | .bvar l =>
            match link with
            | .br _ _ bvars _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
                let found := List.find? (fun x => x.2 == l) bvars
                match found with
                | .none => []
                | .some x => go (done_prune x.1 done) more
            | _ => []
        | .sort l  =>
            match link with
            | .br _ _ _ sorts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
                let found := List.find? (fun x => x.2 == l) sorts
                match found with
                | .none => []
                | .some x => go (done_prune x.1 done) more
            | _ => []
        | .const n l =>
            match link with
            | .br _ _ _ _ consts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
                let found := List.find? (fun x => x.2.1 == n && x.2.2 == l) consts
                match found with
                | .none => []
                | .some x => go (done_prune x.1 done) more
            | _ => []
        | .lit l =>
            match link with
            | .br _ _ _ _ _ lits _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
                let found := List.find? (fun x => x.2 == l) lits
                match found with
                | .none => []
                | .some x => go (done_prune x.1 done) more
            | _ => []
  go [] [(ce,T)]


def unify_reconstruct (candidates : List (Nat × List (CExpr × List Nat))) : List (Nat × List (Nat × CExpr)) :=
    let rec go (node_idx : Nat) (sofar : List (Nat × List (Nat × CExpr))) : List (CExpr × List Nat) → List (Nat × List (Nat × CExpr))
        | [] => sofar
        | (assign, ind) :: rest =>
                let step := ind.foldl (fun out i => List.findModifyAdd (fun x => x.1 == i) (fun (idx, matchInfo) => (idx, (node_idx,assign) :: matchInfo)) (i, [(node_idx,assign)]) out) sofar
                go node_idx step rest
    candidates.foldl (fun out (node_idx, assign_data) => go node_idx out assign_data) []



partial def unify_occurences (ce : CExpr) (T : CExprTrie) : List ((Nat × List (Nat × CExpr)) × List oDirs) :=
    let rec go (done : List ((Nat × List (Nat × CExpr)) × List oDirs)) : List (List oDirs × CExprTrie) → List ((Nat × List (Nat × CExpr)) × List oDirs)
        | [] => done
        | nx :: more =>
            let unis := CExprTrie.unify_reconstruct (CExprTrie.unify_candidates nx.2 ce)
            match unis with
            | [] =>
                match nx.2 with
                | .dead => go done more
                | .br _ _ _ _ _ _ apf apa api laf laa lai alf ala ali lef lea lez lei projs =>
                    let todo := (if api.isEmpty then [] else [(.apf :: nx.1, apf),(.apa :: nx.1, apa)])
                                ++ (if lai.isEmpty then [] else [(.laf :: nx.1, laf),(.laa :: nx.1, laa)])
                                ++ (if ali.isEmpty then [] else [(.alf :: nx.1, alf),(.ala :: nx.1, ala)])
                                ++ (if lei.isEmpty then [] else [(.lef :: nx.1, lef),(.lea :: nx.1, lea),(.lez :: nx.1, lez)])
                                ++ projs.map (fun x => ((.pro x.2.1 x.2.2.1)  :: nx.1, x.2.2.2))
                    go done (todo ++ more)
            | ind =>
                let new := ((ind.map (fun x => (x,nx.1))) ++ done)
                match nx.2 with
                | .dead => go new more
                | .br _ _ _ _ _ _ apf apa api laf laa lai alf ala ali lef lea lez lei projs =>
                    let todo := (if api.isEmpty then [] else [(.apf :: nx.1, apf),(.apa :: nx.1, apa)])
                                ++ (if lai.isEmpty then [] else [(.laf :: nx.1, laf),(.laa :: nx.1, laa)])
                                ++ (if ali.isEmpty then [] else [(.alf :: nx.1, alf),(.ala :: nx.1, ala)])
                                ++ (if lei.isEmpty then [] else [(.lef :: nx.1, lef),(.lea :: nx.1, lea),(.lez :: nx.1, lez)])
                                ++ projs.map (fun x => ((.pro x.2.1 x.2.2.1)  :: nx.1, x.2.2.2))
                    go new (todo ++ more)
    go [] [([],T)]

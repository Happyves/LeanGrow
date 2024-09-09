
import LeanGrow.Caches.QueryTreeSmoothClusters_wL_col2
import LeanGrow.Caches.QueryTreeSmoothClustersGoal_wL_col2
import LeanGrow.Transitions_QueTreClus

open Lean Data


#check LinkTreeTop
#check g_LinkTreeTop



partial def Trie.merge_with [BEq α] [Inhabited α] (l r : Trie α) (f : α → α → α) : Trie α  :=
  let mini_merge (x y : Option α) : Option α :=
    (match x, y with
     | .some X , .some Y => .some (f X Y)
     | .some X , .none => .some X
     | .none,  .some Y => .some Y
     | _, _ => .none)
  match l with
  | .leaf x =>
      match r with
      | .leaf y => .leaf (mini_merge x y)
      | .node1 y ay cy => .node1 (mini_merge x y) ay cy
      | .node y ay cy => .node (mini_merge x y) ay cy
  | .node1 x ax cx =>
      match r with
      | .leaf y => .node1 (mini_merge x y) ax cx
      | .node1 y ay cy =>
          match Ord.compare ax ay with
          | .lt => .node (mini_merge x y) ⟨#[ax, ay]⟩  #[cx, cy]
          | .eq => .node1 (mini_merge x y) ax  (Trie.merge cx cy)
          | .gt => .node (mini_merge x y) ⟨#[ay, ax]⟩  #[cy, cx]
      | .node y ay cy =>
          match ay.has? ax with
          | .none =>
                let (cs',n) := Array.orderedInsertWithIndex (· ≤ ·) ax ay.data
                .node (mini_merge x y) (⟨cs'⟩) (cy.insertAt! n cx)
          | .some i =>
                .node (mini_merge x y) ay (cy.modify i (Trie.merge cx))
  | .node x ax cx =>
      match r with
      | .leaf y => .node (mini_merge x y) ax cx
      | .node1 y ay cy =>
          match ax.has? ay with
          | .none =>
                let (cs',n) := Array.orderedInsertWithIndex (· ≤ ·) ay ax.data
                .node (mini_merge x y) (⟨cs'⟩) (cx.insertAt! n cy)
          | .some i =>
                .node (mini_merge x y) ax (cx.modify i (Trie.merge cy))
      | .node y ay cy =>
          let (uni_b, uni_t) := ByteArray.merge_extra ax ay cx cy
          .node (mini_merge x y) uni_b uni_t


#check Trie.upsert

#check Expr.getAppFn

def Expr.getFunBody : Expr → Expr
| .lam _ _ b _ => Expr.getFunBody b
| x => x

open Meta

partial def count_props : Expr → MetaM Nat
| .lam n t b _ => do
    let fvarId ← mkFreshFVarId
    let ctx ← read
    let lctx := ctx.lctx.mkLocalDecl fvarId n t
    let fvar := mkFVar fvarId
    withReader (fun ctx => { ctx with lctx := lctx }) do
      (if
        let .some c := (← isClass? t)
        then
        withNewLocalInstance c fvar <| count_props (b.instantiate1 fvar)
        else
        count_props (b.instantiate1 fvar)
          )
| .mdata _ e | .proj _ _ e => count_props e
| .app l r => do
      let cl ← count_props l
      let cr ← count_props r
      return cl+cr
| e => do --const and fvar
      if (← inferType e).isProp then return 1 else return 0



partial def sample_goal_and_unrelated_hyps (proof : Expr) : MetaM (Option (Expr × List Expr)) :=
  match proof with
  | .lam n t b i => do
      let fvarId ← mkFreshFVarId
      let ctx ← read
      let lctx := ctx.lctx.mkLocalDecl fvarId n t
      let fvar := mkFVar fvarId
      withReader (fun ctx => { ctx with lctx := lctx }) do
        (if
          let .some c := (← isClass? t)
         then
          withNewLocalInstance c fvar <| sample_goal_and_unrelated_hyps (b.instantiate1 fvar)
         else
          sample_goal_and_unrelated_hyps (b.instantiate1 fvar)
           )
  | .mdata _ e | .proj _ _ e => sample_goal_and_unrelated_hyps e
  | _ => do
      let args := proof.getAppArgs
      let h := proof.getAppFn
      if (← inferType h).isProp
      then
        match h with
        | .const n _ =>


#check IO.rand
#check Meta.transform

def sample_data (proof : Expr) : MetaM (Trie (List ((List Nat) × (List Nat)))) := do
  sorry

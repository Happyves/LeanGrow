
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

partial def count_thms : Expr → MetaM Nat
| .lam n t b _ => do
    let fvarId ← mkFreshFVarId
    let ctx ← read
    let lctx := ctx.lctx.mkLocalDecl fvarId n t
    let fvar := mkFVar fvarId
    withReader (fun ctx => { ctx with lctx := lctx }) do
      (if
        let .some c := (← isClass? t)
        then
        withNewLocalInstance c fvar <| count_thms (b.instantiate1 fvar)
        else
        count_thms (b.instantiate1 fvar)
          )
| .mdata _ e | .proj _ _ e => count_thms e
| .app l r => do
      let cl ← count_thms l
      let cr ← count_thms r
      return cl+cr
| .const c l => do --const and fvar
      if (← inferType (.const c l)).isProp then return 1 else return 0
| _ => return 0



partial def sample_goal_and_hyps (proof : Expr) : MetaM (Option (Name × (Expr × Context) × List (Expr × Context))) :=
  match proof with
  | .lam n t b _ => do
      let fvarId ← mkFreshFVarId
      let ctx ← read
      let lctx := ctx.lctx.mkLocalDecl fvarId n t
      let fvar := mkFVar fvarId
      withReader (fun ctx => { ctx with lctx := lctx }) do
        (if
          let .some c := (← isClass? t)
         then
          withNewLocalInstance c fvar ((Option.map (fun (s,g,h) => (s,g, (t,ctx) :: h))) <$> (sample_goal_and_hyps (b.instantiate1 fvar)))
         else
          ((Option.map (fun (s,g,h) => (s,g, (t,ctx) :: h))) <$> (sample_goal_and_hyps (b.instantiate1 fvar)))
           )
  | .mdata _ e | .proj _ _ e => sample_goal_and_hyps e
  | e => do
      let args := e.getAppArgs
      let h := e.getAppFn
      match h with
      | .const n _ =>
            if (← inferType h).isProp
            then
              let appears ← args.mapM count_thms
              let total := appears.foldl (fun s x => s+x) 0
              if total = 0
              then
                return .some (n,((← inferType e), (← read)),[])
              else
                let r ← IO.rand 0 (total + 1)
                if r = total + 1
                then
                  return .some (n,(← inferType e, (← read)),[])
                else
                  let mut sum := 0
                  let mut idx := 0
                  for w in appears do
                    if r > sum then sum := sum + w ; idx := idx + 1
                  let .some (N, goal, _) ← sample_goal_and_hyps (args.get! idx) | return .none
                  let mut hyps := []
                  let mut idx2 := 0
                  for a in args do
                    if idx2 ≠ idx
                    then
                      let .some (_,_, hyp) ← sample_goal_and_hyps a | pure ()
                      hyps := hyp :: hyps
                      idx2 := idx2 + 1
                    else
                      idx2 := idx2 + 1
                  return .some (N, goal, hyps.join)
            else
              return .none
      | _ => return .some (`Dummy ,(.const `DUMMY [], {}) ,[(← inferType e, (← read))])


elab "testing_sample_goal_and_hyps" : command => do
  let thm_name := `Nat.add_comm
  let info := ((← getEnv).constants.find! thm_name)
  match info with
  | .thmInfo v =>
      let .some (N,T,H) ← Elab.Command.liftTermElabM (sample_goal_and_hyps v.value) | throwError "aaahh 1"
      --let TT := ← withLCtx T.2.lctx T.2.localInstances (inferType T.1)
      let X ← Elab.Command.liftTermElabM  ((H.map Prod.fst).mapM (ppExpr) : MetaM (List Format))
      IO.println s!"Sampleted: {N}\nGoal: {← Elab.Command.liftTermElabM  (ppExpr T.1)}\nAssumptions: {X}"
  | _ => throwError "aaahh 2"

testing_sample_goal_and_hyps

#exit

#check IO.rand
#check Meta.transform

def sample_data (proof : Expr) : MetaM (Trie (List ((List Nat) × (List Nat)))) := do
  sorry

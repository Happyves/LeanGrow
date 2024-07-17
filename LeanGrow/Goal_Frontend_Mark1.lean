
import LeanGrow.CExpr
import LeanGrow.NameListCompare
import LeanGrow.Caches.mark1goalClusters

open Lean

def match_goals (lib : CExpr) (g : Expr) (sofar : RBMap Nat Expr (instOrdNat.compare)) : Option (RBMap Nat Expr (instOrdNat.compare)) :=
  --dbg_trace s!"Matching internals:\n{lib}\n{g}"
  dbg_trace s!"Matching internals:\n{sofar.toList}"
  match lib, g with
  | x, .app (.app (.const `optParam _) e) _ => match_goals x e sofar
  | x, .app (.app (.const `outParam _) e) _ => match_goals x e sofar
  | .node i _ , e => --if sofar.contains i then dbg_trace s!"hmmm"; .none else .some (sofar.insert i e)
        match sofar.find? i with
        | .some x => if x == e then .some sofar else .none
        | .none => .some (sofar.insert i e)
  | .bvar i , .bvar j =>  if i == j then .some sofar else dbg_trace s!"bvar miss {i} {j}" ; .none
  | .sort _, .sort _ => .some sofar
  | .const n _, .const n' _ => if (n == n') then .some sofar else dbg_trace s!"cst miss {n} {n'}"; .none
  | .app f a, .app f' a' =>
        let of := match_goals f f' sofar
        match of with
        | .some sofar' =>
              let oa := match_goals a a' sofar';
              (RBMap.mergeBy (fun _ v1 _ => v1) sofar') <$> oa
        | .none => .none
  | .lam _ t b _, .lam _ t' b' _ =>
        let of := match_goals t t' sofar
        match of with
        | .some sofar' =>
              let oa := match_goals b b' sofar';
              (RBMap.mergeBy (fun _ v1 _ => v1) sofar') <$> oa
        | .none => .none
  | .forallE _ t b _, .forallE _ t' b' _ =>
        let of := match_goals t t' sofar
        match of with
        | .some sofar' =>
              let oa := match_goals b b' sofar';
              (RBMap.mergeBy (fun _ v1 _ => v1) sofar') <$> oa
        | .none => .none
  | .letE _ t v b _, .letE _ t' v' b' _ =>
        let of := match_goals t t' sofar
        match of with
        | .some sofar' =>
              let oa := match_goals b b' sofar'
              match oa with
              | .some sofar'' =>
                  let oc := match_goals v v' sofar'
                  (RBMap.mergeBy (fun _ v1 _ => v1) sofar'') <$> oc
              | .none => .none
        | .none => .none
  | .lit l, .lit l' => if l == l' then .some sofar else dbg_trace s!"lit miss"; .none
  | .proj t i b, .proj t' i' b' => if (t == t') && (i == i') then match_goals b b' sofar else dbg_trace s!"proj miss names {t} {t'} indices {i} {i'}"; .none
  | _ , _ => dbg_trace s!"total miss"; .none



def List.map₂ (l : List α) (L : List β) (f : α → β → γ) : List γ :=
  match l, L with
  | xl :: rl, xL :: rL => (f xl xL) :: (List.map₂ rl rL f)
  | _, _ => []

--#exit


open Lean Elab Meta Command Tactic TryThis

def helper_assign_1 : Expr → List (Expr )
| .forallE _ t b _ => (t) :: (helper_assign_1 b)
| _ => []

def helper_assign_2 (match_data : RBMap Nat Expr (instOrdNat.compare)) (thm_type : Expr) (thm_name : Name) (thm_lp : List Name) : MetaM Expr := do
  let assumptions := (helper_assign_1 thm_type)
  dbg_trace s!"Assumptions : {assumptions}"
  let (res, _) ← assumptions.foldlM (
    fun (e,c) (h) =>
      match match_data.find? c with
      | .some a => do return (.app e a, c-1)
      | _ => do dbg_trace s!"Adding mvar" ; let new_mv ← mkFreshExprMVar (.some (h)) ; return (.app e new_mv, c-1)
    ) ((Expr.const thm_name (thm_lp.map Level.param)), (assumptions.length-1))
  dbg_trace s!"Output : {res}"
  return res



-- TODO: store relevant parts of constant info in gdata
def assign_from_match (match_data : RBMap Nat Expr (instOrdNat.compare)) (thm_name : Name) : MetaM (Option Expr) := do
  let env ← getEnv
  match env.constants.find? thm_name with
  | .none => pure .none
  | .some info =>
      let res ← helper_assign_2 match_data info.type info.name info.levelParams
      return (.some res)


#check ConstantInfo.levelParams

#check Meta.mkFreshExprMVar

#check Lean.Meta.Tactic.TryThis.addExactSuggestion




elab "grow"  : tactic => do
        let ref ← getRef
        Elab.Tactic.withMainContext do
          let g ← getMainTarget
          dbg_trace s!"Target : {g}"
          let names := (Expr.getConstNames g).map Name.toString
          let psn := SortedTrieFormList' names
          dbg_trace s!"Names : {names}"
          for (t, clust) in g_cl_L do
              let inter := Trie.CountCommon psn t
              if inter ≠ 0
              then
                dbg_trace s!"Match!"
                for dat in clust do
                  dbg_trace s!"Testing : {dat.cst_name}"
                  let res := match_goals dat.exp g {}
                  dbg_trace s!"Retrieved {(RBMap.toList <$> res)}"
                  match res with
                  | .none => pure ()
                  | .some dict =>  do
                          dbg_trace s!"Retrieved assignement {← dict.toList.mapM (fun (n,e) => do let pe ← ppExpr e ; return (n, pe ))}"
                          let r ← assign_from_match dict dat.cst_name
                          match r with
                          | .some res =>
                              dbg_trace s!"Retrieved expression {← ppExpr res}"
                              addExactSuggestion ref res
                          | .none => pure ()


-- elab "growin"  : tactic => do
--         let ref ← getRef
--         Elab.Tactic.withMainContext do
--           let ltx ←  getLCtx
--           let (ltx_dag, ltx_dict, ltx_dict') := orderHyps_fromLocalCtx ltx
--           let sink_names := (((DAG.find_sinks ltx_dag true).map DAGnode.data).map CExpr.getConstNames).join.map Name.toString
--           let psn := SortedTrieFormList' sink_names
--           for (t, clust) in cl_L do
--               let inter := Trie.CountCommon psn t
--               if inter ≠ 0 ∧ ( ((Nat.toFloat inter) / (Nat.toFloat sink_names.length))≥ 0.5)
--               then
--                 dbg_trace "Match!"
--                 for dag in clust do
--                   let embeds := matcher dag.dag (SizeDAG.sinks_fst ltx_dag)
--                   match embeds with
--                   | [] => pure ()
--                   | _ =>  do
--                           let P ← (embeds.mapM (fun e => embed_to_expr e --(hyps.map Prod.snd)
--                             dag.dag.size ltx_dict' dag.cst_name  dag.cst_level_params))
--                           addEmbellishedTermSuggestions ref P.toArray
--                             (depPostInfo := fun e => do return s!"\n{← ppExpr (← inferType e)}")


--#exit

elab "print_cluster_cst_names" : command => do
  for c in g_cl_L do
    IO.println s!"Cluster: {String.intercalate ", " (Trie.print_keys ⟨#[]⟩ c.1)}"
    IO.println "\n"

print_cluster_cst_names


elab "print_cluster_thms" : command => do
  let env ← getEnv
  for c in g_cl_L do
    IO.println s!"Cluster:"
    for thm in c.2 do
      let thmdata := env.constants.find! thm.cst_name
      IO.println s!"{thmdata.name} : {instToStringFormat.toString (← liftTermElabM (ppExpr (thmdata.type)))}"
    IO.println "\n\n\n"



print_cluster_thms

--#exit


set_option linter.unusedTactic false

example {α : Type u} {β : Type v} (f : α → β → β) (b : β) (x : α) (xs : List α) :
  List.foldr f b (xs ++ [x]) = List.foldr f (f x b) xs :=
  by
  grow
  sorry

#check List.foldr_concat

example {α : Type u} {p : α → Bool} {l : List α} {x : α}   : List.takeWhile p (x :: l) = [] :=
  by
  grow
  sorry

#check List.takeWhile_cons_of_neg



#exit

example (l : List ℕ) (a : ℕ) (h : a ∈ l) : True :=
  by
  growin
  trivial

example (l L : List ℕ) (h : 0 < l.length) : True :=
  by
  growin
  trivial

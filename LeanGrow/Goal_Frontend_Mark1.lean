
import LeanGrow.CExpr
import LeanGrow.NameListCompare
import LeanGrow.Caches.mark1goalClusters

open Lean

def match_goals (lib : CExpr) (g : Expr) (sofar : RBMap Nat Expr (instOrdNat.compare)) : Option (RBMap Nat Expr (instOrdNat.compare)) :=
  match lib, g with
  | x, .app (.app (.const `optParam _) e) _ => match_goals x e sofar
  | x, .app (.app (.const `outParam _) e) _ => match_goals x e sofar
  | .node i _ , e =>
        match sofar.find? i with
        | .some x => if x == e then .some sofar else .none
        | .none => .some (sofar.insert i e)
  | .bvar i , .bvar j =>  if i == j then .some sofar else  .none
  | .sort _, .sort _ => .some sofar
  | .const n _, .const n' _ => if (n == n') then .some sofar else .none
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
  | .lit l, .lit l' => if l == l' then .some sofar else .none
  | .proj t i b, .proj t' i' b' => if (t == t') && (i == i') then match_goals b b' sofar else .none
  | _ , _ =>  .none



def List.map₂ (l : List α) (L : List β) (f : α → β → γ) : List γ :=
  match l, L with
  | xl :: rl, xL :: rL => (f xl xL) :: (List.map₂ rl rL f)
  | _, _ => []

--#exit


open Lean Elab Meta Command Tactic TryThis

def helper_assign_1 : Expr → List (Expr )
| .forallE _ t b _ => (t) :: (helper_assign_1 b)
| _ => []


def helper_assign_0 (match_data : RBMap Nat Expr (instOrdNat.compare)) (depth : Nat) (shift : Nat) : Expr → Expr
| .bvar i =>
    if i ≥ depth
    then match match_data.find? (i - depth + shift) with
         | .some e => e
         | .none => .const `FAILED []
    else .bvar i
| .app l r => .app (helper_assign_0 match_data depth shift l) (helper_assign_0 match_data depth shift r)
| .lam n l r B => .lam n (helper_assign_0 match_data depth shift l) (helper_assign_0 match_data (depth+1) shift r) B -- shouldn't occur ?
| .forallE n l r B => .forallE n (helper_assign_0 match_data depth shift l) (helper_assign_0 match_data (depth+1) shift r) B -- shouldn't occur ?
| .mdata _ e => helper_assign_0 match_data depth shift e
| .proj n i e => .proj n i (helper_assign_0 match_data depth shift e)
| x => x

def helper_assign_2 (match_data : RBMap Nat Expr (instOrdNat.compare)) (thm_type : Expr) (thm_name : Name) (thm_lp : List Name) : MetaM Expr := do
  let assumptions := (helper_assign_1 thm_type)
  --dbg_trace s!"MD : {match_data.toList}"
  let (res, _) ← assumptions.foldlM (
    fun (e,c) (h) =>
      match match_data.find? c with
      | .some a => do return (.app e a, c-1)
      | _ => do let h' := helper_assign_0 match_data 0 (c+1) h ; let new_mv ← mkFreshExprMVar (.some (h')) ; Lean.MVarId.setType new_mv.mvarId! h'; return (.app e new_mv, c-1)
    ) ((Expr.const thm_name (thm_lp.map Level.param)), (assumptions.length-1))
  --dbg_trace s!"Output : {res}"
  return res

--#exit

-- TODO: store relevant parts of constant info in gdata
def assign_from_match (match_data : RBMap Nat Expr (instOrdNat.compare)) (thm_name : Name): MetaM (Option Expr) := do
  let env ← getEnv
  match env.constants.find? thm_name with
  | .none => pure .none
  | .some info =>
      let res ← helper_assign_2 match_data info.type info.name info.levelParams
      return (.some res)


def Lean.Meta.Tactic.TryThis.delabToEmbellishedRefinableSuggestion (depPreInfo : Expr → MetaM (Option String)) (depPostInfo : Expr → MetaM (Option String)) (e : Expr)  : MetaM Suggestion :=
  return { suggestion := ← delabToRefinableSyntax e, messageData? := e, preInfo? := ← depPreInfo e, postInfo? := ← depPostInfo e }


def Lean.Meta.Tactic.TryThis.addEmbellishedTermSuggestions (ref : Syntax) (es : Array Expr)
    (origSpan? : Option Syntax := none) (header : String := "Try these:")
    (depPreInfo : Expr → MetaM (Option String) := fun _ => do return .none) (depPostInfo : Expr → MetaM (Option String) := fun _ => do return .none)
    (codeActionPrefix? : Option String := none) : MetaM Unit := do
  addSuggestions ref (← es.mapM (delabToEmbellishedRefinableSuggestion depPreInfo depPostInfo))
    (origSpan? := origSpan?) (header := header) (codeActionPrefix? := codeActionPrefix?)



def Lean.LocalDecl.setFVarId : LocalDecl → FVarId → LocalDecl
| .cdecl (index : Nat) (_ : FVarId) (userName : Name) (type : Expr) (bi : BinderInfo) (kind : LocalDeclKind), new => .cdecl (index ) (new) (userName ) (type ) (bi ) (kind )
| .ldecl (index : Nat) (_ : FVarId) (userName : Name) (type : Expr) (value : Expr) (nonDep : Bool) (kind : LocalDeclKind), new => .ldecl (index ) (new ) (userName ) (type ) (value ) (nonDep ) (kind )


def replace_fvars_by_const_with_user_name_cause_ppExpr_sucks (e : Expr) : MetaM Expr := do
  let ltx ← getLCtx
  match e with
  | .fvar id =>
        match ltx.find? id with
        | .some d => do return (.const d.userName [])
        | .none => throwError "oh-oh"
  | .app l r => do return .app (← replace_fvars_by_const_with_user_name_cause_ppExpr_sucks l) ( ← replace_fvars_by_const_with_user_name_cause_ppExpr_sucks r)
  | .lam n l r B => do return .lam n (← replace_fvars_by_const_with_user_name_cause_ppExpr_sucks l) (← replace_fvars_by_const_with_user_name_cause_ppExpr_sucks r) B
  | .forallE n l r B => do return .forallE n (← replace_fvars_by_const_with_user_name_cause_ppExpr_sucks l) (← replace_fvars_by_const_with_user_name_cause_ppExpr_sucks r) B
  | .letE n l t r B => do return .letE n (← replace_fvars_by_const_with_user_name_cause_ppExpr_sucks l) (← replace_fvars_by_const_with_user_name_cause_ppExpr_sucks t)  (← replace_fvars_by_const_with_user_name_cause_ppExpr_sucks r) B
  | .mdata _ e => (replace_fvars_by_const_with_user_name_cause_ppExpr_sucks e)
  | .proj n i e => do return .proj n i (← replace_fvars_by_const_with_user_name_cause_ppExpr_sucks e)
  | x => do return x

--#exit

def print_mvar_types_for_post : Expr → MetaM (Option String) :=
  fun e => do
    let mvs ← getMVars e
    let mut out := ""
    for m in mvs do
      let t ←  m.getType
      out := s!"\n▸ {← ppExpr ( t)}" ++ out
    return .some out

#check LocalContext.getFVarIds
#check LocalContext.modifyLocalDecl

#check forallMetaTelescopeReducing
--#exit

elab "grow"  : tactic => do
        let ref ← getRef
        Elab.Tactic.withMainContext do
          let g ← getMainTarget
          --dbg_trace s!"Target : {g}"
          let names := (Expr.getConstNames g).map Name.toString
          let psn := SortedTrieFormList' names
          --dbg_trace s!"Names : {names}"
          for (t, clust) in g_cl_L do
              let inter := Trie.CountCommon psn t
              if inter ≠ 0 --∧ ( ((Nat.toFloat inter) / (Nat.toFloat names.length))≥ 0.5)
              then
                --dbg_trace s!"Match!"
                for dat in clust do
                  --dbg_trace s!"Testing : {dat.cst_name}"
                  let res := match_goals dat.exp g {}
                  dbg_trace s!"Retrieved {(RBMap.toList <$> res)}"
                  match res with
                  | .none => pure ()
                  | .some dict =>  do
                          --dbg_trace s!"Retrieved assignement {← dict.toList.mapM (fun (n,e) => do let pe ← ppExpr e ; return (n, pe ))}"
                          let r ← assign_from_match dict dat.cst_name
                          match r with
                          | .some res =>
                              --dbg_trace s!"Retrieved expression {← ppExpr res}"
                              --addExactSuggestion ref res -- didn't print the expected types of mvars...
                              addEmbellishedTermSuggestions ref #[res] (depPostInfo := print_mvar_types_for_post)
                          | .none => pure ()



--#exit

elab "print_cluster_cst_names" : command => do
  for c in g_cl_L do
    IO.println s!"Cluster: {String.intercalate ", " (Trie.print_keys ⟨#[]⟩ c.1)}"
    IO.println "\n"

print_cluster_cst_names


#eval g_cl_L.length

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

example {α : Type _} {p : α → Bool} {l : List α}  {x : α} : List.takeWhile p (x :: l) = [] :=
  by
  grow
  sorry

#check List.takeWhile_cons_of_neg
#check List.append_left_cancel


example (l₁ : List α) {l₂ : List α} (_ : l₁ ≠ []) : List.head? (l₁ ++ l₂) = List.head? l₁ :=
  by
  grow
  sorry

#check List.head?_append_of_ne_nil

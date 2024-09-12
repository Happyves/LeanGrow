
import LeanGrow.EmpiricalScore
import LeanGrow.ProcessLocalCtx


open Lean Data Meta


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


structure empiricalScores where
  hyp_cl : RBNode Nat (fun _ => Nat)
  g_cl : RBNode Nat (fun _ => Nat)


#check Expr.getConstNames
#check get_Ltx_names

def get_clusters_from_sample (s : sampleType) : (List Nat) × (List Nat) :=
  let gn := SortedTrieFormList' ((Expr.getConstNames s.goal_type).map Name.toString)
  let hn := SortedTrieFormList' ((get_Ltx_names s.ctx.lctx).map Name.toString)
  let gcs := (QueryTree.query gn g_LinkTreeTop).map Prod.fst
  let hcs := (QueryTree.query hn LinkTreeTop).map Prod.fst
  (hcs, gcs)

#check Trie.insert
#check RBNode.upsert

def update_score_trie (T : Trie empiricalScores) (s : sampleType) : Trie empiricalScores := Id.run do
  let (hcs, gcs) := get_clusters_from_sample s
  let ns := s.thm_name.toString
  let current :=
    match Trie.find? T ns with
    | .some x => x
    | .none => ⟨{},{}⟩
  let mut nhs := current.hyp_cl
  for h in hcs do
    nhs := RBNode.upsert instOrdNat.compare Nat.succ 0 nhs h
  let mut ngs := current.hyp_cl
  for g in gcs do
    ngs := RBNode.upsert instOrdNat.compare Nat.succ 0 ngs g
  return Trie.insert T ns ⟨nhs,ngs⟩ -- overrides, according to docs

def update_score_trie_self (T : Trie empiricalScores) (s : sampleType) (inc : Nat) : Trie empiricalScores := Id.run do
  let (hcs, gcs) := get_clusters_from_sample s
  let ns := s.thm_name.toString
  let current :=
    match Trie.find? T ns with
    | .some x => x
    | .none => ⟨{},{}⟩
  let mut nhs := current.hyp_cl
  for h in hcs do
    nhs := RBNode.upsert instOrdNat.compare (· + inc) (inc) nhs h
  let mut ngs := current.hyp_cl
  for g in gcs do
    ngs := RBNode.upsert instOrdNat.compare Nat.succ 0 ngs g
  return Trie.insert T ns ⟨nhs,ngs⟩ -- overrides, according to docs


instance : ToString empiricalScores where
  toString := fun ⟨h,g⟩ => s!"empiricalScores.mk ({RBNode.toString (fun n => s!"{n}") (fun n => s!"{n}") h}) ({RBNode.toString (fun n => s!"{n}") (fun n => s!"{n}") g})"


partial def Trie.enumVals (count : Nat): Trie α → (Nat × (Trie Nat) × List (Nat × α))
| .leaf x =>
      match x with
      | .some y => (count+1, .leaf (.some count), [(count, y)])
      | .none => (count, .leaf .none, [])
| .node1 x a t =>
      let (nc, nt, es) := Trie.enumVals count t
      match x with
      | .some y => (nc+1, .node1 (.some nc) a nt, (nc, y) :: es)
      | .none => (nc, .node1 .none a nt, es)
| .node x as ts => Id.run do
      let mut cc := count
      let mut nts := Array.mkArray ts.size Trie.empty
      let mut aes := []
      let mut idx := 0
      for t in ts do
        let (nc, nt, es) := Trie.enumVals cc t
        cc := nc
        nts :=  Array.set! nts idx nt
        idx := idx + 1
        aes := es :: aes
      match x with
      | .some y => (cc+1, .node (.some cc) as nts, (cc, y) :: aes.join)
      | .none => (cc, .node .none as nts, aes.join)

partial def print_trie_BS_local : Trie Nat → String
  | .leaf x => --dbg_trace "comp trie"
      s!"Lean.Data.Trie.leaf rbt_empSc_{x}"
  | .node1 o i t => --dbg_trace "comp trie"
      s!"Lean.Data.Trie.node1 rbt_empSc_{o} {i} ({print_trie t})"
  | .node o i t => --dbg_trace "comp trie"
      s!"Lean.Data.Trie.node rbt_empSc_{o} {print_bytearray i} #[{String.intercalate "," (t.data.map print_trie)}]"



elab "cachEmpiricalScores" n:name : command =>
  match (Lean.Syntax.isNameLit? n.raw) with
  | none => throwError s!"Error : please enter the correct name of a module to search theorems in."
  | some N => do
        let env ← getEnv
        let modules := env.header.moduleNames.map (N.isPrefixOf ·)
        let res ← env.constants.map₁.foldM (fun hmm decName decInfo => do
                    let na ← Loogle.isBlackListed decName
                    if modules[env.const2ModIdx[decName].get! (α := Nat)]! && (! na)
                    then match decInfo with
                          | .thmInfo v => do
                                let (sS, os) ← Elab.Command.liftTermElabM (sample_harder v v.name 10)
                                let cos := samples_clean os
                                let mut OT := hmm
                                OT := update_score_trie_self OT sS 100
                                for sam in cos do
                                  OT := update_score_trie OT sam
                                return OT
                          | _ => return hmm
                      else return hmm) (Trie.empty)
        let (_, Top, rbts) := Trie.enumVals 0 res
        let p_rbts := rbts.map (fun (n,T) => s!"def rbt_empSc_{n}_h : RBNode Nat (fun _ => Nat) := {RBNode.toString (fun n => s!"{n}") (fun n => s!"{n}") T.hyp_cl}\ndef rbt_empSc_{n}_g : RBNode Nat (fun _ => Nat) := {RBNode.toString (fun n => s!"{n}") (fun n => s!"{n}") T.g_cl}\ndef rbt_empSc_{n} : empiricalScores := ⟨rbt_empSc_{n}_h ,rbt_empSc_{n}_g⟩")
        let source := s!"import LeanGrow.NameListCompare\nopen Lean Data\n{String.intercalate "\n" p_rbts}\ndef empirical_score_data : Trie empiricalScores := {print_trie_BS_local Top}"
        IO.FS.writeFile ⟨"/./home/yves/Desktop/CodeWorkspace/Lean4_General/LeanGrow/LeanGrow/Caches/EmpScoreSmol.lean"⟩ (source)
        return ()

--cachEmpiricalScores `Mathlib.Data.List.Basic
-- 1 min for Mathlib.Data.List.Basic

#check 1
-- Trie still too fat ; TODO tomorow : BS Tries, visualisation of cluster weight for given thms, front-end for this score
-- Note do visual stuff in new file as this will be imported by cache, hence shouldn't be touched so as to trigger recompilation

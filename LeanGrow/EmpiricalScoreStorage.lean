
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
    nhs := RBNode.upsert instOrdNat.compare Nat.succ 1 nhs h
  let mut ngs := current.hyp_cl
  for g in gcs do
    ngs := RBNode.upsert instOrdNat.compare Nat.succ 1 ngs g
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

def empiricalScores.toString : empiricalScores → String :=
  fun ⟨h,g⟩ => s!"empiricalScores.mk ({RBNode.toString (fun n => s!"{n}") (fun n => s!"{n}") h}) ({RBNode.toString (fun n => s!"{n}") (fun n => s!"{n}") g})"

instance : ToString empiricalScores where
  toString := empiricalScores.toString


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
-- Note : do again and rebuild with lake, i had 0 instead of 1 for fst appearances in rbt ..

#check 1
-- Trie still too fat ; TODO tomorow : BS Tries, visualisation of cluster weight for given thms, front-end for this score
-- Note do visual stuff in new file as this will be imported by cache, hence shouldn't be touched so as to trigger recompilation

#check QueryTree.stratify


partial def Trie.stratify (depth count idx : Nat) : Trie α → (Nat × List (Nat × Trie (preBS α)) × Trie (preBS α))
| .leaf  a => (idx, [], .leaf (preBS.ofVal <$> a))
| .node1 x a t =>
      if count = 0
      then
        let (nidx, tsf, tt) := Trie.stratify depth depth idx (.node1 x a t)
        (nidx+1, (nidx, tt) :: tsf, (.leaf (.some (.ofPoint nidx))))
      else
        let (nidx, tsf, tt) := Trie.stratify depth (count-1) idx t
        (nidx, tsf, .node1 (preBS.ofVal <$> x) a tt)
| .node x as ts =>
      if count = 0
      then
        let (nidx, tsf, tt) := Trie.stratify depth depth idx (.node x as ts)
        (nidx+1, (nidx, tt) :: tsf, (.leaf (.some (.ofPoint nidx))))
      else Id.run do
              let mut i := idx
              let mut nts := Array.mkArray ts.size {}
              let mut ts_all := []
              for I in (List.range ts.size) do
                let (idx_c, qts, pqt) := Trie.stratify depth (count-1) i (ts.get! I)
                nts := nts.set! I pqt
                i := idx_c
                ts_all := qts ++ ts_all
              return (i, ts_all, .node ((preBS.ofVal <$> x)) as nts)



-- correct version in visualize file
partial def Trie.destratify : Trie (tBS α) → Trie α
| .leaf x =>
      match x with
      | .some (.ofPoint p) => Trie.destratify p
      | .some (.ofVal x) => .leaf (.some x)
      | _ => .leaf .none
| .node1 x a t =>
      match x with
      | .some (.ofVal x) => .node1 (.some x) a (Trie.destratify t)
      | _ => .leaf .none
| .node x as ts =>
      match x with
      | .some (.ofVal x) => .node (.some x) as (ts.map Trie.destratify)
      | _ => .leaf .none

def preBS.toString_coret {α : Type _} (string_alpha : α → String) (string_pointer : Nat → String) : preBS α → String
| .ofVal (a : α) => s!"(tBS.ofVal ({string_alpha a}))"
| .ofPoint (p : Nat) => s!"(tBS.ofPoint ({string_pointer p}))"

def preBS.toString_trie {α : Type _} (string_alpha : α → String) :=
  preBS.toString_coret string_alpha (fun n => s!"emT_{n}")

partial def Trie.toString (string_alpha : α → String) : Trie α → String
| .leaf x => s!"Trie.leaf ({string_alpha <$> x})"
| .node1 x a t => s!"Trie.node1 ({string_alpha <$> x}) {a} ({Trie.toString string_alpha t})"
| .node x as ts => s!"Trie.node ({string_alpha <$> x}) {print_bytearray as} #[{String.intercalate "," (ts.map (Trie.toString string_alpha)).toList}]"


def Trie.toString_preBS (string_alpha : α → String) (t : Trie (preBS α)) : String := Trie.toString (preBS.toString_trie string_alpha) t


elab "cachEmpiricalScores_2" n:name : command =>
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
        let (_ , ts, top) := Trie.stratify 3 0 0 Top
        let p_ts := ts.map (fun (n,T) => s!"def emT_{n} : Trie (tBS empiricalScores) := {Trie.toString_preBS (fun n => s!"rbt_empSc_{n}") T}")
        let p_top := Trie.toString_preBS (fun n => s!"rbt_empSc_{n}") top
        let source := s!"import LeanGrow.NameListCompare\nimport LeanGrow.EmpiricalScore\nopen Lean Data\n{String.intercalate "\n" p_rbts}\n{String.intercalate "\n" p_ts.reverse}\ndef empirical_score_data : Trie (tBS empiricalScores) := {p_top}"
        IO.FS.writeFile ⟨"/./home/yves/Desktop/CodeWorkspace/Lean4_General/LeanGrow/LeanGrow/Caches/EmpScoreSmol.lean"⟩ (source)
        return ()

--cachEmpiricalScores_2 `Mathlib.Data.List.Basic
-- 1 min for Mathlib.Data.List.Basic


-- Are also in frontend 3
def RBNode.getTotalWeight (rbt : RBNode ℕ (fun _ ↦ ℕ)) : ℕ :=
  rbt.fold (fun s _ v => s + v) 0

-- modified to aacount for div by 0
def RBNode.normalize (rbt : RBNode ℕ (fun _ ↦ ℕ)) : RBNode ℕ (fun _ ↦ Float) :=
  let totalWeight := Nat.toFloat (RBNode.getTotalWeight rbt)
  RBNode.map (fun _ v => if totalWeight == 0 then 0 else (Nat.toFloat v) / totalWeight) rbt



def preBS.toString_trie' {α : Type _} (string_alpha : α → String) :=
  preBS.toString_coret string_alpha (fun n => s!"aemT_{n}")


def Trie.toString_preBS' (string_alpha : α → String) (t : Trie (preBS α)) : String := Trie.toString (preBS.toString_trie' string_alpha) t

def empiricalScores.normalise : empiricalScores → empiricalScores' :=
  fun ⟨h,g⟩ => ⟨RBNode.normalize h , RBNode.normalize g⟩

partial def Trie.map (f : α → β) : Trie α → Trie β
| .leaf x => .leaf (f <$> x)
| .node1 x a t => .node1 (f <$> x) a (Trie.map f t)
| .node x as ts => .node (f <$> x) as (ts.map (Trie.map f))

partial def Trie.get_total_weight : Trie Nat → Nat
| .leaf x => match x with | .some y => y | _ => 0
| .node1 x _ t =>
      let l := match x with | .some y => y | _ => 0
      l + (Trie.get_total_weight t)
| .node x _ ts =>
      let l := match x with | .some y => y | _ => 0
      l + ((ts.map Trie.get_total_weight).foldl (fun s x => s+x) 0)

instance : Inhabited (RBNode α (fun _ : α => preBS β)) where default := RBNode.leaf
-- otherwise we get error in ↓ ; error message is shit, and people already complained on zulip ...

partial def RBNode.stratify (depth count idx : Nat) : RBNode α (fun _ : α => β) → (Nat × List (Nat × (RBNode α (fun _ : α => preBS β))) × (RBNode α (fun _ : α => preBS β)))
| .leaf => (idx, [], RBNode.leaf)
| .node c l k v r =>
      if count = 0
      then
        let (I,R,T) := RBNode.stratify depth depth idx (RBNode.node c l k v r)
        let L := RBNode.node c RBNode.leaf k (.ofPoint I) RBNode.leaf
        (I+1, (I,T) :: R, L)
      else
        let (lI,lR,lT) := RBNode.stratify depth (count-1) idx l
        let (rI,rR,rT) := RBNode.stratify depth (count-1) lI r
        (rI, lR ++ rR, .node c lT k (.ofVal v) rT)


def RBNode.destratify : RBNode α (fun _ => (rBS α β)) → RBNode α (fun _ => β)
| .leaf => .leaf
| .node c l k v r =>
    match v with
    | .ofVal w => .node c (RBNode.destratify l) k w (RBNode.destratify r)
    | .ofPoint p => RBNode.destratify p

def preBS.toString_corer (string_alpha : β → String) (string_pointer : Nat → String) : preBS β → String
| .ofVal (a : β) => s!"(rBS.ofVal ({string_alpha a}))"
| .ofPoint (p : Nat) => s!"(rBS.ofPoint ({string_pointer p}))"


def preBS.toString_rbt_h {α : Type _} (string_alpha : α → String) :=
  preBS.toString_corer string_alpha (fun n => s!"h_aps_rbt_{n}")

def preBS.toString_rbt_g {α : Type _} (string_alpha : α → String) :=
  preBS.toString_corer string_alpha (fun n => s!"g_aps_rbt_{n}")

#check RBNode.toString

def RBNode.toString_preBS_h (string_alpha : α → String) (string_beta : β → String) (t : RBNode α (fun _ => preBS β)) : String :=
  RBNode.toString string_alpha (preBS.toString_rbt_h string_beta) t

def RBNode.toString_preBS_g (string_alpha : α → String) (string_beta : β → String) (t : RBNode α (fun _ => preBS β)) : String :=
  RBNode.toString string_alpha (preBS.toString_rbt_g string_beta) t


--#exit

elab "cachEmpiricalScores_3" n:name : command =>
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
                                let mut OT := hmm.1
                                let mut AT := hmm.2.1.upsert v.name.toString (fun x => match x with | .some y => Nat.succ y | _ => 1)
                                let mut HCT := hmm.2.2.1
                                let mut GCT := hmm.2.2.2
                                OT := update_score_trie_self OT sS 100
                                let (sh,sg) := get_clusters_from_sample sS
                                HCT := sh.foldl (fun state clu => RBNode.upsert instOrdNat.compare (Nat.succ) 1 state clu) HCT
                                GCT := sg.foldl (fun state clu => RBNode.upsert instOrdNat.compare (Nat.succ) 1 state clu) GCT
                                for sam in cos do
                                  OT := update_score_trie OT sam
                                  AT := AT.upsert sam.thm_name.toString (fun x => match x with | .some y => Nat.succ y | _ => 1)
                                  let (sh,sg) := get_clusters_from_sample sam
                                  HCT := sh.foldl (fun state clu => RBNode.upsert instOrdNat.compare (Nat.succ) 1 state clu) HCT
                                  GCT := sg.foldl (fun state clu => RBNode.upsert instOrdNat.compare (Nat.succ) 1 state clu) GCT
                                return (OT, AT, HCT, GCT)
                          | _ => return hmm
                      else return hmm) (Trie.empty, Trie.empty, RBNode.leaf, RBNode.leaf)
        let (_, Top, rbts) := Trie.enumVals 0 (Trie.map empiricalScores.normalise res.1)
        let p_rbts := rbts.map (fun (n,T) => s!"def rbt_empSc_{n}_h : RBNode Nat (fun _ => Float) := {RBNode.toString (fun n => s!"{n}") (fun n => s!"{n}") T.hyp_cl}\ndef rbt_empSc_{n}_g : RBNode Nat (fun _ => Float) := {RBNode.toString (fun n => s!"{n}") (fun n => s!"{n}") T.g_cl}\ndef rbt_empSc_{n} : empiricalScores' := ⟨rbt_empSc_{n}_h ,rbt_empSc_{n}_g⟩")
        let (_ , ts, top) := Trie.stratify 3 3 0 Top
        let p_ts := ts.map (fun (n,T) => s!"def emT_{n} : Trie (tBS empiricalScores') := {Trie.toString_preBS (fun n => s!"rbt_empSc_{n}") T}")
        let p_top := Trie.toString_preBS (fun n => s!"rbt_empSc_{n}") top
        let W := Trie.get_total_weight res.2.1
        let fW := Nat.toFloat W
        let (_ , ats, atop) := Trie.stratify 3 3 0 (Trie.map (fun x => (Nat.toFloat x) / fW) res.2.1)
        let p_ats := ats.map (fun (n,T) => s!"def aemT_{n} : Trie (tBS Float) := {Trie.toString_preBS' (fun n => s!"{n}") T}")
        let p_atop := Trie.toString_preBS' (fun n => s!"{n}") atop
        let (_,nhcts,nhct) := RBNode.stratify 3 3 0 (RBNode.normalize res.2.2.1)
        let (_, ngcts, ngct) := RBNode.stratify 3 3 0 (RBNode.normalize res.2.2.2)
        let p_nhcts := nhcts.map (fun (n,T) => s!"def h_aps_rbt_{n} : RBNode Nat (fun _ => rBS Nat Float) := {RBNode.toString_preBS_h (fun n => s!"{n}") (fun n => s!"{n}") T}")
        let p_nhct := RBNode.toString_preBS_h (fun n => s!"{n}") (fun n => s!"{n}") nhct
        let p_ngcts := ngcts.map (fun (n,T) => s!"def g_aps_rbt_{n} : RBNode Nat (fun _ => rBS Nat Float) := {RBNode.toString_preBS_g (fun n => s!"{n}") (fun n => s!"{n}") T}")
        let p_ngct := RBNode.toString_preBS_g (fun n => s!"{n}") (fun n => s!"{n}") ngct
        let source := s!"import LeanGrow.NameListCompare\nimport LeanGrow.EmpiricalScore\nopen Lean Data\n{String.intercalate "\n" p_rbts}\n{String.intercalate "\n" p_ts.reverse}\ndef empirical_score_data : Trie (tBS empiricalScores') := {p_top}\n{String.intercalate "\n" p_ats.reverse}\ndef thm_appearances : Trie (tBS Float) := {p_atop}\n{String.intercalate "\n" p_nhcts.reverse}\ndef hyp_clust_appearances : RBNode Nat (fun _ => rBS Nat Float) := {p_nhct}\n{String.intercalate "\n" p_ngcts.reverse}\ndef goal_clust_appearances : RBNode Nat (fun _ => rBS Nat Float) := {p_ngct}"
        IO.FS.writeFile ⟨"/./home/yves/Desktop/CodeWorkspace/Lean4_General/LeanGrow/LeanGrow/Caches/EmpScoreSmol.lean"⟩ (source)
        return ()


--cachEmpiricalScores_3 `Mathlib.Data.List
-- 40 min

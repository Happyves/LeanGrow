
import LeanGrow.Caches.QueryTreeSmoothClusters_wL_col2
import LeanGrow.Caches.QueryTreeSmoothClustersGoal_wL_col2
import LeanGrow.QueryTree_clean
--import LeanGrow.Caches.SmolTransitionGraphs
-- don't import ↑ and ↓ together
import LeanGrow.Caches.LargeTransitionGraphs
-- import LeanGrow.Caches.SmolTransitionGraphClosure_clos_3
import LeanGrow.Caches.LargeTransitionGraphClosure_clos_3


open Lean Data

partial def QueryTree.query (Q : Trie Unit) (T : QueryTree (BS α)) : List α :=
  match T with
  | .root c => (c.map (QueryTree.query Q)).join
  | .node t c => if Trie.CountCommon t Q = Trie.size t then (c.map (QueryTree.query Q)).join else []
  | .leaf (.ofVal a) => [a]
  | .leaf (.ofPoint t) => QueryTree.query Q t

def RBNode.update {β : Type v} (cmp : α → α → Ordering) (f : β → β)  : RBNode α (fun _ => β) → α → RBNode α (fun _ => β)
  | .leaf,             _ => .leaf
  | .node z a ky vy b, x =>
    match cmp x ky with
    | Ordering.lt => .node z (RBNode.update cmp f a x) ky vy b
    | Ordering.gt => .node z a ky vy (RBNode.update cmp f b x)
    | Ordering.eq => .node z a ky (f vy) b


def RBNode.upsert {β : Type v} (cmp : α → α → Ordering) (f : β → β) (val : β) : RBNode α (fun _ => β) → α → RBNode α (fun _ => β) :=
  fun t k =>
    match t.find cmp k with
    | .some _ =>
        RBNode.update cmp f t k
    | .none =>
        RBNode.insert cmp t k val

--#exit

def Clus_Nei_inner (clus : List pdata) : RBNode Nat (fun _ => Nat) :=
  match clus with
  | [] => .leaf
  | d :: ds =>
      let nei := QueryTree.query d.goal_cst_names LinkTreeTop
      Id.run do
        let mut rbn := Clus_Nei_inner ds
        for (n,_) in nei do
          rbn := RBNode.upsert instOrdNat.compare Nat.succ 1 rbn n
        return rbn


def Clus_Nei_outer (clus : List pdata) : RBNode Nat (fun _ => Nat) :=
  match clus with
  | [] => .leaf
  | d :: ds =>
      let nei := QueryTree.query d.goal_cst_names g_LinkTreeTop
      Id.run do
        let mut rbn := Clus_Nei_outer ds
        for (n,_) in nei do
          rbn := RBNode.upsert instOrdNat.compare Nat.succ 1 rbn n
        return rbn


partial def QueryTree.map (f : α → β) : QueryTree α → QueryTree β
| .root c => .root (c.map (QueryTree.map f))
| .node t c => .node t (c.map (QueryTree.map f))
| .leaf x => .leaf (f x)

partial def QueryTree.mapBS (f : α → β) : QueryTree (BS α) → QueryTree (BS β)
| .root c => .root (c.map (QueryTree.mapBS f))
| .node t c => .node t (c.map (QueryTree.mapBS f))
| .leaf (.ofVal x) => .leaf (.ofVal (f x))
| .leaf (.ofPoint p) => .leaf (.ofPoint (QueryTree.mapBS f p))


def RBColor.toString : RBColor → String
| .red => "RBColor.red"
| .black => "RBColor.black"

def RBNode.toString (as : α → String)  (bs : β → String) : RBNode α (fun _ => β) → String
| .leaf => "RBNode.leaf"
| .node  (color : RBColor) (lchild : RBNode α (fun _ => β)) (key : α) (val : β) (rchild : RBNode α (fun _ => β)) =>
      s!"RBNode.node {RBColor.toString color} ({RBNode.toString as bs lchild}) ({as key}) ({bs val}) ({RBNode.toString as bs rchild})"

def BS.toString_trick_more : BS (ℕ × RBNode ℕ (fun _ ↦ ℕ)) → String
| .ofVal (n,a) => s!"(BS.ofVal ({n}, {RBNode.toString (fun x => s!"{x}") (fun x => s!"{x}") a}))"
| .ofPoint (_) => s!"FAIL" -- we expect to run this on the link tree, where there shoudl't be pointer leafs anymore, as we expect it to be small...

def printRBT := RBNode.toString (fun x : Nat => s!"{x}") (fun x : Nat => s!"{x}")

elab "make_smol_transition_graphs" : command => do
  let .some deT := (QueryTree.deStratify true LinkTreeTop).head? | throwError "aaahhh"
  let inner := QueryTree.map (fun (n,l) => (n, Clus_Nei_inner l)) deT
  let outer := QueryTree.map (fun (n,l) => (n, Clus_Nei_outer l)) deT
  let IV := QueryTree.getVals inner
  let OV := QueryTree.getVals inner
  let (_ , sITs, sITtop) := QueryTree.stratify 2 2 0 inner
  let (_ , sOTs, sOTtop) := QueryTree.stratify 2 2 0 outer
  let mut presource := []
  for (i,nei) in IV do
    presource := s!"\ndef i_nei_{i} : RBNode ℕ (fun _ ↦ ℕ) := {printRBT nei}" :: presource
  presource := s!"\ndef i_nei_all : List (Nat × (RBNode ℕ (fun _ ↦ ℕ))) := [{String.intercalate ", " ((IV.map Prod.fst).map (fun n => s!"({n}, i_nei_{n})"))}]" :: presource
  for (i,nei) in OV do
    presource := s!"\ndef o_nei_{i} : RBNode ℕ (fun _ ↦ ℕ) := {printRBT nei}" :: presource
  presource := s!"\ndef o_nei_all : List (Nat × (RBNode ℕ (fun _ ↦ ℕ))) := [{String.intercalate ", " ((IV.map Prod.fst).map (fun n => s!"({n}, o_nei_{n})"))}]" :: presource
  for (i,t) in sITs.reverse do
    presource := s!"\ndef it_{i} : QueryTree (BS (Nat × (RBNode ℕ (fun _ ↦ ℕ)))) := {QueryTree.toString_preBS' t (fun (n,_) => s!"({n}, i_nei_{n})") (fun n => s!"it_{n}")}" :: presource
  presource := s!"\ndef ITreeTop : QueryTree (BS (Nat × (RBNode ℕ (fun _ ↦ ℕ)))) := {QueryTree.toString_preBS' sITtop (fun (n, _) => s!"({n}, i_nei_{n})") (fun n => s!"it_{n}")}" :: presource
  for (i,t) in sOTs.reverse do
    presource := s!"\ndef ot_{i} : QueryTree (BS (Nat × (RBNode ℕ (fun _ ↦ ℕ)))) := {QueryTree.toString_preBS' t (fun (n,_) => s!"({n}, o_nei_{n})") (fun n => s!"ot_{n}")}" :: presource
  presource := s!"\ndef OTreeTop : QueryTree (BS (Nat × (RBNode ℕ (fun _ ↦ ℕ)))) := {QueryTree.toString_preBS' sOTtop (fun (n, _) => s!"({n}, o_nei_{n})") (fun n => s!"ot_{n}")}" :: presource
  let source := s!"\nimport LeanGrow.QueryTree_idea\nopen Lean Data{String.join presource.reverse}"
  IO.FS.writeFile ⟨s!"/./home/yves/Desktop/CodeWorkspace/Lean4_General/LeanGrow/LeanGrow/Caches/SmolTransitionGraphs.lean"⟩ (source)

--make_smol_transition_graphs

--#exit

def Clus_Nei_inner_large (clus : List pdata) : RBNode Nat (fun _ => Nat) :=
  match clus with
  | [] => .leaf
  | d :: ds => Id.run do
      let mut rbn := Clus_Nei_inner_large ds
      for (n,c) in Lsclu_from_qt_all do
        let mut hits := 0
        for pd in c do
          if Trie.CountCommon pd.sink_cst_names d.goal_cst_names ≠ 0 then hits := hits +1
        if hits ≠ 0 then rbn := RBNode.upsert instOrdNat.compare (· + hits) hits rbn n
      return rbn

def Clus_Nei_outer_large (clus : List pdata) : RBNode Nat (fun _ => Nat) :=
  match clus with
  | [] => .leaf
  | d :: ds => Id.run do
      let mut rbn := Clus_Nei_outer_large ds
      for (n,c) in g_Lsclu_from_qt_all do
        let mut hits := 0
        for pd in c do
          if Trie.CountCommon pd.name_list d.goal_cst_names ≠ 0 then hits := hits +1
        if hits ≠ 0 then rbn := RBNode.upsert instOrdNat.compare (· + hits) hits rbn n
      return rbn


#eval Trie.CountCommon (.leaf .none : Trie Unit)  (.leaf .none)


elab "make_large_transition_graphs" : command => do
  let .some deT := (QueryTree.deStratify true LinkTreeTop).head? | throwError "aaahhh"
  let inner := QueryTree.map (fun (n,l) => (n, Clus_Nei_inner_large l)) deT
  let outer := QueryTree.map (fun (n,l) => (n, Clus_Nei_outer_large l)) deT
  let IV := QueryTree.getVals inner
  let OV := QueryTree.getVals inner
  let (_ , sITs, sITtop) := QueryTree.stratify 2 2 0 inner
  let (_ , sOTs, sOTtop) := QueryTree.stratify 2 2 0 outer
  let mut presource := []
  for (i,nei) in IV do
    presource := s!"\ndef i_nei_{i} : RBNode ℕ (fun _ ↦ ℕ) := {printRBT nei}" :: presource
  presource := s!"\ndef i_nei_all : List (Nat × (RBNode ℕ (fun _ ↦ ℕ))) := [{String.intercalate ", " ((IV.map Prod.fst).map (fun n => s!"({n}, i_nei_{n})"))}]" :: presource
  for (i,nei) in OV do
    presource := s!"\ndef o_nei_{i} : RBNode ℕ (fun _ ↦ ℕ) := {printRBT nei}" :: presource
  presource := s!"\ndef o_nei_all : List (Nat × (RBNode ℕ (fun _ ↦ ℕ))) := [{String.intercalate ", " ((IV.map Prod.fst).map (fun n => s!"({n}, o_nei_{n})"))}]" :: presource
  for (i,t) in sITs.reverse do
    presource := s!"\ndef it_{i} : QueryTree (BS (Nat × (RBNode ℕ (fun _ ↦ ℕ)))) := {QueryTree.toString_preBS' t (fun (n,_) => s!"({n}, i_nei_{n})") (fun n => s!"it_{n}")}" :: presource
  presource := s!"\ndef ITreeTop : QueryTree (BS (Nat × (RBNode ℕ (fun _ ↦ ℕ)))) := {QueryTree.toString_preBS' sITtop (fun (n, _) => s!"({n}, i_nei_{n})") (fun n => s!"it_{n}")}" :: presource
  for (i,t) in sOTs.reverse do
    presource := s!"\ndef ot_{i} : QueryTree (BS (Nat × (RBNode ℕ (fun _ ↦ ℕ)))) := {QueryTree.toString_preBS' t (fun (n,_) => s!"({n}, o_nei_{n})") (fun n => s!"ot_{n}")}" :: presource
  presource := s!"\ndef OTreeTop : QueryTree (BS (Nat × (RBNode ℕ (fun _ ↦ ℕ)))) := {QueryTree.toString_preBS' sOTtop (fun (n, _) => s!"({n}, o_nei_{n})") (fun n => s!"ot_{n}")}" :: presource
  let source := s!"\nimport LeanGrow.QueryTree_idea\nopen Lean Data{String.join presource.reverse}"
  IO.FS.writeFile ⟨s!"/./home/yves/Desktop/CodeWorkspace/Lean4_General/LeanGrow/LeanGrow/Caches/LargeTransitionGraphs.lean"⟩ (source)


--make_large_transition_graphs
-- 2 min

--#exit


def getTotalWeight : RBNode ℕ (fun _ ↦ ℕ) → Nat :=
  RBNode.fold (fun sofar _ v => sofar + v) 0


def RBNode.getKeyVals : RBNode α (fun _ => β) → List (α × β)
| .leaf => []
| .node _ l k v r => (k, v) :: ((RBNode.getKeyVals l) ++ ( RBNode.getKeyVals r))



-- computes total weights along all walks of length N exactly
def n_step_closure_rbt' (N : Nat) (inner outer : List (Nat × (RBNode ℕ (fun _ ↦ ℕ)))) (key : Nat) : Option (RBNode ℕ (fun _ ↦ (ℕ × ℕ))) :=
  match N with
  | 0 =>
      -- in ↓ v = 0 shouldn't occur on our graphs
      (RBNode.map (fun _ v => if v ≠ 0 then (v,1) else (v,0))) <$> ((Prod.snd) <$> (outer.find? (Prod.fst · = key)))
  | n+1 => Id.run do
      let .some nei := Prod.snd <$> inner.find? (Prod.fst · = key) | return .none
      let res := RBNode.fold
          (fun sofar k v => Id.run do
              let .some sofar' := sofar | return .none
              let .some fromhere := Id.run do
                let .some clos := n_step_closure_rbt' n inner outer k | return Option.none
                return .some (RBNode.map (fun _ (total_weight, num_paths) => (total_weight+(v*num_paths), num_paths)) clos) | return Option.none
              return .some (RBNode.fold (fun S K V => RBNode.upsert instOrdNat.compare (fun x => x + V) V S K) sofar' fromhere)
              )
          (Option.some RBNode.leaf) nei
      return res

def n_step_closure_rbt (N : Nat) (inner outer : List (Nat × (RBNode ℕ (fun _ ↦ ℕ)))) (key : Nat) : Option (RBNode ℕ (fun _ ↦ (ℕ))) :=
  (RBNode.map (fun _ v => v.1)) <$> (n_step_closure_rbt' N inner outer key)


--#exit

def RBNode.fromList (l : List (Nat × Nat)) : RBNode ℕ (fun _ ↦ ℕ) :=
  l.foldl (fun s (k,v) => RBNode.insert instOrdNat.compare s k v ) RBNode.leaf

-- unit edge wuit four-cycle
def C4 : List (Nat × (RBNode ℕ (fun _ ↦ ℕ))) :=
  [(0, RBNode.fromList [(1,1), (3,1)]), (1, RBNode.fromList [(0,1), (2,1)]), (2, RBNode.fromList [(1,1), (3,1)]), (3, RBNode.fromList [(0,1), (2,1)]) ]

--#exit
#eval do
  let .some res := n_step_closure_rbt 0 C4 C4 0 | IO.println "aaahh"
  IO.println (RBNode.toString (fun x => s!"{x}") (fun x => s!"{x}") res)
  -- just the neighbourhood

#eval do
  let .some res := n_step_closure_rbt 1 C4 C4 0 | IO.println "aaahh"
  IO.println (RBNode.toString (fun x => s!"{x}") (fun x => s!"{x}") res)
  -- For example, 0 can gets weight 4 for 1 step because there are 2 paths of length
  -- less or equal to 2 that reach 0 from 0,each with wieght 2 : 0,1,0 and 0,3,0

#eval do
  let .some res := n_step_closure_rbt 2 C4 C4 0 | IO.println "aaahh"
  IO.println (RBNode.toString (fun x => s!"{x}") (fun x => s!"{x}") res)
  -- For example, 1 can gets weight 10 for 2 steps because there are 4 paths of length
  -- equal to 3 that reach 1 from 0, 4 wieght 3  :
  -- 0,1,0,1 and 0,1,2,1 and 0,3,2,1 and 0,3,0,1

#eval do
  let .some res := n_step_closure_rbt 2 C4 C4 1 | IO.println "aaahh"
  IO.println (RBNode.toString (fun x => s!"{x}") (fun x => s!"{x}") res)


#eval do
  let .some res := n_step_closure_rbt 3 C4 C4 0 | IO.println "aaahh"
  IO.println (RBNode.toString (fun x => s!"{x}") (fun x => s!"{x}") res)
  -- For example, 0 can gets weight 32 due to:
  -- 0,1,0,1,0 for 4 ; 0,1,0,3,0 for 4 ; 0,3,0,1,0 for 4 ; 0,3,0,3,0 for 4 ;
  -- 0,1,2,1,0 for 4 ; 0,3,2,3,0 for 4 ; 0,1,2,3,0 for 4 ; 0,3,2,1,0 for 4 ;
  --and 8*4 = 32

--#exit

/-- requires no BEq on α-/
def List.hasNone? : List (Option α) → Bool
| [] => false
| x :: xs =>
    match x with
    | .none => true
    | _ => xs.hasNone?

partial def QueryTree.mapBS_Opt (f : α → Option β) : QueryTree (BS α) → Option (QueryTree (BS β))
| .root c =>
    let cn := (c.map (QueryTree.mapBS_Opt f))
    if cn.hasNone? then .none else .some (.root (cn.reduceOption))
| .node t c =>
    let cn := (c.map (QueryTree.mapBS_Opt f))
    if cn.hasNone? then .none else .some (.node t (cn.reduceOption))
| .leaf (.ofVal x) =>
    match f x with
    | .some fx => .some (.leaf (.ofVal (fx)))
    | _ => .none
| .leaf (.ofPoint p) =>
    match QueryTree.mapBS_Opt f p with
    | .some P => .some (.leaf (.ofPoint P))
    | _ => .none

partial def QueryTree.map_Opt (f : α → Option β) : QueryTree α → Option (QueryTree β)
| .root c =>
    let cn := (c.map (QueryTree.map_Opt f))
    if cn.hasNone? then .none else .some (.root (cn.reduceOption))
| .node t c =>
    let cn := (c.map (QueryTree.map_Opt f))
    if cn.hasNone? then .none else .some (.node t (cn.reduceOption))
| .leaf x =>
    match f x with
    | .some fx => .some (.leaf fx)
    | _ => .none




def n_step_closure (N : Nat) (inner outer : QueryTree (Nat × (RBNode ℕ (fun _ ↦ ℕ)))) : Option (QueryTree (Nat × (RBNode ℕ (fun _ ↦ ℕ)))) :=
  let inner' := QueryTree.getVals inner
  let outer' := QueryTree.getVals outer
  QueryTree.map_Opt (fun (k,_) => (k, · ) <$> n_step_closure_rbt N inner' outer' k) inner


def QueryTree.getChildren : QueryTree α → List (QueryTree  α)
| .root c => c
| .node _ c => c
| .leaf _ => []


def QueryTree.get_vals_of_valLeaves : List (QueryTree α) → List α
| [] => []
| x :: l =>
      match x with
      | .leaf a => a :: (QueryTree.get_vals_of_valLeaves l)
      | .node (.leaf .none) [.leaf a] => a :: (QueryTree.get_vals_of_valLeaves l) -- don't know if necessary...
      | _ => [] --fail (aka. early return)


def QueryTree.get_tree_of_pointLeaves : List (QueryTree (BS α)) → List (QueryTree (BS α))
| [] => []
| x :: l =>
      match x with
      | .leaf (.ofPoint a) => a :: (QueryTree.get_tree_of_pointLeaves l)
      | .node (.leaf .none) [.leaf (.ofPoint a)] => a :: (QueryTree.get_tree_of_pointLeaves l) -- don't know if necessary...
      | _ => [] --fail (aka. early return)


partial def List.process_Lists (m : List α → Option α) (l : List (List α)) : Option (List α) :=
  let hds := l.map List.head?
  if hds.hasNone?
  then
    --dbg_trace "fail at List.process_Lists 1"
    .some [] -- maybe due to the anoying .node [] [.leaf] phenomenon ??
  else
    match m hds.reduceOption with
    | .some y => (y :: ·) <$> (List.process_Lists m (l.map List.tail))
    | .none =>
        --dbg_trace "fail at List.process_Lists 2"
        .none

/-- assumes that the trees of the list are the same , excpet of the leaf-values-/
partial def QueryTree.merge (m : List α → Option α)  (data : List (QueryTree  α)) : Option (QueryTree α) :=
  match QueryTree.get_vals_of_valLeaves data with
  | [] =>
      let chi := data.map QueryTree.getChildren
      let res := List.process_Lists (QueryTree.merge m) chi
      match data with
      | .root _ :: _ => (.root) <$> res
      | .node t _ :: _ => (.node t) <$> res
      | _ => .none
  | l =>  (fun x => QueryTree.leaf x) <$> (m l)



def merge_rbt (l : List (Nat × (RBNode ℕ (fun _ ↦ ℕ)))) : Option (Nat × (RBNode ℕ (fun _ ↦ ℕ))) :=
  match l.head? with
  | .some (n,_) =>
      let rbts := l.map Prod.snd
      .some (n, rbts.foldl (fun S rbt => (rbt.fold (fun s k v => s.insert instOrdNat.compare k v) S) ) RBNode.leaf)
  | _ =>
      dbg_trace "fail at merge_rbt"
      .none



-- we can probably do better, since the closers are recomputed for larger steps ...
def n_step_closure_full (N : Nat) (inner outer : QueryTree (Nat × (RBNode ℕ (fun _ ↦ ℕ)))) : Option (QueryTree (Nat × (RBNode ℕ (fun _ ↦ ℕ)))) :=
  let ouf := ((List.range N).map (n_step_closure · inner outer)).reduceOption
  QueryTree.merge merge_rbt ouf



elab "make_large_transition_graph_closure" : command => do
  let clos_step := 3
  let .some inner_trans_large := (QueryTree.deStratify true ITreeTop).head? | throwError "aaahhh"
  let .some outer_trans_large := (QueryTree.deStratify true OTreeTop).head? | throwError "aaahhh"
  let .some res := n_step_closure_full clos_step inner_trans_large outer_trans_large | throwError "Fail :<"
  let RV := QueryTree.getVals res
  let (_ , sRTs, sRTtop) := QueryTree.stratify 2 2 0 res
  let mut presource := []
  for (i,nei) in RV do
    presource := s!"\ndef r_nei_{i} : RBNode ℕ (fun _ ↦ ℕ) := {printRBT nei}" :: presource
  presource := s!"\ndef r_nei_all : List (Nat × (RBNode ℕ (fun _ ↦ ℕ))) := [{String.intercalate ", " ((RV.map Prod.fst).map (fun n => s!"({n}, r_nei_{n})"))}]" :: presource
  for (i,t) in sRTs.reverse do
    presource := s!"\ndef rt_{i} : QueryTree (BS (Nat × (RBNode ℕ (fun _ ↦ ℕ)))) := {QueryTree.toString_preBS' t (fun (n,_) => s!"({n}, r_nei_{n})") (fun n => s!"rt_{n}")}" :: presource
  presource := s!"\ndef RTreeTop : QueryTree (BS (Nat × (RBNode ℕ (fun _ ↦ ℕ)))) := {QueryTree.toString_preBS' sRTtop (fun (n, _) => s!"({n}, r_nei_{n})") (fun n => s!"rt_{n}")}" :: presource
  let source := s!"\nimport LeanGrow.QueryTree_idea\nopen Lean Data{String.join presource.reverse}"
  IO.FS.writeFile ⟨s!"/./home/yves/Desktop/CodeWorkspace/Lean4_General/LeanGrow/LeanGrow/Caches/LargeTransitionGraphClosure_clos_{clos_step}.lean"⟩ (source)

--make_large_transition_graph_closure
-- ≤ 20 min

--#exit


-- # Analysis of clusters and graphs


def print_cluster_hyp_names (L : List pdata) : List String :=
  List.dedup ((L.map pdata.sink_cst_names).map (Trie.print_keys ⟨#[]⟩)).join

def print_cluster_goal_names (L : List pdata) : List String :=
  List.dedup ((L.map pdata.goal_cst_names).map (Trie.print_keys ⟨#[]⟩)).join

def get_cluster_list_from_index (i : Nat) : List pdata :=
  match Lsclu_from_qt_all.find? (fun (j,_) => i=j) with
  | .some l => l.2
  | _ => []

#check RBNode.getKeyVals

elab "one_step_analysis" : command => do
  let clus_nr := 42
  let mut toPrint := []
  let .some (_,data) := Lsclu_from_qt_all.find? (fun (n,_) => n == clus_nr) | throwError "aaahh 1"
  toPrint := s!"Inspecting cluster {clus_nr}.\nIts hyp-names {print_cluster_hyp_names data}\nIts thms {data.map pdata.cst_name}" :: toPrint
  let .some (_, neis) := r_nei_all.find? (fun (n,_) => n == clus_nr) | throwError "aaahh 2"
  for (nr, hits) in RBNode.getKeyVals neis do
    let .some (_,data_2) := Lsclu_from_qt_all.find? (fun (n,_) => n == nr) | throwError "aaahh 3"
    toPrint := s!"\n\nLink to cluster {nr} with score {hits}.\nIts hyp-names {print_cluster_hyp_names data_2}\nIts thms {data_2.map pdata.cst_name}" :: toPrint
  IO.println (String.join toPrint.reverse)

--one_step_analysis

/-

Inspecting cluster 42.
Its hyp-names [Sigma.fst, Sigma, Ne, List]
Its thms [List.kerase_cons_ne, List.dlookup_cons_ne, List.lookupAll_cons_ne, List.dlookup_kinsert_ne, List.dlookup_kerase_ne, List.mem_keys_kerase_of_ne]

Link to cluster 32 with score 2453980.
Its hyp-names [Bool, Bool.true, WithTop, WithTop.some, List.minimum, WithBot, WithBot.some, Membership.mem, List, List.maximum, List.instMembership, Eq]
Its thms [List.mem_filter_of_mem, List.length_eraseP_add_one, List.minimum_not_lt_of_mem, List.not_lt_maximum_of_mem]

Link to cluster 16 with score 3528723.
Its hyp-names [Nat, List.Subperm, List.Nodup, List.dedup, instHAppendOfAppend, Ne, List.nil, List.instAppend, List.cons, HAppend.hAppend, Not, Membership.mem, List, List.instMembership]
Its thms [List.Nodup.set, List.Nodup.concat, List.Nodup.cons, List.cons_subperm_of_mem, List.dedup_cons_of_not_mem', List.injOn_insertNth_index_of_not_mem, List.indexOf_of_not_mem, List.nodup_permutations'Aux_of_not_mem, List.append_cons_inj_of_not_mem, List.erase_orderedInsert_of_not_mem, List.next_cons_concat, List.dedup_cons_of_not_mem, List.nextOr_concat, List.cons_bagInter_of_neg, List.insert_neg, List.indexOf_append_of_not_mem, List.inter_cons_of_not_mem]

Link to cluster 8 with score 2360857.
Its hyp-names [List.instInterOfBEq_batteries, Inter.inter, instBEqOfDecidableEq, Union.union, Membership.mem, List, List.instUnionOfBEq_batteries, List.instMembership, LeanGrowLabel.pi]
Its thms [List.forall_mem_inter_of_forall_right, List.forall_mem_inter_of_forall_left, List.forall_mem_of_forall_mem_union_left, List.forall_mem_of_forall_mem_union_right]

Link to cluster 4 with score 5076176.
Its hyp-names [WithBot, WithBot.some, WithBot.preorder, instDistribLatticeOfLinearOrder, WithTop, WithTop.some, WithTop.preorder, SemilatticeInf.toPartialOrder, Preorder.toLE, PartialOrder.toPreorder, Lattice.toSemilatticeInf, LE.le, DistribLattice.toLattice, List.Duplicate, Iff, LeanGrowLabel.sort, semigroupDvd, SemigroupWithZero.toSemigroup, Prime, MulZeroOneClass.toMulZeroClass, MulZeroClass.toMul, MonoidWithZero.toSemigroupWithZero, MonoidWithZero.toMulZeroOneClass, MonoidWithZero.toMonoid, Monoid.toOne, List.prod, Dvd.dvd, CommMonoidWithZero.toMonoidWithZero, CancelCommMonoidWithZero.toCommMonoidWithZero, Symmetric, List.Pairwise, List.cons, Nat, List.Chain, Subtype, Bool, Function.Injective, List.map, List.Perm, Reflexive, Ne, Sigma, Sigma.mk, Not, instHAppendOfAppend, Membership.mem, List, List.instMembership, List.instAppend, LeanGrowLabel.pi, HAppend.hAppend]
Its thms [List.max_le_of_forall_le, List.maximum_le_of_forall_le, List.le_min_of_forall_le, List.le_minimum_of_forall_le, List.Duplicate.below.cons_mem, List.tfae_of_forall, List.pairwise_pmap, Prime.not_dvd_prod, mem_list_primes_of_dvd_prod, List.Pairwise.pmap, List.Pairwise.forall_of_forall, List.forall_mem_of_forall_mem_cons, List.foldrRecOn_cons, List.getElem?_pmap, List.get?_pmap, List.foldlRecOn, List.chain_pmap_of_chain, List.filter_attach', List.injective_foldl_comp, List.map_pmap, List.pmap_eq_map_attach, List.pmap_map, List.pmap_eq_nil, List.Perm.bind_left, List.pmap_eq_map, List.pairwise_of_forall_mem_list, List.lookup_graph, List.pairwise_of_reflexive_of_forall_ne, List.infix_bind_of_mem, List.mem_pmap, List.pmap_append', List.length_pmap, List.foldrRecOn, List.kreplace_of_forall_not, List.pmap_append]

Link to cluster 1 with score 43025148.
Its hyp-names [Levenshtein.Cost, LeanGrowLabel.sort, Option, Function.Injective, instHAppendOfAppend, List.instAppend, HAppend.hAppend, List.Perm, Prod, List.inits, List.cyclicPermutations, List.tails, List.length, Fin, Bool, List.Lex, Function.Involutive, List.instHasSubset_batteries, HasSubset.Subset, PartialOrder.toPreorder, List.Chain', LinearOrder.toPartialOrder, GT.gt, List.LE', LE.le, Sym2, Prime, Cycle, List.Disjoint, Not, Preorder.toLT, List.cons, List.LT', LT.lt, List]
Its thms [suffixLevenshtein_nil', levenshtein_cons_cons, suffixLevenshtein_eq_tails_map, levenshtein_nil_cons, instEstimatorMkLevenshteinLevenshteinEstimatorOfWellFoundedGTSubtypeProdNatLe, LevenshteinEstimator, suffixLevenshtein_minimum_le_levenshtein_cons, suffixLevenshtein_length, le_suffixLevenshtein_append_minimum, le_levenshtein_cons, levenshtein, instEstimatorDataProdNatMkMkLevenshteinLengthLevenshteinEstimator', instBotLevenshteinEstimator, suffixLevenshtein_cons₂, le_suffixLevenshtein_cons_minimum, suffixLevenshtein_cons₁_fst, estimator', suffixLevenshtein_eq, le_levenshtein_append, suffixLevenshtein_cons₁, levenshtein_cons_nil, suffixLevenshtein_minimum_le_levenshtein_append, suffixLevenshtein, List.zipLeft_nil_right, List.zipRight_nil_right, List.zipLeft_nil_left, List.zipRight'_nil_right, List.zipRight_nil_cons, List.zipRight'_nil_left, List.product_nil, List.tfae_cons_self, List.zipLeft'_nil_left, List.tfae_not_iff, List.tfae_cons_cons, List.nil_product, List.zipLeft'_nil_right, List.zipLeft_cons_nil, List.zipRight_nil_left, List.zipRight'_nil_cons, List.zipLeft'_cons_nil, List.TFAE, List.reduceOption_length_eq, List.reduceOption_length_lt_iff, List.reduceOption_concat_of_some, List.reduceOption_append, List.reduceOption_get?_iff, List.reduceOption_cons_of_none, List.reduceOption_length_le, List.reduceOption_cons_of_some, List.reduceOption_length_eq_iff, List.foldl_argAux_eq_none, List.length_eq_reduceOption_length_add_filter_none, List.reduceOption_mem_iff, List.reduceOption_concat, List.map_filter', List.map_erase, List.nodup_map_iff, List.map_subset_iff, List.count_map_of_injective, List.mem_map_of_injective, List.map_foldl_erase, List.map_diff, List.Perm.bagInter_left, List.Perm.subset_congr_left, List.mem_permutationsAux_of_perm, List.Perm.product_right, List.Perm.subset_congr_right, List.Perm.product_left, List.Perm.bagInter_right, List.unzip_swap, List.unzip_right, List.mem_map_swap, List.unzip_left, List.unzip_eq_map, List.zip_unzip, List.get_inits, List.get_cyclicPermutations, List.drop_take_succ_join_eq_get', List.get_tails, List.orM, List.andM, List.replaceIf, List.Lex.append_right, List.Lex.append_left, List.Lex.isOrderConnected.aux, Function.Involutive.exists_mem_and_apply_eq_iff, List.mem_map_of_involutive, List.subset_inter, List.append_subset_of_subset_of_subset, List.Chain'.cons_of_le, List.cons_le_cons, List.mem_sym2_cons_iff, List.mem_sym2_iff, List.getElem?_length, List.count_bagInter, List.nodup_sublists', List.sublist_singleton, List.mem_foldr_permutationsAux2, List.duplicate_iff_sublist, List.permutationsAux_append, List.length_pos_iff_ne_nil, List.permutations'Aux, Prime.dvd_prod_iff, List.ext_get?_iff, List.isRotated_nil_iff', List.permutations_perm_permutations', List.nodup_iff_nthLe_inj, List.map_reverse_tails, List.nodup_attach, List.perm_orderedInsert, List.perm_mergeSort, List.Palindrome.append_reverse, List.destutter_is_chain', List.chain'_isInfix, List.length_permutationsAux, List.prefix_iff_eq_take, List.exists_duplicate_iff_not_nodup, List.findIdxs_eq_map_indexesValues, List.isEmpty_iff_eq_nil, List.getLast_concat', List.maximum, List.tails_reverse, List.chain'_iff_pairwise, List.rotate_zero, List.rotate_one_eq_self_iff_eq_replicate, List.nodup_append_comm, List.dedup_sublist, List.suffix_rfl, List.Palindrome.instDecidableOfDecidableEq, List.permutations'Aux_eq_permutationsAux2, List.inits_append, List.zipLeft_cons_cons, List.forall₂_refl, List.IsRotated.refl, List.mergeSort, List.inter_subset_right, List.permutations, List.destutter'_eq_self_iff, List.mem_product, Cycle.lists_coe, List.decidableChain, Cycle.ofList, List.subset_singleton_iff, List.length_tails, List.set_of_mem_cons, List.prefix_concat, List.rtake_zero, List.suffix_iff_eq_drop, List.length_split_snd_le, List.join_join, List.join_filter_ne_nil, List.perm_permutations_iff, List.getLast_append_singleton, List.nodup_reverse, List.tails_eq_inits, List.subperm_cons_self, List.infix_insert, List.map_pure_sublist_sublists, List.prefix_concat_iff, List.intersperse_cons_cons, List.sym_one_eq, List.maximum_eq_none, List.cyclicPermutations, List.inter_eq_nil_iff_disjoint, List.append_left_eq_self, List.length_cyclicPermutations_cons, List.duplicate_iff_exists_distinct_nthLe, List.destutter_cons_cons, Cycle.mem_coe_iff, List.zipLeft_eq_zipLeft', List.revzip_swap, List.bagInter_nil_iff_inter_nil, List.orderedInsert_count, List.equivSigmaTuple_apply_fst, List.isRotated_iff_mod, List.count_eq_count_filter_add, List.join_filter_isEmpty_eq_false, List.sublists'_cons, List.subperm_nil, Cycle.mk''_eq_coe, List.rdrop_append_length, List.sublists'Aux_eq_array_foldl, List.isRotated_singleton_iff', List.getLastI_eq_getLast?, List.sublists'_reverse, List.inter_subset_left, List.perm_rfl, List.permutationsAux_cons, List.dedup_eq_cons, List.length_inits, List.forall_mem_ne, List.nodup_cons, List.revzip_map_fst, List.rotate'_zero, List.head?_cyclicPermutations, List.foldl_assoc_comm_cons, List.map_ret_sublist_sublists, List.sublistsLen_zero, List.decidableDuplicate, List.sublists_concat, Cycle.mk_eq_coe, List.nodup_iff_sublist, List.prefix_rfl, List.cons_eq_append_iff, List.head!_eq_head?, List.join_filter_not_isEmpty, List.ofFn_getElem, List.sublistsLen_length, List.dedup_append, List.subperm_iff, List.rotate_append_length_eq, List.nodup_append, List.foldr_fixed, List.getLast?_isNone, List.bagInter_sublist_left, List.minimum_eq_top, List.dropLast_prefix, List.concat_eq_reverse_cons, List.foldr_permutationsAux2, List.dedup_eq_self, List.enum_cons', List.zipRight_eq_zipRight', List.insertNth_zero, List.reverse_eq_iff, List.foldl_op_eq_op_foldr_assoc, List.lt_iff_lex_lt, List.getLast?_eq_none, List.subset_dedup, List.append_join_map_append, List.perm_permutations'_iff, List.inits_eq_tails, List.sublists_append, List.subperm_singleton_iff, List.tail_subset, Cycle.nodup_coe_iff, List.attach_map_val, List.destutter'_ne_nil, List.indexesValues_eq_filter_enum, List.headI_dedup, List.insertionSort_cons_eq_take_drop, List.zipLeft'_cons_cons, List.length_permutations'Aux, List.length_sublists, List.reverse_foldl, List.mk_mem_sym2_iff, List.nodup_iff_injective_getElem, List.maximum_eq_coe_iff, List.orderedInsert_eq_take_drop, List.enum_eq_zip_range, List.dedup_eq_nil, List.decidableChain', List.append_right_eq_self, List.rotate_length, List.Lex.isTrichotomous.aux, List.destutter, List.cyclicPermutations_cons, List.append_left_injective, List.sublists_cons_perm_append, List.sublist_nil_iff_eq_nil, List.map_reverse_inits, List.sym2_eq_nil_iff, List.length_mergeSort, List.mem_cyclicPermutations_self, List.rotate_eq_self_iff_eq_replicate, List.permutations_append, List.tail_sublistForall₂_self, List.sym2, List.cyclicPermutations_inj, List.isRotated_concat, List.nil_lt_cons, List.head!_cons, List.mem_sublists, List.sublist_insert, List.mem_permutationsAux2, List.mem_tails, List.filter_false, List.Lex.cons_iff, List.tail_suffix, Cycle.mem_lists_iff_coe_eq, List.nodup_join, List.IsRotated, List.prefix_iff_eq_append, List.nextOr, List.tails_append, List.cyclicPermutations_ne_nil, List.nodup_permutations'Aux_iff, List.minimum_le_coe_iff, Cycle.reverse_coe, List.join_singleton, List.infix_rfl, List.nextOr_self_cons_cons, List.length_attach, List.attach_eq_nil, List.permutations', List.zipRight'_cons_cons, List.foldl_assoc, List.inter_reverse, List.mem_dedup, Cycle.coe_toFinset, List.cons_prefix_iff, Cycle.decidableNontrivialCoe, List.nodup_iff_get?_ne_get?, List.insertionSort, List.join_append, List.destutter_idem, List.decidableSublist, List.nodup_iff_forall_not_duplicate, List.sublistsAux, List.cons_sublist_cons', List.sublist_iff_exists_orderEmbedding_get?_eq, List.maximum_concat, List.mem_inits, List.isRotated_comm, List.isRotated_iff_mem_map_range, Cycle.coe_eq_nil, List.destutter'_cons_pos, List.getLast?_cons_cons, List.rotate'_length, List.tail_dedup, List.reverse_join, List.dedup_subset, Cycle.coe_cons_eq_coe_append, List.Lex.rel, List.ext_get_iff, List.getI_zero_eq_headI, List.get?_length, List.inter_nil, List.self_eq_append_right, List.destutter'_sublist, List.unzip_enum_eq_prod, List.enum_append, List.insertNth_length_self, List.chain_iff_pairwise, List.ext_get?_iff', List.minimum_eq_coe_iff, List.mem_cyclicPermutations_iff, List.isRotated_cyclicPermutations_iff, List.length_foldr_permutationsAux2, List.destutter_cons', List.mem_destutter', List.suffix_iff_eq_append, List.destutter_sublist, List.minimum, List.length_sym2, List.minimum_cons, List.count_permutations'Aux_self, List.indexOf_eq_length, List.destutter', List.sublists_eq_sublists', List.ofFn_nthLe, List.inits_reverse, List.indexOf_lt_length, List.isRotated_singleton_iff, List.sublists'_eq_sublists'Aux, List.unzip_revzip, Cycle.length_coe, List.decidableSuffix, List.duplicate_iff_exists_distinct_get, List.destutter'_cons, List.suffix_insert, List.extractp, List.count_dedup, List.length_product, List.join_reverse, List.mem_orderedInsert, List.dedup, List.length_split_fst_le, List.maximum_cons, List.nodup_iff_injective_get, List.sublist_orderedInsert, List.reverse_concat', List.suffix_union_right, List.append_eq_has_append, List.enum_eq_nil, List.bagInter_nil, List.subset_insert, List.length_sublists', List.zip_swap, List.cons_sublist_cons_iff, List.sublist_suffix_of_union, List.sorted_insertionSort, List.isRotatedDecidable, List.nil_bagInter, List.nodup_iff_count_eq_one, List.takeI_left, List.nodup_sublists, List.length_eq_three, List.indexOf_cons_self, List.mergeSort_eq_insertionSort, List.isRotated_append, List.filter_true, List.nodup_iff_getElem?_ne_getElem?, List.nil_le, List.count_cons', List.takeD_left, List.decidableSorted, List.mem_permutations, List.mem_permutations', List.length_join', List.rdrop_zero, List.destutter'_is_chain, List.join_eq_nil, List.sublists'Aux, List.decidableInfix, List.perm_permutations'Aux_comm, List.mem_iff_nthLe, List.sorted_mergeSort, List.isRotated_reverse_comm_iff, List.erase_orderedInsert, List.perm_insertionSort, Cycle.coe_eq_coe, List.range_bind_sublistsLen_perm, List.getLast?_isSome, List.self_eq_append_left, List.Perm.inter_append, List.tails_cons, List.Palindrome.iff_reverse_eq, List.sublists_cons, List.destutter'_cons_neg, List.head_cyclicPermutations, List.reverse_revzip, List.zipRight_cons_cons, List.foldr_eta, List.dropLast_subset, List.duplicate_cons_iff, List.split, List.mem_permutationsAux2', List.join_concat, List.coe_le_maximum_iff, List.isRotated_nil_iff, List.foldl_fixed, List.cyclicPermutations_eq_singleton_iff, List.append_right_injective, List.ofFn_get, List.count_join', List.nodup_enum_map_fst, List.getLast_cons_cons, List.exists_mem_cons_of, List.lookmap_some, List.sublists_perm_sublists', List.mem_sublists', List.enum_map_snd, List.instDecidableR_mathlib, List.mem_bagInter, List.orderedInsert, List.tail_sublist, List.getI_cons_zero, List.length_revzip, List.intercalate_splitOn, List.orderedInsert_length, List.reverse_inj, List.mem_sections, List.sublists'Aux_eq_map, List.dropLast_sublist, List.indexOf_le_length, List.sym2_eq_sym_two, List.reverse_cons', List.lookmap_none, List.finRange_map_get, List.decidablePrefix, List.maximum_eq_bot, List.union_sublist_append, List.nodup_dedup, List.sublists_reverse, List.permutationsAux, List.dedup_idem, List.isRotated_reverse_iff, List.minimum_concat, List.inits_cons, List.nodup_iff_count_le_one, List.append_eq_cons_iff, Cycle.coe_toMultiset, List.getLast?_append_cons, List.revzip_map_snd, List.head_le_of_lt, List.sublists'_eq_sublists, List.sublist_iff_exists_fin_orderEmbedding_get_eq, List.destutter_eq_nil, List.length_eq_two, List.cyclicPermutations_eq_nil_iff, List.destutter'_is_chain', List.mem_zip_inits_tails, List.minimum_eq_none, List.duplicate_iff_two_le_count, List.sublistsLen_one, List.duplicate_cons_self_iff, List.insert_eq_ite, List.destutter_eq_self_iff, List.nodup_middle, List.length_permutations, List.permutationsAux_nil, List.product_cons]

Link to cluster 0 with score 2429781.
Its hyp-names [LevenshteinEstimator', List.IsRotated, Symmetric, List.Pairwise, String, Levenshtein.Cost, List.cons_ne_nil, WithTop, WithTop.some, List.minimum, WithBot, WithBot.some, List.maximum, Eq, List.ne_nil_of_mem, List.getLast, Ne, List.nextOr, Relator.BiUnique, List.Forall₂, List.cons, List.Subperm, Function.Injective, List.Chain, List.Lex, List.Palindrome, List.SublistForall₂.below, List.SublistForall₂, Relator.RightUnique, Function.Involutive, Sigma, List.Palindrome.below, List.IsSuffix, List.Duplicate.below, List.Lex.below, Function.LeftInverse, Irreflexive, Function.RightInverse, Relator.LeftUnique, List.IsPrefix, Relation.ReflTransGen, WellFounded, List.Disjoint, List.IsInfix, Function.Surjective, Cycle.Nodup, List.chains, List.TFAE, Cycle.Subsingleton, AList.Disjoint, Function.Bijective, Cycle.Nontrivial]
Its thms [List.LT', List.SublistForall₂.is_refl, List.replicate_left_injective, List.destutter_nil, List.getLast_singleton', List.instLinearOrder, List.not_duplicate_singleton, List.Palindrome.singleton, List.uniqueOfIsEmpty, List.Lex.isTrichotomous, AList.insert_empty, Levenshtein.instInhabitedCostNatOfDecidableEq, List.nextOr_singleton, List.Lex.isOrderConnected, Cycle.fintypeNodupCycle, AList.singleton_entries, AList.insert_singleton_eq, List.destutter'_nil, List.instDecidablePredForall, List.surjective_head!, List.toFinsupp_cons_apply_zero, List.Lex.isStrictTotalOrder, List.toFinsupp_singleton, Levenshtein.defaultCost_insert, Levenshtein.defaultCost_substitute, Levenshtein.defaultCost_delete, List.destutter_pair, List.reverse_singleton, Levenshtein.stringLengthCost, Levenshtein.defaultCost, Levenshtein.stringLogLengthCost, List.toFinsupp, List.not_duplicate_nil, List.sublists_eq_sublistsFast, List.mergeSort_singleton, List.destutter'_singleton, List.decidableGetDNilNe, List.SublistForall₂.is_trans, List.Nat.antidiagonal_zero, List.singleton_inj, List.orderedInsert_nil, Cycle.fintypeNodupNontrivialCycle, List.Lex.decidableRel, List.«term_~r_», List.not_nodup_pair, List.maximum_singleton, List.minimum_singleton, List.finRange_zero, List.sublists_singleton, List.toFinsupp_append, List.toFinsupp_cons_eq_single_add_embDomain, Cycle.instRepr, List.coe_toFinsupp, List.nodup_singleton, List.singleton_eq, AList.instDecidableEq, List.iterate_eq_iterateTR, List.minimum_nil, List.maximum_nil, List.splitOn_nil, List.Lex.isAsymm, List.mem_pair, List.length_injective, List.instLawfulSingleton_mathlib, List.instIsSymmOpZipWith, Cycle.not_mem_nil, List.intersperse_singleton, List.dedup_nil, List.cons_injective, List.mergeSort_nil, List.instInsertOfDecidableEq_mathlib, List.LE', List.toFinsupp_concat_eq_toFinsupp_add_single, List.toFinsupp_eq_sum_map_enum_single, List.destutter_singleton, Cycle.instDecidableEq, List.mem_pure, List.head!_nil, instIsWellFoundedChainsLex_chains, List.toFinsupp_nil, List.nextOr_nil, AList.singleton, List.injective_permutations'Aux, List.instSDiffOfDecidableEq_mathlib, AList.keys_singleton, List.enum_singleton, List.tfae_nil, List.toFinsupp_support, List.sublists'_singleton, Cycle.nil_toFinset, LevenshteinEstimator'.bound, LevenshteinEstimator'.suff, LevenshteinEstimator'.pre_rev, LevenshteinEstimator'.distances, LevenshteinEstimator'.split, LevenshteinEstimator'.bound_eq, LevenshteinEstimator'.distances_eq, List.IsRotated.symm, List.IsRotated.perm, List.IsRotated.reverse, List.IsRotated.cyclicPermutations, List.IsRotated.mem_iff, List.IsRotated.nodup_iff, List.IsRotated.trans, List.pairwise_sublists, List.Pairwise.chain', List.Pairwise.set_pairwise, List.Pairwise.sublists', List.Pairwise.pwFilter, List.Pairwise.nodup, Levenshtein.stringLengthCost_substitute, Levenshtein.stringLogLengthCost_delete, Levenshtein.stringLengthCost_insert, Levenshtein.stringLogLengthCost_insert, Levenshtein.stringLengthCost_delete, Levenshtein.stringLogLengthCost_substitute, Levenshtein.Cost.substitute, levenshtein_nil_nil, Levenshtein.Cost.delete, Levenshtein.Cost.insert, suffixLevenshtein_nil_nil, List.relationReflTransGen_of_exists_chain, List.minimum_mem, List.maximum_mem, List.zipWith_congr, List.doubleton_eq, List.nextOr_eq_nextOr_of_mem_of_ne, List.Lex.to_ne, List.mem_of_nextOr_ne, List.rel_perm, Relator.BiUnique.forall₂, List.rel_mem, List.rel_nodup, List.left_unique_forall₂', List.right_unique_forall₂', List.Forall₂.length_eq, List.subperm.of_cons, List.subperm.cons, List.Subperm.sym2, Function.Injective.list_map, List.disjoint_map, List.Chain.pairwise, List.destutter'_of_chain, List.Lex.cons, List.Lex.isAsymm.aux, List.Palindrome.reverse_eq, List.Palindrome.cons_concat, List.SublistForall₂.below.cons, List.SublistForall₂.below.cons_right, List.SublistForall₂.cons, List.SublistForall₂.cons_right, Relator.RightUnique.forall₂, List.rel_perm_imp, Function.Involutive.list_map, List.nodupKeys_singleton, List.Palindrome.below.cons_concat, List.isSuffix.reverse, List.Duplicate.below.cons_duplicate, List.Lex.below.cons, Function.LeftInverse.list_map, List.argAux_self, Function.RightInverse.list_map, Relator.LeftUnique.forall₂, List.isPrefix.reverse, List.exists_chain_of_relationReflTransGen, WellFounded.list_chain', List.Disjoint.symm, List.isInfix.reverse, Function.Surjective.list_map, Cycle.Nodup.nontrivial_iff, List.lex_chains, List.TFAE.not, Cycle.Subsingleton.nodup, AList.union_comm_of_disjoint, Function.Bijective.list_map, Cycle.length_nontrivial]

Link to cluster 2 with score 16330339.
Its hyp-names [List.instHasSubset_batteries, HasSubset.Subset, ULift, Bool.true, Bool, Option, List.map, Eq, Iff, Prod, List.Palindrome, List.Palindrome.below, List.Lex, List.Lex.below, Array, PUnit, List.SublistForall₂, List.SublistForall₂.below, List.Duplicate, List.Duplicate.below, Ne, List.nil, Unit, List, LeanGrowLabel.pi]
Its thms [List.rdropWhile_concat, List.takeWhile_takeWhile, List.findIdx_le_length, List.findIdx_lt_length, List.splitOnP_cons, List.rtakeWhile_concat, List.rtakeWhile, List.countP_join', List.span_eq_take_drop, List.splitOnP_ne_nil, List.filter_attach, List.rdropWhile_eq_nil_iff, List.countP_bind', List.takeWhile_eq_nil_iff, List.dropWhile_idempotent, List.rdropWhile, List.takeWhile_prefix, List.rtakeWhile_eq_nil_iff, List.dropWhile_eq_self_iff, List.splitOnP_spec, List.filter_comm, List.length_filter_lt_length_iff_exists, List.dropWhile_eq_nil_iff, List.dropWhile_suffix, List.findIdx_eq_length, List.monotone_filter_left, List.rdropWhile_idempotent, List.rtakeWhile_suffix, List.findM?', List.splitOnP.go_ne_nil, List.rdropWhile_prefix, List.rdropWhile_eq_self_iff, List.rtakeWhile_eq_self_iff, List.monotone_filter_right, List.takeWhile_idem, List.filter_subset, List.filter_eq_foldr, List.rtakeWhile_idempotent, List.span.loop_eq_take_drop, List.length_eq_length_filter_add, List.splitOnP.go_acc, List.countP_attach, List.takeWhile_eq_self_iff, List.map₂Right_nil_cons, List.map₂Right_cons_cons, List.map₂Left_eq_map₂Left', List.length_lookmap, List.map₂Right'_nil_left, List.map₂Right'_nil_cons, List.map₂Right_nil_left, List.map₂Right, List.filterMap_eq_bind_toList, List.reduceOption_map, List.map₂Left, List.map₂Right'_nil_right, List.filterMap_eq_map_iff_forall_eq_some, List.map₂Right_eq_map₂Right', List.lookmap.go_append, List.map₂Left_nil_right, List.map₂Right', List.map₂Left'_nil_right, List.map₂Right'_cons_cons, List.map₂Right_nil_right, List.map₂Left', List.foldl_eq_of_comm', List.foldl_hom₂, List.zipWith_comm_of_comm, List.map_permutationsAux2', List.foldr_fixed', List.foldr_hom₂, List.foldl_eq_foldr', List.foldr_eq_of_comm', List.foldl_fixed', List.Chain'.iff, List.Chain.iff, List.mapAccumr₂_eq_foldr, List.mapAccumr_eq_foldr, List.argmin_concat, List.zipWith_zipWith_left, List.map_map_permutationsAux2, List.bind_eq_nil, List.scanl_cons, List.modifyLast_append_one, List.argmin_cons, List.attach_map_val', List.map_tail, List.sublists'_map, List.map_uncurry_zip_eq_zipWith, List.get?_zero_scanl, List.zipWith_comm, List.map_permutationsAux2, List.map_permutations, List.Palindrome.brecOn, List.attach_map_coe', List.mem_sigma, List.permutationsAux2_comp_append, List.foldl_join, List.map_reverseAux, List.bind_pure_eq_map, List.sublists_map, List.foldlM_eq_foldl, List.permutationsAux2_snd_cons, List.zipWith_zipWith_right, List.zipWith3_same_left, List.ofFn_getElem_eq_map, List.enum_map, List.Lex.brecOn, List.argmin, List.bind_eq_bind, List.zipWith_flip, List.modifyLast.go_append_one, List.findM, List.length_sigma', List.zipWith_nil, List.nil_zipWith, List.length_permutationsAux2, List.SublistForall₂.brecOn, List.zipWith5, List.foldr_concat, List.zipWith3_same_right, List.Duplicate.brecOn, List.ofFn_get_eq_map, List.map_eq_map, List.map_prod_left_eq_zip, List.nil_sigma, List.nodup_bind, List.argmax_cons, List.argmax_eq_none, List.foldr_join, List.modifyLast_append, List.bind_append_perm, List.map_permutations', List.mem_argmin_iff, List.zipWith_same, List.permutationsAux2, List.modifyHead_modifyHead, List.scanr_cons, List.argmin_eq_none, List.mem_argmax_iff, List.mapDiagM', List.permutationsAux2_snd_eq, List.length_bind', List.zipWith_rotate_one, List.length_scanl, List.permutationsAux2_append, List.permutationsAux2_snd_nil, List.map_append_bind_perm, List.map_map_permutations'Aux, List.zipWith4, List.argmax, List.count_bind', List.map_prod_right_eq_zip, List.comp_map, List.getElem?_scanl_zero, List.map_eq_map_iff, List.zipWith3_same_mid, List.zipWith3, List.sublistsLenAux_zero, List.argmax_eq_some_iff, List.bind_ret_eq_map, List.foldrM_eq_foldr, List.map_permutationsAux, List.argmin_eq_some_iff, List.argmax_concat, List.sigma_cons, Cycle.map_coe, List.foldl_concat, List.permutationsAux2_fst]

Link to cluster 6 with score 2656916.
Its hyp-names [List.length, Fin, Sigma, Iff, Ne, Membership.mem, List, List.instMembership, List.Nodup, LeanGrowLabel.pi]
Its thms [List.Nodup.getEquivOfForallMemList_apply, List.Nodup.getBijectionOfForallMemList_coe, List.mem_ext, List.Nodup.getEquivOfForallMemList, List.Nodup.getEquivOfForallMemList_symm_apply_val, List.Nodup.pairwise_of_forall_ne, List.Nodup.getBijectionOfForallMemList]

Link to cluster 5 with score 3860377.
Its hyp-names [Option.none, Option, Not, Bool, Bool.true, List.Nodup, Prime, MulZeroOneClass.toMulZeroClass, MulZeroClass.toMul, MonoidWithZero.toMulZeroOneClass, MonoidWithZero.toMonoid, Monoid.toOne, List.prod, CommMonoidWithZero.toMonoidWithZero, CancelCommMonoidWithZero.toCommMonoidWithZero, List.Disjoint, Nat, List.length, instHAppendOfAppend, Or, List.permutationsAux, List.nil, List.instAppend, List.Perm, HAppend.hAppend, Exists, Membership.mem, List, List.instMembership, List.getLast, List.cons, List.cons_ne_nil, List.Chain, LeanGrowLabel.pi, Eq]
Its thms [List.lookmap_of_forall_not, List.filterMap_congr, List.lookmap_congr, List.splitOnP_eq_single, List.splitOnP_first, List.Nodup.map_on, List.Nodup.pmap, perm_of_prod_eq_prod, List.foldl_ext, List.bind_congr, List.disjoint_pmap, List.length_foldr_permutationsAux2', List.mem_permutations_of_perm_lemma, List.foldr_ext, List.map_congr, List.pmap_congr, List.Chain.induction]

Link to cluster 7 with score 2427389.
Its hyp-names [Ne, Not, LeanGrowLabel.sort, Membership.mem, List, List.nil, List.instMembership, LeanGrowLabel.pi]
Its thms [List.splitOn_intercalate, List.getLast_pmap, List.foldlRecOn_nil, List.chain'_join, List.foldrRecOn_nil]

Link to cluster 12 with score 2093772.
Its hyp-names [List, List.cons, LeanGrowLabel.pi, Cycle, Cycle.ofList, Cycle.nil]
Its thms [Cycle.induction_on]

Link to cluster 10 with score 7663726.
Its hyp-names [Array, PUnit, List.ofFn, Fin, instLENat, LE.le, List.length, Eq, Nat, List, LeanGrowLabel.pi]
Its thms [List.mapIdxGo_length, List.mapIdxGo_append, List.mapIdxMAux'_eq_mapIdxMGo, List.mapIdxMGo_eq_mapIdxMAuxSpec, List.mapIdxM', List.mapIdxM'_eq_mapIdxM, List.mapIdxMAux', List.modifyNth_eq_set, List.oldMapIdxCore, List.mapIdxM_eq_mmap_enum, List.length_modifyNth, List.map_enumFrom_eq_zipWith, List.sublistsLenAux_eq, List.modifyNthTail_modifyNthTail_same, List.iterateTR.loop, List.oldMapIdxCore_eq, List.mapIdxMAuxSpec_cons, List.oldMapIdx, List.ofFnRec, List.getD_map, List.sym_map, List.foldrIdxSpec, List.get?_zip_with, List.modifyNthTail_modifyNthTail_le, List.foldlIdx_eq_foldlIdxSpec, List.mapIdx_eq_enum_map, List.get?_succ_scanl, List.oldMapIdxCore_append, List.getElem?_zip_with, List.mapIdx_eq_ofFn, List.sublistsLenAux_append, List.foldlIdxM, List.foldlIdxSpec_cons, List.foldlIdx_eq_foldl_enum, List.modifyNthTail_modifyNthTail, List.mapIdx_cons, List.foldrIdx_eq_foldrIdxSpec, List.foldrIdxSpec_cons, List.mapAsyncChunked, List.sublistsLenAux, List.iterateTR_loop_eq, List.oldMapIdx_append, List.new_def_eq_old_def, List.enumFrom_map, List.length_mapIdx, List.map_rotate, List.foldrIdxM, List.foldrIdxM_eq_foldrM_enum, List.mapIdx_eq_nil, List.mapIdxMAuxSpec, List.get?_zip_with_eq_some, List.mapIdx_append_one, List.foldrIdx_eq_foldr_enum, List.foldlIdxSpec, List.foldlIdxM_eq_foldlM_enum, List.getElem?_zip_with_eq_some, List.length_modifyNthTail, List.mapIdx_append]

Link to cluster 9 with score 2342855.
Its hyp-names [Eq, flip, Subtype.val, Option, Option.instMembership, Membership.mem, List, List.head?, List.Chain', LeanGrowLabel.sort, LeanGrowLabel.pi, Acc]
Its thms [List.lookmap_id', List.lookmap_map_eq, Acc.list_chain']

Link to cluster 11 with score 6624914.
Its hyp-names [List.Lex, List.Palindrome, List.SublistForall₂, Ne, List.nil, List, LeanGrowLabel.sort, LeanGrowLabel.pi]
Its thms [List.Lex.below.rel, List.Lex.below.nil, List.Palindrome.below.singleton, List.Palindrome.below.nil, List.Chain'.iff_mem, List.chain'_cons, List.SublistForall₂.below.nil, List.forall₂_cons_left_iff, List.forall₂_map_left_iff, List.exists_mem_cons_iff, List.forall₂_nil_left_iff, List.chain'_split, List.sublistForall₂_iff, List.forall₂_cons_right_iff, List.forall₂_iff_nthLe, List.chain'_append_cons_cons, List.Chain.iff_mem, List.forall₂_nil_right_iff, List.chain'_append, List.forall₂_and_left, List.chain_append_singleton_iff_forall₂, Cycle.chain_coe_cons, List.forall_iff_forall_mem, List.chain'_iff_get, List.forall_mem_union, List.forall_map_iff, List.chain_iff_forall₂, List.pairwise_iff_nthLe, List.chain_iff_get, List.forall_cons, List.Lex.nil_left_or_eq_nil, List.Forall, List.forall₂_reverse_iff, List.Sorted, List.forall_iff_forall_tuple, List.forall₂_iff_get, List.forall₂_map_right_iff, List.chain'_reverse, List.forall₂_same, List.forall₂_iff, List.exists_iff_exists_tuple, List.Lex.nil, List.pairwise_iff, List.chain'_map, List.chain_map, List.forall₂_iff_zip, List.chain_append_cons_cons, List.sigma_nil, List.chain'_cons', List.chain_split, List.sorted_cons, List.chain_iff, Cycle.chain_ne_nil, List.Lex.not_nil_right, List.SublistForall₂.nil, List.pairwise_map']

Link to cluster 14 with score 2160671.
Its hyp-names [List.getLast?, Option, Option.instMembership, Membership.mem, List, List.head?]
Its thms [List.getLast?_append, List.head?_append]

Link to cluster 13 with score 2918044.
Its hyp-names [instHAppendOfAppend, List.instAppend, HAppend.hAppend, List, List.nil, List.cons, LeanGrowLabel.pi]
Its thms [List.reverseRecOn, List.bidirectionalRec_nil, List.bidirectionalRec_singleton, List.bidirectionalRec, List.bidirectionalRecOn, List.list_reverse_induction, List.reverseRecOn_concat, List.reverseRecOn_nil, List.bidirectionalRec_cons_append, List.permutationsAux.rec]

Link to cluster 15 with score 7280280.
Its hyp-names [Exists, And, List.argmin, Transitive, List.foldl, List.argAux, Irreflexive, Option, Option.instMembership, List.argmax, Subtype, List.length, List.attach, Fin, instBEqOfDecidableEq, List.instInterOfBEq_batteries, Inter.inter, List.filter, List.takeWhile, List.permutationsAux, List.Chain, List.dropSlice, List.permutations, List.sections, List.rtakeWhile, Sym, Sym.instMembership, List.sym, List.IsSuffix, List.instHasSubset_batteries, HasSubset.Subset, List.sublistsLen, List.cyclicPermutations, List.dedup, List.dropLast, Symmetric, Ne, List.Pairwise, LeanGrowLabel.sort, Membership.mem, List, List.tail, List.instMembership]
Its thms [List.exists_mem_cons_of_exists, List.choose_mem, List.choose_property, List.choose_spec, List.chooseX, List.choose, List.not_lt_of_mem_argmin, List.not_of_mem_foldl_argAux, List.not_lt_of_mem_argmax, List.count_attach, List.mem_attach, List.get_attach, List.mem_of_mem_inter_right, List.mem_of_mem_inter_left, List.of_mem_filter, List.mem_of_mem_filter, List.mem_union_right, List.next, List.Duplicate.cons_mem, List.length_erase_add_one, List.indexOf_inj, List.mem_takeWhile_imp, List.sublist_join, List.perm_of_mem_permutationsAux, List.nthLe_of_mem, List.cons_bagInter_of_pos, List.mk_mem_sym2, List.Chain.rel, List.mem_of_mem_dropSlice, List.prev_mem, List.getElem?_indexOf, List.prev, List.perm_of_mem_permutations, List.mem_sections_length, List.not_lt_maximum_of_mem', List.mem_rtakeWhile_imp, List.mem_of_mem_of_mem_sym, List.nextOr_mem, List.mem_union_left, List.dedup_cons_of_mem, List.insert_pos, List.mem_of_mem_suffix, List.cons_subset_of_subset_of_mem, List.inter_cons_of_mem, List.length_of_sublistsLen, List.not_lt_minimum_of_mem', List.length_mem_cyclicPermutations, List.next_mem, List.indexOf_append_of_mem, List.sizeOf_lt_sizeOf_of_mem, List.Mem.duplicate_cons_self, List.dedup_cons_of_mem', List.not_nodup_cons_of_mem, List.mem_of_mem_dropLast, List.le_maximum_of_mem', List.mem_split, List.mem_inter_of_mem_of_mem, List.indexOf_get?, List.Pairwise.forall, List.tfae_cons_of_mem, List.minimum_le_of_mem', List.mem_of_mem_tail]

Link to cluster 24 with score 2192923.
Its hyp-names [instDistribLatticeOfLinearOrder, SemilatticeInf.toPartialOrder, Preorder.toLE, PartialOrder.toPreorder, Membership.mem, List, List.instMembership, Lattice.toSemilatticeInf, LE.le, DistribLattice.toLattice]
Its thms [List.min_le_of_le, List.le_max_of_le]

Link to cluster 20 with score 3023754.
Its hyp-names [List.IsRotated, List.attach, Subtype, setOf, Set.Pairwise, Membership.mem, List, List.map, List.instMembership, List.Nodup, Eq]
Its thms [List.isRotated_prev_eq, List.isRotated_next_eq, List.Nodup.of_attach, List.Nodup.getEquiv_symm_apply_val, List.prev_next, List.count_eq_one_of_mem, List.prev_reverse_eq_next, List.Nodup.pairwise_of_set_pairwise, List.next_reverse_eq_prev, List.next_prev, List.inj_on_of_nodup_map]

Link to cluster 18 with score 2929812.
Its hyp-names [List.getLast, List.cons_ne_nil, Ne, List.nil, Exists, And, List.Sorted, Membership.mem, List, List.instMembership, List.cons]
Its thms [List.prev_cons_cons_of_ne, List.next_ne_head_ne_getLast, List.prev_ne_cons_cons, List.prev_singleton, List.next_singleton, List.prev_cons_cons_eq, List.next_cons_cons_eq, List.or_exists_of_exists_mem_cons, List.rel_of_sorted_cons, List.prev_getLast_cons]

Link to cluster 17 with score 2349013.
Its hyp-names [Sigma, Option, Option.instMembership, Not, Membership.mem, List, List.kunion, List.keys, List.instMembership, List.dlookup]
Its thms [List.dlookup_kunion_right, List.kerase_append_right, List.kerase_of_not_mem_keys, List.mem_dlookup_kunion_middle]

Link to cluster 19 with score 2580575.
Its hyp-names [List.getLast, List.cons_ne_nil, List.Nodup, Ne, Membership.mem, List, List.instMembership, List.cons, Eq]
Its thms [List.next_getLast_cons, List.prev_cons_cons_of_ne', List.prev_cons_cons_eq', List.next_cons_cons_eq', List.prev_getLast_cons']

Link to cluster 22 with score 2607331.
Its hyp-names [Prod.mk, List.enumFrom, Prod, Nat, Membership.mem, List, List.instMembership, List.enum]
Its thms [List.snd_mem_of_mem_enumFrom, List.le_fst_of_mem_enumFrom, List.fst_lt_add_of_mem_enumFrom, List.mem_enumFrom, List.snd_mem_of_mem_enum, List.fst_lt_of_mem_enum]

Link to cluster 21 with score 2216011.
Its hyp-names [List.ranges, instOfNatNat, instHAdd, instAddNat, Sym, Sym.cons, OfNat.ofNat, Nat, Nat.succ, Membership.mem, List, List.sym, List.instMembership, HAdd.hAdd]
Its thms [List.ranges_nodup, List.first_mem_of_cons_mem_sym]

Link to cluster 23 with score 2329316.
Its hyp-names [instOfNatNat, OfNat.ofNat, instLTNat, Subtype, Nat, Membership.mem, List, List.length, List.instMembership, List.attach, LT.lt]
Its thms [List.minimum_of_length_pos_le_of_mem, List.le_maximum_of_length_pos_of_mem, List.getElem_attach]

Link to cluster 28 with score 2343131.
Its hyp-names [List.sublists, List.sublists', List.revzip, List.Forall₂, Prod, Prod.mk, Membership.mem, List, List.zip, List.instMembership]
Its thms [List.revzip_sublists, List.revzip_sublists', List.forall₂_zip, List.mem_zip]

Link to cluster 26 with score 2382035.
Its hyp-names [Preorder.toLE, LE.le, List.argmin, instDistribLatticeOfLinearOrder, instDecidableLt_mathlib, SemilatticeInf.toPartialOrder, PartialOrder.toPreorder, Option, Option.instMembership, Membership.mem, List, List.instMembership, List.argmax, Lattice.toSemilatticeInf, DistribLattice.toLattice]
Its thms [List.index_of_argmin, List.index_of_argmax, List.le_of_mem_argmin, List.le_of_mem_argmax]

Link to cluster 25 with score 2271082.
Its hyp-names [WithBot, WithBot.some, List.maximum, instDistribLatticeOfLinearOrder, instDecidableLt_mathlib, WithTop, WithTop.some, SemilatticeInf.toPartialOrder, PartialOrder.toPreorder, Membership.mem, List, List.minimum, List.instMembership, Lattice.toSemilatticeInf, Eq, DistribLattice.toLattice]
Its thms [List.le_maximum_of_mem, List.minimum_le_of_mem]

Link to cluster 27 with score 2160511.
Its hyp-names [Sym2, Sym2.mk, Prod.mk, Membership.mem, List, List.sym2, List.instMembership]
Its thms [List.left_mem_of_mk_mem_sym2, List.right_mem_of_mk_mem_sym2]

Link to cluster 30 with score 2260407.
Its hyp-names [Subtype, LT.lt, Preorder.toLT, Membership.mem, List, List.instMembership, List.Sorted, GT.gt]
Its thms [List.Sorted.coe_getIso_symm_apply, List.Sorted.head!_le, List.Sorted.le_head!]

Link to cluster 29 with score 2164346.
Its hyp-names [List.take, List.drop, Membership.mem, List, List.instMembership, List.Sorted]
Its thms [List.Sorted.rel_of_mem_take_of_mem_drop, List.orderedInsert_erase]

Link to cluster 31 with score 2421204.
Its hyp-names [Sigma, Membership.mem, List, List.keys, List.kerase, List.instMembership]
Its thms [List.dlookup_kunion_left, List.kerase_append_left, List.exists_of_kerase, List.exists_of_mem_keys, List.mem_keys_of_mem_keys_kerase]

Link to cluster 48 with score 2564628.
Its hyp-names [List.cons, Prod, Prod.mk, List, List.split, Eq]
Its thms [List.mergeSort_cons_cons, List.length_split_lt, List.split_cons_of_eq, List.length_split_le, List.perm_split]

Link to cluster 40 with score 2496548.
Its hyp-names [suffixLevenshtein, instHAppendOfAppend, Subtype, Prod, Prod.mk, OrderedAddCommMonoid.toAddCommMonoid, List.reverse, List.nil, List.minimum_of_length_pos, List.instAppend, LinearOrderedAddCommMonoid.toLinearOrder, LevenshteinEstimator'.match_1, HAppend.hAppend, CanonicallyOrderedAddCommMonoid.toOrderedAddCommMonoid, CanonicallyLinearOrderedAddCommMonoid.toMin, CanonicallyLinearOrderedAddCommMonoid.toLinearOrderedAddCommMonoid, CanonicallyLinearOrderedAddCommMonoid.toCanonicallyOrderedAddCommMonoid, AddMonoid.toAddZeroClass, AddCommMonoid.toAddMonoid, instOfNatNat, instLTNat, Subtype.val, Subtype.property, OfNat.ofNat, Nat, List, List.tail, List.length, List.instGetElemNatLtLength, LT.lt, GetElem.getElem, Eq]
Its thms [LevenshteinEstimator'.mk, LevenshteinEstimator'.mk.injEq, LevenshteinEstimator'.mk.sizeOf_spec, suffixLevenshtein_cons₁_aux]

Link to cluster 36 with score 3324999.
Its hyp-names [List.permutations'Aux, List.inits, List.tails, instLENat, instHAppendOfAppend, List.instAppend, LE.le, HAppend.hAppend, Option, instLTNat, Nat, List, List.length, List.cyclicPermutations, LT.lt]
Its thms [List.getElem_permutations'Aux, List.get_permutations'Aux, List.nthLe_permutations'Aux, List.nth_le_inits, List.getElem_inits, List.getElem_tails, List.nth_le_tails, List.nthLe_append_right, List.getD_append, List.prefix_take_le_iff, List.drop_take_succ_join_eq_getElem', List.getI_append, List.getElem_cyclicPermutations]

Link to cluster 34 with score 11080411.
Its hyp-names [Prod, instSubNat, instOfNatNat, instLTNat, instHSub, OfNat.ofNat, Ne, List.ofFn, List.nil, LT.lt, HSub.hSub, instLENat, LE.le, Array, Nat, List]
Its thms [List.get?_zip_eq_some, List.mem_enum_iff_get?, List.getElem?_zip_eq_some, List.perm_replicate_append_replicate, List.last_ofFn, List.length_le_length_insertNth, List.sublist_replicate_iff, List.rotate_rotate, List.nil_eq_rotate_iff, List.ranges_disjoint, List.sym, List.mem_sublistsLen, List.sublistsLen_succ_cons, List.get?_enum, List.ranges_join', List.mk_mem_enum_iff_get?, List.enumFrom_map_snd, List.map_fst_add_enum_eq_enumFrom, List.map_fst_add_enumFrom_eq_enumFrom, List.enumFrom_eq_zip_range', List.get?_enumFrom, List.getD_eq_getD_get?, List.getI_eq_iget_get?, List.rotate_eq_drop_append_take_mod, List.mk_add_mem_enumFrom_iff_get?, List.rotate'_cons_succ, List.rdrop_eq_reverse_drop_reverse, List.sublistsLen, List.getI_cons_succ, List.rotate_cons_succ, List.getElem?_enumFrom, List.prefix_take_iff, List.enum_get?, List.rotate_eq_singleton_iff, List.mem_mem_ranges_iff_lt_natSum, List.rotate'_length_mul, List.rdrop_concat_succ, List.takeI, List.cyclicPermutations_rotate, List.drop_sum_join', List.rotate_eq_iff, List.dropSlice_sublist, List.eraseIdx_insertNth, List.rtake, List.rotate_eq_rotate', List.take_sum_join', List.removeNth_eq_nthTail, List.splitAt_eq_take_drop, List.rotate_eq_rotate, List.length_insertNth_le_succ, List.length_rotate, List.getD_default_eq_getI, List.takeD_length, List.rotate_mod, List.mem_rotate, List.getElem?_enum, List.rdrop_add, List.drop_sublist_drop_left, List.sym_sublist_sym_cons, List.length_sublistsLen, List.enumFrom_cons', List.sublistsLen_sublist_sublists', List.IsRotated.forall, List.getI, List.enumFrom_append, List.rtake_concat_succ, List.rotate_perm, List.drop_tail, List.dropSlice_subset, List.ranges, List.reverse_rotate, List.insertNth_succ_cons, List.length_rotate', List.splitAt_eq_take_drop.go_eq_take_drop, List.rotate_length_mul, List.rdrop_append_length_add, List.enumFrom_eq_nil, List.rtake_eq_reverse_take_reverse, List.rdrop, List.ranges_length, List.singleton_eq_rotate_iff, List.rotate'_rotate', List.rotate_reverse, List.removeNth_insertNth, List.length_sym, List.unzip_enumFrom_eq_prod, List.rotate_eq_nil_iff, List.nodup_rotate, List.take_cons, List.dropSlice_eq, List.enumFrom_get?, List.mk_mem_enumFrom_iff_le_and_get?_sub, List.rotate'_mod, List.takeI_length]

Link to cluster 33 with score 2255170.
Its hyp-names [Sigma.mk, List.NodupKeys, Sigma, Membership.mem, List, List.instMembership]
Its thms [List.kreplace_self, List.mem_dlookup, List.mem_keys_of_mem]

Link to cluster 35 with score 2580176.
Its hyp-names [instLENat, LE.le, Nat, List, List.length, Eq]
Its thms [List.rdrop_append_of_le_length, List.getD_append_right, List.getI_append_right, List.takeD_left', List.takeI_left']

Link to cluster 38 with score 2241538.
Its hyp-names [Subtype.mk, Levenshtein.impl, suffixLevenshtein, instOfNatNat, instLTNat, Subtype.val, OfNat.ofNat, Nat, List, List.length, List.cons, LT.lt]
Its thms [Levenshtein.impl_cons_fst_zero, suffixLevenshtein_cons_cons_fst_get_zero]

Link to cluster 37 with score 2437341.
Its hyp-names [Subtype, List.cons, Levenshtein.Cost, List.permutations'Aux, instOfNatNat, instLTNat, OfNat.ofNat, Ne, Nat, List, List.reverse, List.nil, List.length, LT.lt]
Its thms [Levenshtein.impl, Levenshtein.impl_cons, List.permutations'Aux_get_zero, List.getLast_reverse]

Link to cluster 39 with score 2160344.
Its hyp-names [instOfNatNat, instLTNat, instHAdd, instAddNat, Subtype.val, OfNat.ofNat, Nat, List, List.length, Levenshtein.Cost, LT.lt, HAdd.hAdd, Eq]
Its thms [Levenshtein.impl_length]

Link to cluster 44 with score 4885140.
Its hyp-names [List.rotate, List.Nodup, Eq, List.IsPrefix, instHAppendOfAppend, List.instAppend, List.Chain', HAppend.hAppend, Nat.succ, List.ofFn, Preorder.toLT, List.LT', LT.lt, List.rdropWhile, List.replicate, Ne, List, List.nil]
Its thms [List.Nodup.rotate_congr, List.getLast_congr, List.IsPrefix.head_eq, List.IsPrefix.ne_nil, List.length_pos_of_ne_nil, List.head!_append, List.getLast?_eq_getLast_of_ne_nil, List.getLast_append', List.head?_append_of_ne_nil, List.foldr_min_of_ne_nil, List.length_cyclicPermutations_of_ne_nil, List.getLast?_append_of_ne_nil, List.Chain'.append_overlap, List.head_cons_tail, List.foldr_max_of_ne_nil, List.cons_head!_tail, List.cyclicPermutations_of_ne_nil, List.tail_append_of_ne_nil, List.minimum_ne_top_of_ne_nil, List.last_ofFn_succ, List.head!_mem_self, List.head_mem, List.head!_le_of_lt, List.getLast_cons, List.rdropWhile_last_not, List.head!_mem_head?, List.splitOnP_spec.join_zipWith, List.head_replicate, List.tail_append_singleton_of_ne_nil, List.dropLast_append_getLast, List.join_drop_length_sub_one, List.maximum_ne_bot_of_ne_nil]

Link to cluster 42 with score 2506885.
Its hyp-names [Sigma.fst, Sigma, Ne, List]
Its thms [List.kerase_cons_ne, List.dlookup_cons_ne, List.lookupAll_cons_ne, List.dlookup_kinsert_ne, List.dlookup_kerase_ne, List.mem_keys_kerase_of_ne]

Link to cluster 41 with score 6977091.
Its hyp-names [List.instHasSubset_batteries, HasSubset.Subset, AList.entries, List.NodupKeys, List.Perm, Sigma.fst, Eq, Sigma, List]
Its thms [AList.ext, AList.keys_subset_keys_of_entries_subset_entries, List.Perm.kunion_left, List.Perm.kunion_right, List.mem_lookupAll, List.kinsert_def, List.keys_cons, List.dlookup_dedupKeys, List.kerase, List.dlookup, List.kinsert, List.kreplace_nodupKeys, List.keys, List.kunion_kerase, List.kerase_keys_subset, List.lookupAll_eq_nil, List.lookupAll, List.sizeOf_kerase, List.sizeOf_dedupKeys, List.kunion_nil, List.not_eq_key, List.kerase_kerase, List.NodupKeys, List.dlookup_eq_none, List.kerase_comm, List.kunion_cons, List.nodupKeys_join, List.toAList, List.head?_lookupAll, List.nodupKeys_iff_pairwise, List.lookupAll_cons_eq, AList.lookup_to_alist, List.keys_kerase, List.dlookup_cons_eq, List.kerase_sublist, List.dlookup_kunion_eq_some, List.mem_keys, List.dlookup_isSome, List.kunion, List.mem_dlookup_kunion, AList.toAList_cons, List.lookupAll_sublist, List.mem_keys_kunion, List.dlookup_kinsert, List.kreplace, List.map_dlookup_eq_find, List.kextract_eq_dlookup_kerase, List.keys_kreplace, List.kerase_cons_eq, List.nodupKeys_cons, AList.entries_toAList, List.not_mem_keys, List.mem_keys_kinsert, List.nil_kunion, List.dedupKeys_cons, List.kextract, List.nodupKeys_dedupKeys, List.dedupKeys]

Link to cluster 43 with score 2224804.
Its hyp-names [Ne, List]
Its thms [List.nextOr_cons_of_ne, List.indexOf_cons_ne, List.duplicate_cons_iff_of_ne]

Link to cluster 46 with score 2770637.
Its hyp-names [Not, rfl, List.nil, List.getLast, List.filter, Eq.symm, Eq.rec, List, Eq, Bool, Bool.true]
Its thms [List.rtakeWhile_concat_neg, List.rdropWhile_concat_neg, List.takeWhile_cons_of_neg, List.getLast_filter, List.rtakeWhile_concat_pos, List.takeWhile_cons_of_pos, List.rdropWhile_concat_pos]

Link to cluster 45 with score 2660995.
Its hyp-names [instHAppendOfAppend, List.instAppend, HAppend.hAppend, Option.none, Option, Option.some, List.reverse, List, Eq]
Its thms [List.append_left_cancel, List.append_right_cancel, List.lookmap_cons_none, List.lookmap_cons_some, List.Palindrome.of_reverse_eq, List.indexOf_cons_eq]

Link to cluster 47 with score 2143291.
Its hyp-names [Prod, Prod.snd, Prod.fst, List, List.map, Eq]
Its thms [List.zip_of_prod]

Link to cluster 64 with score 2528862.
Its hyp-names [LeanGrowLabel.sort, LeanGrowLabel.pi, instOfNatNat, instHAdd, instAddNat, OfNat.ofNat, HAdd.hAdd, Nat, List.length, Eq]
Its thms [List.zipWith_rotate_distrib, List.forall_zipWith, List.zipWith_distrib_reverse, List.exists_of_length_succ, List.unzip_zip, List.nthLe_cons_length]

Link to cluster 54 with score 4671053.
Its hyp-names [Option, List.get?, Eq, List.Nodup, List.zipWith, List.finRange, Fin, List.IsPrefix, List.insertNth, List.pmap, List.Forall₂, instBEqOfDecidableEq, List.indexOf, List.map, List.ofFn.go, List.ofFn, List.rotate, Ne, List.set, List.cons, List.Sorted, List.range, List.iterate, List.range', instHAdd, instAddNat, List.reverseAux, HAdd.hAdd, List.mapIdx, instLTNat, Nat, List.length, LT.lt]
Its thms [List.next_nthLe, List.get?_injective, List.prev_nthLe, List.Nodup.erase_getElem, List.Nodup.nthLe_inj_iff, List.indexOf_getElem, List.Nodup.getElem_inj_iff, List.lt_length_right_of_zipWith, List.lt_length_left_of_zipWith, List.nthLe_zipWith, List.getElem_zipWith, List.get_finRange, List.getElem_finRange, List.nthLe_finRange, List.IsPrefix.getElem, List.concat_get_prefix, List.IsPrefix.get_eq, List.nthLe_insertNth_of_lt, List.get_insertNth_of_lt, List.getElem_insertNth_of_lt, List.nthLe_pmap, List.getElem_pmap, List.get_pmap, List.Forall₂.nthLe, List.Forall₂.get, List.getElem_indexOf, List.indexOf_get, List.nthLe_map', List.nthLe_map, List.getElem_ofFn_go, List.get_ofFn_go, List.nthLe_ofFn', List.getElem_ofFn, List.getElem_rotate, List.nthLe_rotate, List.getElem_set_of_ne, List.get_set_of_ne, List.getD_eq_get, List.getI_eq_get, List.getElem?_rotate, List.nthLe_get?, List.nthLe, List.nthLe_cons, List.take_one_drop_eq_of_lt_length, List.nthLe_rotate', List.Sorted.rel_nthLe_of_lt, List.insertNth_of_length_lt, List.nthLe_range, List.toFinsupp_apply_lt', List.getElem_iterate, List.cons_getElem_drop_succ, List.getElem_eq_getElem?, List.length_eraseIdx_add_one, List.get?_rotate, List.nthLe_range', List.sublistsLen_of_length_lt, List.toFinsupp_apply_lt, List.drop_take_succ_eq_cons_getElem, List.get_reverse_aux₁, List.nthLe_mem, List.nthLe_mapIdx, List.drop_take_succ_eq_cons_nthLe, List.head?_rotate]

Link to cluster 50 with score 2321187.
Its hyp-names [List.Chain', instHAppendOfAppend, List, List.instAppend, List.Forall₂, HAppend.hAppend]
Its thms [List.Chain'.left_of_append, List.Chain'.right_of_append, List.forall₂_take_append, List.forall₂_drop_append]

Link to cluster 49 with score 2925477.
Its hyp-names [instHAppendOfAppend, List.instAppend, HAppend.hAppend, List.instHasSubset_batteries, HasSubset.Subset, List.sublists, List, List.sublists', List.Nodup]
Its thms [List.Nodup.of_append_right, List.disjoint_of_nodup_append, List.Nodup.of_append_left, List.Nodup.subperm, List.Nodup.mem_diff_iff, List.Nodup.union, List.nodup.of_sublists, List.Nodup.diff_eq_filter, List.Nodup.diff, List.Nodup.inter, List.nodup.of_sublists']

Link to cluster 51 with score 2223070.
Its hyp-names [Commutative, List, Associative]
Its thms [List.foldl_eq_of_comm_of_assoc, List.foldl_eq_foldr, List.foldl1_eq_foldr1]

Link to cluster 52 with score 4995631.
Its hyp-names [instLENat, LE.le, LeanGrowLabel.sort, List.Sublist, List.Chain', List.Forall₂, instOfNatNat, OfNat.ofNat, Ne, Prod, Nat]
Its thms [List.Ico.map_sub, List.Ico.append_consecutive, List.Ico.filter_lt_of_ge, List.Ico.filter_lt_of_top_le, List.Ico.filter_le_of_le, List.Ico.succ_top, List.Ico.filter_le_of_le_bot, List.Ico.filter_lt_of_le_bot, List.Ico.filter_le_of_top_le, List.rtake_nil, List.rotate_nil, List.rdrop_nil, List.ofFn_injective, List.rotate'_nil, List.replicate_right_injective, List.sublistsLen_succ_nil, List.rotate_injective, List.Sublist.drop, List.sublistsLen_sublist_of_sublist, List.Sublist.sym, List.Chain'.drop, List.Chain'.take, List.forall₂_take, List.forall₂_drop, List.replicate_dedup, List.replicate_right_inj, List.Nat.antidiagonal_succ_succ', List.Ico.zero_bot, List.finRange_succ, List.Nat.antidiagonal_succ', List.ofFn_const, List.getElem?_getD_singleton_default_eq, List.nodup_replicate, List.Nat.nodup_antidiagonal, List.nodup_range, List.enumFrom_singleton, List.Ico.inter_consecutive, List.replicate_right_inj', List.Nat.mem_antidiagonal, List.rotate_replicate, List.finRange_succ_eq_map, List.pairwise_le_range, List.Ico.chain'_succ, List.getD_replicate_default_eq, List.toFinsupp_cons_apply_succ, List.Ico.filter_le, List.Ico.succ_singleton, List.ofFn_id, List.Nat.antidiagonal_succ, List.Ico.bagInter_consecutive, List.getI_nil, List.finRange_eq_nil, List.insertNth_injective, List.insertNth_succ_nil, List.pairwise_lt_finRange, List.Ico.length, List.Ico.self_empty, List.Ico.not_mem_top, List.getLast_replicate_succ, List.length_finRange, List.take_range, List.map_coe_finRange, List.range'_one, List.Nat.length_antidiagonal, List.pairwise_le_finRange, List.toFinsupp_apply, List.Ico, List.tail_replicate, List.pairwise_gt_iota, List.Ico.filter_lt, List.takeI_nil, List.Ico.map_add, List.Ico.nodup, List.replicate_add, List.Nat.antidiagonal, List.Ico.mem, List.rotate_singleton, List.nodup_iota, List.replicate_left_inj, List.getElem?_getD_replicate_default_eq, List.replicate_succ', List.finRange, List.nodup_finRange, List.pairwise_lt_range, List.getD_singleton_default_eq, List.Ico.trichotomy, List.replicate_subset_singleton, List.Ico.pairwise_lt, List.Nat.map_swap_antidiagonal]

Link to cluster 58 with score 2140195.
Its hyp-names [List.insertNth, instLTNat, instLENat, Nat, List.length, List.Sorted, LT.lt, LE.le]
Its thms [List.nthLe_insertNth_self, List.get_insertNth_self, List.getElem_insertNth_self, List.insertNth_removeNth_of_ge, List.insertNth_eraseIdx_of_ge, List.insertNth_removeNth_of_le, List.insertNth_eraseIdx_of_le, List.Sorted.rel_nthLe_of_le]

Link to cluster 56 with score 2127499.
Its hyp-names [Fin.val, List.reverse, List.reverseAux, instSubNat, instOfNatNat, instLTNat, instHSub, OfNat.ofNat, Nat, List.length, LT.lt, HSub.hSub]
Its thms [List.get_reverse, List.nthLe_reverse, List.getElem_reverse, List.get_reverse', List.nthLe_reverse', List.get_reverse_aux₂, List.getElem_reverse_aux₂, List.get_length_sub_one]

Link to cluster 55 with score 2794427.
Its hyp-names [List.scanl, List.dropWhile, List.rotate, List.range', instOfNatNat, instLTNat, OfNat.ofNat, Ne, Nat, List.length, List.cons, LT.lt]
Its thms [List.nthLe_zero_scanl, List.get_zero_scanl, List.getElem_scanl_zero, List.ne_nil_of_length_pos, List.getElem_le_maximum_of_length_pos, List.coe_minimum_of_length_pos, List.minimum_of_length_pos_mem, List.maximum_ne_bot_of_length_pos, List.dropWhile_nthLe_zero_not, List.maximum_of_length_pos_mem, List.minimum_ne_top_of_length_pos, List.coe_maximum_of_length_pos, List.sizeOf_dropSlice_lt, List.minimum_of_length_pos_le_iff, List.nthLe_rotate_one, List.maximum_of_length_pos, List.nthLe_range'_1, List.minimum_of_length_pos, List.minimum_of_length_pos_le_getElem, List.le_maximum_of_length_pos_iff, List.nthLe_cons_aux]

Link to cluster 57 with score 2047220.
Its hyp-names [List.insertNth, List.scanl, instOfNatNat, instLTNat, instHAdd, instAddNat, OfNat.ofNat, Nat, List.tail, List.length, LT.lt, HAdd.hAdd]
Its thms [List.nthLe_insertNth_add_succ, List.getElem_insertNth_add_succ, List.get_insertNth_add_succ, List.get_succ_scanl, List.nthLe_succ_scanl, List.nthLe_tail]

Link to cluster 60 with score 2480537.
Its hyp-names [instDistribLatticeNat, SemilatticeInf.toPartialOrder, PartialOrder.toPreorder, Not, List.get, Lattice.toSemilatticeInf, LT.lt.trans, Fin.mk, DistribLattice.toLattice, Bool, Bool.true, List.nthLe, instLTNat, Option, Nat, Nat.instMax, Max.max, List.length, List.get?, LeanGrowLabel.pi, LT.lt, Eq]
Its thms [List.forall₂_of_length_eq_of_get, List.le_findIdx_of_not, List.ext_nthLe, List.forall₂_of_length_eq_of_nthLe, List.ext_get?']

Link to cluster 59 with score 1915695.
Its hyp-names [Bool, instLTNat, Nat, List.length, LeanGrowLabel.pi, LT.lt]
Its thms [List.findIdx_eq, List.nthLe_map_rev, List.getElem_map_rev]

Link to cluster 62 with score 2365513.
Its hyp-names [instLENat, Nat, List.length, LE.le]
Its thms [List.takeD_eq_take, Decidable.List.Lex.ne_iff, List.getI_eq_default, List.mem_insertNth, List.toFinsupp_apply_le, List.rotate_eq_drop_append_take, List.getD_eq_default, List.unzip_zip_right, List.rotate'_eq_drop_append_take, List.takeI_eq_take, List.unzip_zip_left, List.Lex.ne_iff, List.length_insertNth, List.insertNth_comm]

Link to cluster 61 with score 2070395.
Its hyp-names [List.zip, List.enumFrom, instLTNat, Prod, Nat, List.length, List.enum, LT.lt]
Its thms [List.lt_length_right_of_zip, List.nthLe_zip, List.lt_length_left_of_zip, List.getElem_zip, List.getElem_enumFrom, List.getElem_enum]

Link to cluster 63 with score 2226729.
Its hyp-names [Option, instLENat, instDistribLatticeNat, SemilatticeInf.toPartialOrder, PartialOrder.toPreorder, Not, Nat, List.length, List.get, LeanGrowLabel.pi, Lattice.toSemilatticeInf, LE.le, LE.le.trans_lt, Fin.mk, Eq, DistribLattice.toLattice, Bool, Bool.true]
Its thms [List.map₂Left_eq_zipWith, List.map₂Right_eq_zipWith, List.lt_findIdx_of_not]

Link to cluster 77 with score 1488155.
Its hyp-names [Option, List.IsPrefix, LeanGrowLabel.pi]
Its thms [List.IsPrefix.filterMap, List.IsPrefix.filter_map, List.IsPrefix.map]

Link to cluster 72 with score 1859094.
Its hyp-names [Fin, Cycle, List.map, List.TFAE, List.getLastD, List.cons, List.Chain, LeanGrowLabel.sort, LeanGrowLabel.pi]
Its thms [List.pairwise_ofFn, List.forall_mem_ofFn_iff, List.sorted_ofFn_iff, Cycle.chain_map, Cycle.Chain, List.forall_tfae, List.exists_tfae, AList.instEmptyCollection, List.sorted_nil, List.rel_join, List.dlookup_nil, AList.keys_empty, List.chain'_singleton, List.chains, List.keys_nil, AList.not_mem_empty, AList.instMembership, List.kerase_nil, List.tfae_of_cycle, Cycle.Chain.nil, List.lookupAll_nil, List.chain_singleton, AList.lookup_empty, List.nodupKeys_nil, List.rel_append, List.forall₂_comp_perm_eq_perm_comp_forall₂, AList.instInhabited, List.rel_foldr, List.rel_foldl, List.chain'_pair, AList.instUnion, List.rel_sections, List.rel_reverse, Cycle.chain_singleton, List.rel_map, List.sorted_singleton, List.Lex.singleton_iff, List.rel_filterMap, List.rel_bind, List.chain'_nil, AList.empty_entries]

Link to cluster 67 with score 2522641.
Its hyp-names [Eq, instMulNat, instHMul, HMul.hMul, List.ofFn, instOfNatNat, OfNat.ofNat, instHAdd, instAddNat, HAdd.hAdd, Sigma, Nat, LeanGrowLabel.pi, Fin]
Its thms [List.length_ofFn_go, List.ofFn_congr, List.ofFn_mul, List.ofFn_mul', List.ofFnRec_ofFn, List.get?_ofFn, List.ofFn_zero, List.getElem?_ofFn, List.ofFn_add, List.ofFn_fin_repeat, List.equivSigmaTuple_symm_apply]

Link to cluster 66 with score 2741621.
Its hyp-names [LeanGrowLabel.sort, instLTNat, LT.lt, instLENat, RelEmbedding.instFunLike, OrderEmbedding, Option, List.get?, LE.le, Eq, DFunLike.coe, Nat, LeanGrowLabel.pi]
Its thms [List.chain'_range_succ, Cycle.chain_range_succ, List.chain_range_succ, List.get?_iterate, List.getElem?_iterate, List.range_map_iterate, List.iterate_eq_nil, Levenshtein.weightCost, Levenshtein.weightCost_substitute, List.length_iterate, List.mapIdx_nil, List.sublist_of_orderEmbedding_get?_eq, List.iterateTR, List.take_iterate, Levenshtein.weightCost_insert, Levenshtein.weightCost_delete, List.mem_iterate, List.iterate, List.iterate_add]

Link to cluster 65 with score 1933286.
Its hyp-names [List.enum, Prod, List.enumFrom, Nat, List.length, Fin]
Its thms [List.get_enum, List.get_enumFrom, List.get_eq_get_rotate]

Link to cluster 69 with score 1872092.
Its hyp-names [List.findIdx, instLTNat, Nat, LT.lt]
Its thms [List.Ico.filter_lt_of_succ_bot, List.not_of_lt_findIdx, List.Ico.filter_le_of_bot]

Link to cluster 68 with score 2158923.
Its hyp-names [List.Perm, Nat, List.Nodup]
Its thms [List.Perm.drop_inter, List.Perm.dropSlice_inter, List.Perm.take_inter, List.Nodup.sym, List.Nodup.rotate_congr_iff, List.nodup_sublistsLen, List.Nodup.take_eq_filter_mem, List.Nodup.rotate_eq_self_iff]

Link to cluster 71 with score 2236977.
Its hyp-names [Bool, List.Chain', List.map, List.pmap, List.getLast, List.cons, List.cons_ne_nil, List.Chain, Eq, Cycle, List.Nodup, List.Forall₂, List.Lex, List.Palindrome, List.Sublist, AList, Cycle.Chain, List.IsRotated, Option, List.Forall, LeanGrowLabel.pi]
Its thms [List.splitOnP_nil, List.rdropWhile_singleton, List.filter_singleton, List.Nodup.filter, List.rtakeWhile_nil, List.rdropWhile_nil, List.Chain'.imp, List.chain'_map_of_chain', List.Chain'.imp_head, List.chain'_of_chain'_map, List.chain_of_chain_map, List.chain_map_of_chain, List.chain_of_chain_pmap, List.Chain.induction_head, Cycle.map, Cycle.map_eq_nil, Cycle.mem_map, List.Nodup.map_update, List.nodup_map_iff_inj_on, List.Nodup.sigma, List.Forall₂.imp, List.Forall₂.mp, List.Lex.imp, List.argmin_nil, List.Palindrome.map, List.argmin_singleton, Levenshtein.Cost.mk.injEq, List.Sublist.map, List.map_involutive_iff, List.map_injective_iff, List.argmax_singleton, List.map_rightInverse_iff, List.scanr_nil, AList.foldl, List.map_leftInverse_iff, Cycle.Chain.imp, List.argmax_nil, List.scanl_nil, Cycle.map_nil, Levenshtein.Cost.mk.sizeOf_spec, List.IsRotated.map, List.lookmap_nil, Levenshtein.Cost.mk, List.map_comp_map, List.Forall.imp, List.map_bijective_iff, List.map_surjective_iff]

Link to cluster 70 with score 1908864.
Its hyp-names [_auto._@.Mathlib.Data.List.Range._hyg.51, autoParam, _auto._@.Mathlib.Data.List.Range._hyg.186, instOfNatNat, instLTNat, OfNat.ofNat, Nat, LT.lt]
Its thms [List.pairwise_lt_range', List.nodup_range', List.nthLe_singleton, List.Ico.pred_singleton]

Link to cluster 75 with score 2321217.
Its hyp-names [List.Nodup, List.Perm, List.Pairwise, Eq, And, List.getLast?, List.head?, List.Chain', Option, Option.instMembership, Membership.mem, List.dlookup, List.NodupKeys, LeanGrowLabel.pi, Iff]
Its thms [List.Nodup.filterMap, List.perm_lookmap, List.Chain'.append, List.Chain'.cons', List.lookup_ext]

Link to cluster 74 with score 1732735.
Its hyp-names [Sigma.fst, Not, EmptyCollection.emptyCollection, AList, AList.instMembership, AList.instEmptyCollection, AList.insert, Membership.mem, LeanGrowLabel.pi, Cycle, Cycle.instMembership]
Its thms [AList.insertRec_empty, AList.insertRec_insert_mk, AList.insertRec_insert, AList.insertRec, Cycle.chain_of_pairwise]

Link to cluster 73 with score 1750309.
Its hyp-names [Nat.succ, Equiv.Perm, List.length, LeanGrowLabel.pi, Fin]
Its thms [List.ofFn_succ', List.ofFn_succ, List.mem_ofFn, List.nodup_ofFn, List.length_ofFn, List.sorted_le_ofFn_iff, List.sorted_lt_ofFn_iff, List.ofFn_eq_pmap, List.ofFn_inj, List.ofFn_fin_append, List.nthLe_ofFn, List.map_ofFn, List.ofFn_eq_map, List.ofFn_eq_nil_iff, List.monotone_iff_ofFn_sorted, Equiv.Perm.ofFn_comp_perm, List.ofFn_inj', List.get_map_rev]

Link to cluster 76 with score 2134157.
Its hyp-names [Eq, Set, Set.range, Set.instHasSubset, LeanGrowLabel.pi, HasSubset.Subset]
Its thms [List.foldr_range_eq_of_range_eq, List.foldl_range_eq_of_range_eq, List.foldl_range_subset_of_range_subset, List.foldr_range_subset_of_range_subset]

Link to cluster 83 with score 1775613.
Its hyp-names [Cycle.reverse, Membership.mem, Cycle, Cycle.instMembership, Cycle.Nodup]
Its thms [Cycle.next_reverse_eq_prev', Cycle.prev_reverse_eq_next', Cycle.prev, Cycle.prev_reverse_eq_next, Cycle.next, Cycle.next_reverse_eq_prev, Cycle.prev_next, Cycle.next_prev, Cycle.prev_mem, Cycle.next_mem]

Link to cluster 80 with score 1838715.
Its hyp-names [Union.union, Option, Option.instMembership, AList.lookup, AList.instUnion, Not, Membership.mem, AList, AList.instMembership]
Its thms [AList.lookup_union_right, AList.mem_lookup_union_middle, AList.insert_of_neg, AList.insert_entries_of_neg, AList.lookup_union_left]

Link to cluster 78 with score 2163540.
Its hyp-names [autoParam, _auto._@.Mathlib.Data.List.TFAE._hyg.509, _auto._@.Mathlib.Data.List.TFAE._hyg.498, Option, Option.some, List.get?, List.TFAE, Relator.LiftFun, Iff, Eq, Bool, Bool.true, flip, List.Forall₂, LeanGrowLabel.sort]
Its thms [List.TFAE.out, List.rel_filter, List.reverse_bijective, List.instIsTransSubset, List.sublists_nil, List.reverse_surjective, List.instIsPartialOrderIsPrefix, List.perm_comp_perm, Cycle.nodup_nil, List.instSingletonList, Cycle.length_nil, List.instTransPerm_mathlib, List.instLawfulIdentityAppendNil_mathlib, List.cyclicPermutations_injective, Cycle.instMembership, List.sublistsAux_eq_bind, List.equivSigmaTuple, List.Palindrome.nil, List.instAssociativeAppend_mathlib, List.instSProd, Cycle.instInhabited, Cycle.subsingleton_nil, Cycle.coe_nil, List.IsRotated.setoid, List.permutations_nil, List.reduceOption_nil, Cycle, List.IsRotated.eqv, Cycle.instEmptyCollection, List.cyclicPermutations_nil, Cycle.chain_mono, List.surjective_head?, List.length_injective_iff, List.sublists'_nil, List.reverse_injective, List.instIsPartialOrderIsSuffix, Cycle.lists_nil, List.surjective_tail, List.sublistsAux_eq_array_foldl, List.forall₂_eq_eq_eq, List.Forall₂.flip, List.attach_nil, Cycle.instCoeList, Cycle.nil, List.tfae_singleton, Cycle.reverse_nil, List.nodup_nil, Cycle.empty_eq, List.singleton_injective, Cycle.nil_toMultiset, List.reverse_involutive, List.instIsPartialOrderIsInfix]

Link to cluster 79 with score 1026035.
Its hyp-names [Ne, AList]
Its thms [AList.lookup_insert_ne, AList.lookup_erase_ne, AList.insert_insert_of_ne, AList.replace, AList.lookup_isSome, AList.keys, AList.mem_lookup_union, AList.keys_replace, AList.insert, AList.lookup_insert_eq_none, AList.insert_entries, AList.ext_iff, AList.nodupKeys, AList.union_erase, AList.keys_nodup, AList.keys_insert, AList.Disjoint, AList.union_entries, AList.keys_erase, AList.mem_erase, AList.mem_union, AList.lookup_eq_none, AList.erase_erase, AList.erase, AList.lookup, AList.insert_union, AList.extract_eq_lookup_erase, AList.extract, AList.insert_insert, AList.mem_keys, AList.union, AList.instDecidableMem, AList.lookup_erase, AList.lookup_insert, AList.empty_union, AList.union_assoc, AList.mem_insert, AList.mem_replace, AList.union_empty, AList.lookup_union_eq_some, AList.entries, AList.mem_lookup_iff]

Link to cluster 82 with score 1638667.
Its hyp-names [Cycle.Subsingleton, Membership.mem, Cycle, Cycle.instMembership, Cycle.Chain]
Its thms [Cycle.Subsingleton.congr, Cycle.forall_eq_of_chain]

Link to cluster 81 with score 830155.
Its hyp-names [Cycle]
Its thms [Cycle.toMultiset, Cycle.toFinset_eq_nil, Cycle.chain_iff_pairwise, Cycle.toFinset, Cycle.mem_reverse_iff, Cycle.Nodup, Cycle.instDecidableNodup, Cycle.length_reverse, Cycle.instDecidableNontrivial, Cycle.lists, Cycle.reverse_reverse, Cycle.reverse, Cycle.subsingleton_reverse_iff, Cycle.instDecidableMemOfDecidableEq, Cycle.Mem, Cycle.toMultiset_eq_nil, Cycle.length_subsingleton_iff, Cycle.toFinset_toMultiset, Cycle.Nontrivial, Cycle.length, Cycle.Subsingleton, Cycle.card_toMultiset, Cycle.nodup_reverse_iff, Cycle.nontrivial_reverse_iff]

Link to cluster 91 with score 1399822.
Its hyp-names [AList.entries, Sigma, List.Perm]
Its thms [AList.mem_of_perm, AList.perm_union, AList.perm_replace, AList.perm_erase, AList.perm_lookup, AList.perm_insert, List.perm_nodupKeys]

Link to cluster 86 with score 1900798.
Its hyp-names [List.Perm, List.cons, Sigma, List.Sublist, List.NodupKeys]
Its thms [List.Perm.kerase, List.Perm.kinsert, List.Perm.kunion, List.perm_dlookup, List.perm_lookupAll, List.Perm.kreplace, List.not_mem_keys_of_nodupKeys_cons, List.nodupKeys_of_nodupKeys_cons, AList.mk_cons_eq_insert, List.NodupKeys.sublist]

Link to cluster 84 with score 2359878.
Its hyp-names [List.length, Fin, LE.le, Preorder.toLE, PartialOrder.toPreorder, List.Sorted, GE.ge, List.cons, List.map, List.Sublist, List.Disjoint, List.Nodup, Function.Injective]
Its thms [List.Nodup.erase_get, List.Nodup.get_inj_iff, List.next_get, List.get_indexOf, List.Nodup.getEquiv_apply_coe, List.Sorted.lt_of_le, List.Sorted.gt_of_ge, List.Nodup.of_cons, List.Nodup.not_mem, Cycle.nontrivial_coe_nodup_iff, List.nodup.sublists, List.Nodup.dedup, List.pmap_next_eq_rotate_one, List.Nodup.getEquiv, List.Nodup.insert, List.Nodup.attach, List.Nodup.pairwise_coe, List.Nodup.product, List.Nodup.mem_erase_iff, List.count_eq_of_nodup, List.Nodup.cyclicPermutations, List.Nodup.not_mem_erase, List.nodup.sublists', List.Nodup.of_map, List.Nodup.ne_singleton_iff, List.Nodup.erase, List.Nodup.sublist, List.Nodup.erase_eq_filter, List.Nodup.sym2, List.pmap_prev_eq_rotate_length_sub_one, List.Nodup.append, List.nodup_permutations, List.Nodup.map]

Link to cluster 85 with score 116209.
Its hyp-names [List.NodupKeys]
Its thms [List.mem_dlookup_iff, AList.mk.sizeOf_spec, AList.mk.injEq, List.NodupKeys.pairwise_ne, AList.mk, List.NodupKeys.kunion, List.lookupAll_eq_dlookup, List.lookupAll_nodup, List.NodupKeys.kerase, List.NodupKeys.nodup, List.dlookup_kerase, List.kinsert_nodupKeys, List.lookupAll_length_le_one, List.not_mem_keys_kerase]

Link to cluster 89 with score 1854134.
Its hyp-names [Preorder.toLT, instLTFin, LT.lt, instLEFin, List.length, List.Sorted, LE.le, Fin]
Its thms [List.Sorted.coe_getIso_apply, List.Sorted.rel_get_of_lt, List.Sorted.rel_get_of_le]

Link to cluster 88 with score 2365736.
Its hyp-names [List.zipWith, Ne, List.get, Eq, Prod, List.zip, List.ofFn, List.rotate, List.iterate, List.length, Fin]
Its thms [List.equivSigmaTuple_apply_snd, List.get_zipWith, List.erase_get, List.not_nodup_of_get_eq_of_ne, List.drop_take_succ_eq_cons_get, List.get_zip, List.get_ofFn, List.get_eq_get?, List.get_rotate, List.cons_get_drop_succ, List.get_iterate, List.toFinsupp_apply_fin]

Link to cluster 87 with score 1347285.
Its hyp-names [Equiv.Perm, Function.Injective, PartialOrder.toPreorder, Monotone, Fin.instPartialOrder, Fin]
Its thms [Equiv.Perm.map_finRange_perm, List.nodup_ofFn_ofInjective, List.mem_finRange, Monotone.ofFn_sorted, List.indexOf_finRange]

Link to cluster 90 with score 1390830.
Its hyp-names [RightCommutative, List.Forall₂, List.Perm, LeftCommutative]
Its thms [List.Perm.foldl_eq, List.perm_comp_forall₂, List.Perm.product, List.Perm.sym2, List.Perm.fold_op_eq, List.Perm.permutations', List.Perm.permutations, List.Perm.dedup, List.Perm.bagInter, List.Perm.foldr_eq]

Link to cluster 93 with score 2154744.
Its hyp-names [List.getLast?, List.cons, List.Chain', List.head?, List.argmax, List.argmin, Option, Option.instMembership, Membership.mem, List.dlookup]
Its thms [List.dropLast_append_getLast?, List.mem_getLast?_eq_getLast, List.mem_getLast?_cons, List.mem_of_mem_getLast?, List.mem_of_mem_head?, List.Chain'.rel_head?, List.cons_head?_tail, List.argmax_mem, List.argmin_mem, List.of_mem_dlookup]

Link to cluster 92 with score 2115775.
Its hyp-names [List.IsPrefix, Option, Option.some, List.find?, Eq]
Its thms [List.argAux, Option.toList_nodup, List.perm_option_to_list, List.IsPrefix.reduceOption, List.reduceOption_singleton, List.find?_mem]

Link to cluster 96 with score 1784896.
Its hyp-names [List.cons, List.Duplicate, List.Chain', List.Chain, List.Sublist]
Its thms [List.Sublist.of_cons_cons, List.sublist_of_cons_sublist_cons, List.Sublist.tail, List.Sublist.cons_cons, List.Duplicate.mono_sublist, List.Chain'.sublist, List.erase_diff_erase_sublist_of_sublist, List.Sublist.sublistForall₂, List.Sublist.antisymm, List.Chain.sublist, List.sublist_cons_of_sublist, List.Sublist.sym2, List.mem_sublistsLen_self]

Link to cluster 94 with score 1848753.
Its hyp-names [Preorder.toLE, LE.le, List.Subperm, List.cons, List.Sorted]
Its thms [List.mergeSort_eq_self, List.Sorted.get_mono, List.Sorted.orderedInsert, List.Sorted.merge, List.sublist_of_subperm_of_sorted, List.Sorted.insertionSort_eq, List.Sorted.of_cons, List.Sorted.tail, List.Sorted.nodup]

Link to cluster 95 with score 1546357.
Its hyp-names [LT.lt, Preorder.toLT, List.Sorted, GT.gt]
Its thms [List.Sorted.get_strictMono, List.Sorted.getIso, List.Sorted.le_of_lt, List.Sorted.ge_of_gt]

Link to cluster 97 with score 1861392.
Its hyp-names [Ne, List.cons, List.nil, List.Duplicate]
Its thms [List.Duplicate.of_duplicate_cons, List.Duplicate.mem_cons_self, List.Duplicate.elim_singleton, List.Duplicate.ne_nil, List.Duplicate.cons_duplicate, List.Duplicate.not_nodup, List.Duplicate.duplicate_cons, List.Duplicate.elim_nil, List.Duplicate.ne_singleton, List.Duplicate.mem]

Link to cluster 98 with score 1782546.
Its hyp-names [List.cons, List.IsSuffix, List.IsPrefix, List.IsInfix, List.Chain']
Its thms [List.Chain'.rel_head, List.Chain'.cons, List.Chain'.init, List.Chain'.suffix, List.destutter_of_chain', List.Chain'.prefix, List.Chain'.tail, List.Chain'.infix]



-/

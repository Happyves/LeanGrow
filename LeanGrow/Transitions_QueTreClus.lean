
import LeanGrow.Caches.QueryTreeSmoothClusters_wL_col2
import LeanGrow.Caches.QueryTreeSmoothClustersGoal_wL_col2
import LeanGrow.QueryTree_clean
--import LeanGrow.Caches.SmolTransitionGraphs
-- don't import ↑ and ↓ together
import LeanGrow.Caches.LargeTransitionGraphs
-- import LeanGrow.Caches.SmolTransitionGraphClosure_clos_3
-- import LeanGrow.Caches.LargeTransitionGraphClosure_clos_3
-- import LeanGrow.Caches.SmolTransitionGraphClosure_rbt_clos_3
-- import LeanGrow.Caches.LargeTransitionGraphClosure_rbt_clos_3


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
        rbn := RBNode.upsert instOrdNat.compare (· + hits) hits rbn n
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
        rbn := RBNode.upsert instOrdNat.compare (· + hits) hits rbn n
      return rbn




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
      --dbg_trace s!"0th closure queried on {key}, returning { (RBNode.toString (fun x => s!"{x}") (fun x => s!"{x}")) <$> (Prod.snd <$> (outer.find? (Prod.fst · = key)))}"
      (RBNode.map (fun _ v => (v,1))) <$> ((Prod.snd) <$> (outer.find? (Prod.fst · = key)))
  | n+1 => Id.run do
      --dbg_trace s!""
      --dbg_trace s!"Call on {n+1} with key {key}"
      let .some nei := Prod.snd <$> inner.find? (Prod.fst · = key) | return .none
      --dbg_trace s!"Found neighbourhood : {(RBNode.toString (fun x => s!"{x}") (fun x => s!"{x}")) nei}\nStart recursive calls in fold"
      let res := RBNode.fold
          (fun sofar k v => Id.run do
              let .some sofar' := sofar | return .none
              --dbg_trace s!"In fold of call {n+1} with key {key}, start fold loop with sofar : {(RBNode.toString (fun x => s!"{x}") (fun x => s!"{x}")) sofar'}"
              let .some fromhere := Id.run do
                --dbg_trace s!"In fold of call {n+1} with key {key}, make recursive call on key {k}"
                let .some clos := n_step_closure_rbt' n inner outer k | return Option.none
                --dbg_trace s!"In fold of call {n+1} with key {key}, update entries by adding edge weight {v}, so as to get: {(RBNode.toString (fun x => s!"{x}") (fun x => s!"{x}")) (RBNode.map (fun _ (total_weight, num_paths) => (total_weight+(v*num_paths), num_paths)) clos)}"
                return .some (RBNode.map (fun _ (total_weight, num_paths) => (total_weight+(v*num_paths), num_paths)) clos) | return Option.none
              --dbg_trace s!"In fold of call {n+1} with key {key}, merge it to main  entry, so as to get: {(RBNode.toString (fun x => s!"{x}") (fun x => s!"{x}")) (RBNode.fold (fun S K V => RBNode.upsert instOrdNat.compare (fun x => x + V) V S K) sofar' fromhere)}"
              return .some (RBNode.fold (fun S K V => RBNode.upsert instOrdNat.compare (fun x => x + V) V S K) sofar' fromhere)
              )
          (Option.some RBNode.leaf) nei
      --dbg_trace s!"Folds on call {n+1} with key {key} terminated, returning: {(RBNode.toString (fun x => s!"{x}") (fun x => s!"{x}")) <$> res}"
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

-- #exit


-- def merge_rbt' (rbts : List ((RBNode ℕ (fun _ ↦ ℕ)))) :  ((RBNode ℕ (fun _ ↦ ℕ))) :=
--   match rbts.head? with
--   | .some _ =>
--       (rbts.foldl (fun S rbt => (rbt.fold (fun s k v => s.insert instOrdNat.compare k v) S) ) RBNode.leaf)
--   | _ =>
--       .leaf


-- def n_step_closure_to_rbt (N : Nat) (inner outer : QueryTree (BS (Nat × (RBNode ℕ (fun _ ↦ ℕ))))) :  (RBNode ℕ (fun _ ↦ ((RBNode ℕ (fun _ ↦ ℕ))))) :=
--   let inner' := QueryTree.getVals inner
--   let outer' := QueryTree.getVals outer
--   (inner'.map Prod.fst).foldl (fun S k => S.insert instOrdNat.compare k (merge_rbt' ((List.range N).map (fun n => match n_step_closure_rbt n inner' outer' k with | .some x => x | _ => dbg_trace "here" ; .leaf))) ) RBNode.leaf



-- elab "make_smol_transition_graph_closure_rbt" : command => do
--   let clos_step := 3
--   let res := n_step_closure_to_rbt clos_step inner_trans outer_trans
--   let source := s!"\nimport LeanGrow.QueryTree_idea\nopen Lean Data\ndef smol_closure_rbt : (RBNode ℕ (fun _ ↦ ((RBNode ℕ (fun _ ↦ ℕ))))) := {RBNode.toString (fun x => s!"{x}") (RBNode.toString (fun x => s!"{x}") (fun x => s!"{x}"))  res}"
--   IO.FS.writeFile ⟨s!"/./home/yves/Desktop/CodeWorkspace/Lean4_General/LeanGrow/LeanGrow/Caches/SmolTransitionGraphClosure_rbt_clos_{clos_step}.lean"⟩ (source)

-- --make_smol_transition_graph_closure_rbt

-- elab "make_large_transition_graph_closure_rbt" : command => do
--   let clos_step := 3
--   let res := n_step_closure_to_rbt clos_step inner_trans_large outer_trans_large
--   let source := s!"\nimport LeanGrow.QueryTree_idea\nopen Lean Data\ndef large_closure_rbt : (RBNode ℕ (fun _ ↦ ((RBNode ℕ (fun _ ↦ ℕ))))) := {RBNode.toString (fun x => s!"{x}") (RBNode.toString (fun x => s!"{x}") (fun x => s!"{x}"))  res}"
--   IO.FS.writeFile ⟨s!"/./home/yves/Desktop/CodeWorkspace/Lean4_General/LeanGrow/LeanGrow/Caches/LargeTransitionGraphClosure_rbt_clos_{clos_step}.lean"⟩ (source)

-- --make_large_transition_graph_closure_rbt


-- #exit


-- # Analysis of clusters and graphs


def print_cluster_hyp_names (L : List pdata) : List String :=
  ((L.map pdata.sink_cst_names).map (Trie.print_keys ⟨#[]⟩)).join

def print_cluster_goal_names (L : List pdata) : List String :=
  ((L.map pdata.goal_cst_names).map (Trie.print_keys ⟨#[]⟩)).join

def get_cluster_list_from_index (i : Nat) : List pdata :=
  match Lsclu_from_qt_all.find? (fun (j,_) => i=j) with
  | .some l => l.2
  | _ => []

def RBNode.getVals : RBNode α (fun _ => β) → List (α × β)
| .leaf => []
| .node _ l k v r => (k,v) :: ((RBNode.getVals l) ++ (RBNode.getVals r))


#exit

elab "one_step_cluster_study_large" : command => do
  let mut toPrint := [""]
  let cluster_index := 110 --110 --106 --96
  let data := get_cluster_list_from_index cluster_index
  toPrint := s!"Analysis on cluster nr. {cluster_index}.\nIts hyp-names: {print_cluster_hyp_names data}\n\n" :: toPrint
  let .some nei := (QueryTree.query RTreeTop) instOrdNat.compare cluster_index | throwError "aaaahhh"
  let nei! := RBNode.getVals nei
  for (idx, hits) in nei! do
    toPrint := s!"Suggests moving to cluster nr. {idx}, with score {hits}.\nIts hyp-names: {print_cluster_hyp_names (get_cluster_list_from_index idx)}\n\n" :: toPrint
  IO.println (String.join toPrint.reverse)

--one_step_cluster_study_large

/-
- 96 :  nice small cluster, with coherence arround List.Nodup
- 106 : mega cluster arround Nat and Nat's ≤  and < instances ...
- 110 : empty hyp names... but not actually empty

-/


#exit

--#eval  QueryTree.toString BS.toString_trick_more (QueryTree.mapBS (fun (n,l) => (n, Clus_Nei_inner l)) Lsclu_from_qt_all)
#check (QueryTree.mapBS (fun (n,l) => (n, Clus_Nei_inner l)) Lsclu_from_qt_all)


elab "testin_1" : command => do
  let mut toPrint := [""]
  let nr := 96
  let data := get_cluster_list_from_index nr
  let rbt := Clus_Nei_inner data
  toPrint := s!"Analysis on cluster nr. {nr}.\nIts hyp-names: {print_cluster_hyp_names data}\n\n" :: toPrint
  let nei! := RBNode.getVals rbt
  for (idx, hits) in nei! do
    toPrint := s!"Suggests moving to cluster nr. {idx}, with score {hits}.\nIts hyp-names: {print_cluster_hyp_names (get_cluster_list_from_index idx)}\n\n" :: toPrint
  IO.println (String.join toPrint.reverse)

--testin_1

#eval RBNode.toString (fun x => s!"{x}") (fun x => s!"{x}") (Clus_Nei_inner (get_cluster_list_from_index 96))
#eval (get_cluster_list_from_index 96).length

#eval RBNode.toString (fun x => s!"{x}") (fun x => s!"{x}") (Clus_Nei_inner_large (get_cluster_list_from_index 96))

#eval (QueryTree.query (SortedTrieFormList' ["List"]) Lsclu_from_qt_all).map Prod.fst

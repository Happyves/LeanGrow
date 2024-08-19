
import LeanGrow.Caches.CoData
import LeanGrow.Caches.goalCoData
--import LeanGrow.Caches.CarikarClusters_batch_o_0 -- seems to have been corrupted when I did  the same for nomenclature .. should be rebuilt
import LeanGrow.Caches.CarikarClustersGoal_batch_0
import LeanGrow.Caches.CoData_nom
import LeanGrow.Caches.CarikarClustersNom_batch_o_0
import LeanGrow.Caches.CarikarClustersSquared_batch_0


open Lean Data

partial def Trie.get_key [BEq α] (v : α) (cache : ByteArray) : Trie α → Option String
| .leaf x => if x == .some v then .some (String.fromUTF8! cache) else .none
| .node1 x a t =>
    if x == .some v
    then .some (String.fromUTF8! cache)
    else Trie.get_key v (cache.push a) t
| .node x as ts =>
    if x == .some v
    then .some (String.fromUTF8! cache)
    else
      Id.run do
      for c in List.range (as.size) do
        let res := Trie.get_key v (cache.push (as.get! c)) (ts.get! c)
        if res.isSome then return res
      return .none




elab "app_order": command => do
  let mut tag := Array.mkArray joined_apps.size (0,0)
  let mut c := 0
  for x in joined_apps do
    tag := tag.set! c (c,x)
    c := c+1
  let stag := tag.qsort (fun (_,x) (_,y)=> x > y)
  let pstag := (stag.map (fun (i,v) => ((·,v)) <$> (Trie.get_key i ⟨#[]⟩ indexing))).reduceOption
  IO.println pstag

--app_order

/-
Observation :
- we get rfl, probably from terms woh's types carry proofs ? Modify getConstNames to only take constant names who's types aren't props (in MetaM)

-/


def burnout (i : Nat) : Option (Nat × Nat) :=
  if i = 0 then (1,0)
  else if i = 1 then (2,0)
       else if i = 2 then (2,1)
            else if i = 3 then (3,0)
              else
                Id.run do
                let mut s := 0
                for x in List.range i do
                  if i < s + x
                  then return .some (x,i-s)
                  else s := s+x
                return .none


elab "co_order": command => do
  let mut tag := []
  let mut cx := 0
  for x in joined_co_pre do
    let mut cy := 0
    for y in x do
      if y ≥ 10 then tag := (((cx*10) + cy),y) :: tag -- the 10 here is the split_param for data
      cy := cy +1
    cx := cx +1
  let stag := tag.mergeSort (fun (_,x) (_,y)=> x > y)
  let pstag := (stag.map (fun (i,v) =>
      match burnout i with
      | .none => .none
      | .some (f,s) =>
          match (Trie.get_key (f) ⟨#[]⟩ indexing), (Trie.get_key (s) ⟨#[]⟩ indexing) with
          | .some fn, .some sn => .some ((fn,sn),v)
          | _, _ => .none
      )).reduceOption
  IO.println pstag

--co_order



elab "g_app_order": command => do
  let mut tag := Array.mkArray g_joined_apps.size (0,0)
  let mut c := 0
  for x in g_joined_apps do
    tag := tag.set! c (c,x)
    c := c+1
  let stag := tag.qsort (fun (_,x) (_,y)=> x > y)
  let pstag := (stag.map (fun (i,v) => ((·,v)) <$> (Trie.get_key i ⟨#[]⟩ g_indexing))).reduceOption
  IO.println pstag

elab "g_co_order": command => do
  let mut tag := []
  let mut cx := 0
  for x in g_joined_co_pre do
    let mut cy := 0
    for y in x do
      if y ≥ 10 then tag := (((cx*10) + cy),y) :: tag -- the 10 here is the split_param for data
      cy := cy +1
    cx := cx +1
  let stag := tag.mergeSort (fun (_,x) (_,y)=> x > y)
  let pstag := (stag.map (fun (i,v) =>
      match burnout i with
      | .none => .none
      | .some (f,s) =>
          match (Trie.get_key (f) ⟨#[]⟩ g_indexing), (Trie.get_key (s) ⟨#[]⟩ g_indexing) with
          | .some fn, .some sn => .some ((fn,sn),v)
          | _, _ => .none
      )).reduceOption
  IO.println pstag

--g_app_order

--g_co_order

-- #eval Trie.print_keys ⟨#[]⟩ clusTrie_0
-- #eval Trie.print_keys ⟨#[]⟩ clusTrie_1
-- #eval Trie.print_keys ⟨#[]⟩ clusTrie_2


#eval Trie.print_keys ⟨#[]⟩ g_clusTrie_0
#eval Trie.print_keys ⟨#[]⟩ g_clusTrie_1
#eval Trie.print_keys ⟨#[]⟩ g_clusTrie_2



elab "nom_app_order": command => do
  let mut tag := Array.mkArray nom_joined_apps.size (0,0)
  let mut c := 0
  for x in nom_joined_apps do
    tag := tag.set! c (c,x)
    c := c+1
  let stag := tag.qsort (fun (_,x) (_,y)=> x > y)
  let pstag := (stag.map (fun (i,v) => ((·,v)) <$> (Trie.get_key i ⟨#[]⟩ nom_indexing))).reduceOption
  IO.println pstag

elab "nom_co_order": command => do
  let mut tag := []
  let mut cx := 0
  for x in nom_joined_co_pre do
    let mut cy := 0
    for y in x do
      if y ≥ 10 then tag := (((cx*10) + cy),y) :: tag -- the 10 here is the split_param for data
      cy := cy +1
    cx := cx +1
  let stag := tag.mergeSort (fun (_,x) (_,y)=> x > y)
  let pstag := (stag.map (fun (i,v) =>
      match burnout i with
      | .none => .none
      | .some (f,s) =>
          match (Trie.get_key (f) ⟨#[]⟩ nom_indexing), (Trie.get_key (s) ⟨#[]⟩ nom_indexing) with
          | .some fn, .some sn => .some ((fn,sn),v)
          | _, _ => .none
      )).reduceOption
  IO.println pstag

-- nom_app_order

-- nom_co_order

#eval Trie.print_keys ⟨#[]⟩ nom_clusTrie_0
#eval Trie.print_keys ⟨#[]⟩ nom_clusTrie_1
#eval Trie.print_keys ⟨#[]⟩ nom_clusTrie_2

#eval Trie.print_keys ⟨#[]⟩ sq_clusTrie_0
#eval Trie.print_keys ⟨#[]⟩ sq_clusTrie_1
#eval Trie.print_keys ⟨#[]⟩ sq_clusTrie_2

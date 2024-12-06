
import LeanGrow.F.Utils.SetTrie.Types


#check 1

namespace SetTrie

def init [Inhabited α] (l : List β) : SetTrie α β :=
  .root (l.map (fun x => .node x [.leaf default]))

def initial (l : List (β × α)) : SetTrie α β :=
  .root (l.map (fun (xb,xa) => .node xb [.leaf xa]))


def find_keys (c : List (SetTrie α β)) (empty : γ) (merge : β → γ → γ) : γ :=
  match c with
  | [] => empty
  | .root _ :: _ => empty -- ill formed tree, root shouldn't appear as child
  | .node t _ :: rest =>
        let sofar := find_keys rest empty merge
        merge t sofar
  | .leaf _ :: rest => find_keys rest empty merge


def find_keys' (c : List (SetTrie α β)) (empty : β) (merge : β → β → β) (count : β → γ) : γ :=
  let rec go (done : β) : List (SetTrie α β) → β
    | [] => done
    | nx :: more =>
        match nx with
        | .root _ => empty
        | .node t _ => go (merge done t) more
        | .leaf _ => go done more
  count (go empty c)



def split_on_split (c : List (SetTrie α β)) (key : γ) (find : β → γ → Option δ) :
  List (SetTrie α β) × List (SetTrie α β) :=
  match c with
  | [] => ([],[])
  | .root _ :: _ => ([],[]) -- ill formed tree, root shouldn't appear as child
  | .node t chi :: rest =>
        let (sofar_pos, sofar_neg) := split_on_split rest key find
        let T := find t key
        match T with
        | .some _ => (.node t chi :: sofar_pos, sofar_neg)
        | .none => (sofar_pos, .node t chi :: sofar_neg)
  | .leaf a :: rest =>
        let (sofar_pos, sofar_neg) := split_on_split rest key find
        (sofar_pos, .leaf a :: sofar_neg)


def split_on (c : List (SetTrie α β)) (key : γ) (find : β → γ → Option δ)
  (newkey : β) : List (SetTrie α β) :=
    let (pos, neg) := split_on_split c key find
    (.node (newkey) pos) :: neg


def delete_key_or_leave (k : γ) (delete : β → γ → β) : SetTrie α β → SetTrie α β
  | .node T r => .node ((delete T k)) r
  | x => x


partial def split_greedy_exact_hitting_set
    (empty : γ) (merge : β → γ → γ) (max : γ → Option (δ × Nat))
    (find : β → δ → Option ι) (delete : β → δ → β) (newkey : δ → β)
    (c : List (SetTrie α β)) : List (SetTrie α β) :=
      let apps := SetTrie.find_keys c empty merge
      match max apps with
      | .none => c
      | .some (key, M) =>
            if M > 1
            then
              let (pos, neg) := SetTrie.split_on_split c key find
              let pos' := pos.map (fun qt => SetTrie.delete_key_or_leave key delete qt)
              let proceed := SetTrie.split_greedy_exact_hitting_set empty merge max find delete newkey neg
              (.node (newkey key) pos') :: proceed
            else c

partial def split_greedy_exact_hitting_set'
    (empty : β) (merge : β → β → β) (count : β → γ) (max : γ → Option (δ × Nat))
    (find : β → δ → Option ι) (delete : β → δ → β) (newkey : δ → β)
    (c : List (SetTrie α β)) : List (SetTrie α β) :=
      let apps := SetTrie.find_keys' c empty merge count
      match max apps with
      | .none => c
      | .some (key, M) =>
            if M > 1
            then
              let (pos, neg) := SetTrie.split_on_split c key find
              let pos' := pos.map (fun qt => SetTrie.delete_key_or_leave key delete qt)
              let proceed := SetTrie.split_greedy_exact_hitting_set' empty merge count max find delete newkey neg
              (.node (newkey key) pos') :: proceed
            else c



def delete_keyes_or_leave (k : β) (difference : β → β → β) : SetTrie α β → SetTrie α β :=
  fun t =>  match t with
            | .node T r => .node ((difference T k)) r
            | x => x


partial def lift
  (emptyC : γ) (emptyO : β) (merge : β → γ → γ) (max : γ → Option (β × Nat))
  (difference : β → β → β)
  (c : List (SetTrie α β)) : β × List (SetTrie α β) :=
    let apps := SetTrie.find_keys c emptyC merge
    match max apps with
    | .none => (emptyO,c)
    | .some (key, M) =>
          if M = c.length
          then  let c' := c.map (fun qt => SetTrie.delete_keyes_or_leave key difference qt)
                (key,c')
          else (emptyO,c)


partial def lift'
  (emptyO : β) (merge : β → β → β) (count : β → γ) (max : γ → Option (β × Nat))
  (difference : β → β → β)
  (c : List (SetTrie α β)) : β × List (SetTrie α β) :=
    let apps := SetTrie.find_keys' c emptyO merge count
    match max apps with
    | .none => (emptyO,c)
    | .some (key, M) =>
          if M = c.length
          then  let c' := c.map (fun qt => SetTrie.delete_keyes_or_leave key difference qt)
                (key,c')
          else (emptyO,c)



def build_main (emptyC : γ) (emptyO : β) (merge : β → γ → γ) (max : γ → Option (β × Nat))
  (difference : β → β → β) (maxl : γ → Option (δ × Nat))
  (find : β → δ → Option ι) (delete : β → δ → β) (newkey : δ → β)
    (c : List (SetTrie α β)) : β × List (SetTrie α β) :=
      let (lifted_names, listed_children) := SetTrie.lift emptyC emptyO merge max difference c
      (lifted_names, SetTrie.split_greedy_exact_hitting_set emptyC merge maxl find delete newkey listed_children)



def build_main' (emptyO : β) (merge : β → β → β) (count : β → γ) (max : γ → Option (β × Nat))
  (difference : β → β → β) (maxl : γ → Option (δ × Nat))
  (find : β → δ → Option ι) (delete : β → δ → β) (newkey : δ → β)
    (c : List (SetTrie α β)) : β × List (SetTrie α β) :=
      let (lifted_names, listed_children) := SetTrie.lift' emptyO merge count max difference c
      (lifted_names, SetTrie.split_greedy_exact_hitting_set' emptyO merge count maxl find delete newkey listed_children)




partial def build [Inhabited α] [BEq β] (emptyC : γ) (emptyO : β) (merge : β → γ → γ) (max : γ → Option (β × Nat))
  (difference : β → β → β) (maxl : γ → Option (δ × Nat))
  (find : β → δ → Option ι) (delete : β → δ → β) (newkey : δ → β) (mergeB : β → β → β)
  : SetTrie α β → SetTrie α β
    | .root c =>
          let (l,cn) := SetTrie.build_main emptyC emptyO merge max difference maxl find delete newkey  c
          if l == emptyO
          then .root (cn.map (build emptyC emptyO merge max difference maxl find delete newkey mergeB))
          else .root [.node l (cn.map ((build emptyC emptyO merge max difference maxl find delete newkey mergeB)) )]
    | .node t c =>
          let (l,cn) := SetTrie.build_main emptyC emptyO merge max difference maxl find delete newkey c
          if cn.isEmpty
          then   .node (mergeB t l) [.leaf default]
          else   .node (mergeB t l) (cn.map (build emptyC emptyO merge max difference maxl find delete newkey mergeB))
    | .leaf a =>  .leaf a


partial def build' [Inhabited α] [BEq β] (emptyO : β) (merge : β → β → β) (count : β → γ) (max : γ → Option (β × Nat))
  (difference : β → β → β) (maxl : γ → Option (δ × Nat))
  (find : β → δ → Option ι) (delete : β → δ → β) (newkey : δ → β)
  : SetTrie α β → SetTrie α β
    | .root c =>
          let (l,cn) := SetTrie.build_main' emptyO merge count max difference maxl find delete newkey  c
          if l == emptyO
          then .root (cn.map (build' emptyO merge count max difference maxl find delete newkey))
          else .root [.node l (cn.map ((build' emptyO merge count max difference maxl find delete newkey)) )]
    | .node t c =>
          let (l,cn) := SetTrie.build_main' emptyO merge count max difference maxl find delete newkey c
          if cn.isEmpty
          then   .node (merge t l) [.leaf default]
          else   .node (merge t l) (cn.map (build' emptyO merge count max difference maxl find delete newkey))
    | .leaf a =>  .leaf a




def make [Inhabited α] [BEq β] (emptyC : γ) (emptyO : β) (merge : β → γ → γ) (max : γ → Option (β × Nat))
  (difference : β → β → β) (maxl : γ → Option (δ × Nat))
  (find : β → δ → Option ι) (delete : β → δ → β) (newkey : δ → β) (mergeB : β → β → β) (l : List β) : SetTrie α β :=
    (SetTrie.build emptyC emptyO merge max difference maxl find delete newkey mergeB (SetTrie.init l))


def make' [Inhabited α] [BEq β] (emptyO : β) (merge : β → β → β) (count : β → γ) (max : γ → Option (β × Nat))
  (difference : β → β → β) (maxl : γ → Option (δ × Nat))
  (find : β → δ → Option ι) (delete : β → δ → β) (newkey : δ → β) (l : List β) : SetTrie α β :=
    (SetTrie.build' emptyO merge count max difference maxl find delete newkey (SetTrie.init l))


end SetTrie

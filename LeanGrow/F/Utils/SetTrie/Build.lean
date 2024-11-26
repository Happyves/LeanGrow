
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

end SetTrie

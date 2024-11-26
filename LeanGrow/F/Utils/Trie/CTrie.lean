
import LeanGrow.F.Utils.Trie.ByteArray


inductive CTrie (α : Type) where
  | leaf : Option α → CTrie α
  | node1 : Option α → ByteArray → CTrie α → CTrie α
  | node : Option α → Array ByteArray → Array (CTrie α) → CTrie α
deriving Repr


namespace CTrie
variable {α : Type}

def empty : CTrie α := leaf none

instance : EmptyCollection (CTrie α) :=
  ⟨empty⟩

instance : Inhabited (CTrie α) where
  default := empty


private def upsert_help (cs : Array ByteArray) (i : Nat) (s : ByteArray) : Option (Nat × Nat) :=
  let rec go : Nat → Option (Nat × Nat)
    | 0 => .none
    | n+1 =>
        let j := ByteArray.getLongestMatch_wOffset i s (cs.get! n)
        if j == 0 then go n else .some (n,j)
  go cs.size

partial def upsert (t : CTrie α) (s : ByteArray) (f : Option α → Option α) : CTrie α :=
  let rec go (i : Nat) : CTrie α → CTrie α
    | .leaf v =>
          if i < s.size
          then
            .node1 v (s.drop i) (.leaf (f .none))
          else
            .leaf (f v)
    | .node1 v c t =>
          if i < s.size
          then
            let j := ByteArray.getLongestMatch_wOffset i s c
            let sum := (i+j)
            if j == c.size
            then
              .node1 v c (go sum t)
            else
              if sum == s.size
              then
                .node1 v (c.take j) (.node1 (f .none) (c.drop j) t)
              else
                let nc := c.drop j
                let add := s.drop sum
                let join := c.take j
                .node1 v join (.node .none #[nc,add] #[t,(.leaf (f .none))])
          else
            .node1 (f v) c t
    | .node v cs ts =>
          if i < s.size
          then
            match CTrie.upsert_help cs i s with
            | .none =>
                .node v (cs.push (s.drop i)) (ts.push (.leaf (f .none)))
            | .some (idx,len) =>
                let sum := (i+len)
                let c := (cs.get! idx)
                if len == c.size
                then
                  .node v cs (ts.modify idx ((go sum)))
                else
                  if sum == s.size
                  then
                    .node v ((cs.modify idx (fun _ => c.take len))) (ts.modify idx (fun t => .node1 (f .none) (c.drop len) t))
                  else
                    let nc := c.drop len
                    let add := s.drop sum
                    let join := c.take len
                    .node v ((cs.modify idx (fun _ => join))) (ts.modify idx (fun t => .node .none #[nc,add] #[t,(.leaf (f .none))]))
          else
            .node (f v) cs ts
  go 0 t



partial def insert (t : CTrie α) (s : String) (val : α) : CTrie α :=
  CTrie.upsert t (s.toUTF8) (fun _ => val)

partial def delete (t : CTrie α) (s : String)  : CTrie α :=
  CTrie.upsert t (s.toUTF8) (fun _ => .none)


def ofList : List (String × α) → CTrie α
  | [] => CTrie.empty
  | (s,v) :: more => CTrie.insert (CTrie.ofList more) s v



partial def find? (t : CTrie α) (s : String) : Option α :=
  let toB := s.toUTF8
  let rec go (i : Nat) : CTrie α → Option α
    | .leaf v => v
    | .node1 v c t =>
          if i = toB.size
          then v
          else
            let j := ByteArray.getLongestMatch_wOffset i toB c
            if j == c.size
            then go (i+j) t
            else .none
    | .node v cs ts =>
          if i = toB.size
          then v
          else
            match CTrie.upsert_help cs i toB with
            | .none => .none
            | .some (idx,len) =>
                  if len == (cs.get! idx).size
                  then go (i+len) (ts.get! idx)
                  else .none
  go 0 t


#eval (⟨#[1,2]⟩ : ByteArray) ++ (⟨#[3,4]⟩ : ByteArray)


partial def toList (t : CTrie α) : List (String × α) :=
  let rec go (done : List (String × α)) : List (ByteArray × CTrie α) → List (String × α)
    | [] => done
    | (pre, nx) :: more =>
      match nx with
      | .leaf x =>
          match x with
          | .some v => go ((String.fromUTF8! pre, v) :: done) more
          | .none => go done more
      | .node1 x ax cx =>
          let next := (pre ++ ax, cx) :: more
          match x with
          | .some v => go ((String.fromUTF8! pre, v) :: done) next
          | .none => go done next
      | .node x ax cx =>
          let next := (Array.zip (ax.map (pre ++ ·)) cx).toList ++ more
          match x with
          | .some v => go ((String.fromUTF8! pre, v) :: done) next
          | .none => go done next
  go [] [(⟨#[]⟩, t)]


partial def size (t : CTrie α) : Nat :=
  let rec go (count : Nat) : List (CTrie α) → Nat
    | [] => count
    | nx :: more =>
        match nx with
        | .leaf x => match x with | .some _ => go (Nat.succ count) more | .none => go count more
        | .node1 x _ cx => match x with | .some _ => go (Nat.succ count) (cx :: more) | .none => go count (cx :: more)
        | .node x _ cx => match x with | .some _ => go (Nat.succ count) (cx.toList ++ more) | .none => go count (cx.toList ++ more)
  go 0 [t]


partial def keys (t : CTrie α) : List (String) :=
  let rec go (done : List (String)) : List (ByteArray × CTrie α) → List (String)
    | [] => done
    | (pre, nx) :: more =>
      match nx with
      | .leaf x =>
          match x with
          | .some _ => go ((String.fromUTF8! pre) :: done) more
          | .none => go done more
      | .node1 x ax cx =>
          let next := (pre ++ ax, cx) :: more
          match x with
          | .some _ => go ((String.fromUTF8! pre) :: done) next
          | .none => go done next
      | .node x ax cx =>
          let next := (Array.zip (ax.map (pre ++ ·)) cx).toList ++ more
          match x with
          | .some _ => go ((String.fromUTF8! pre) :: done) next
          | .none => go done next
  go [] [(⟨#[]⟩, t)]


partial def values (t : CTrie α) : List α :=
  let rec go (done : List α) : List (ByteArray × CTrie α) → List α
    | [] => done
    | (pre, nx) :: more =>
      match nx with
      | .leaf x =>
          match x with
          | .some v => go ((v) :: done) more
          | .none => go done more
      | .node1 x ax cx =>
          let next := (pre ++ ax, cx) :: more
          match x with
          | .some v => go ((v) :: done) next
          | .none => go done next
      | .node x ax cx =>
          let next := (Array.zip (ax.map (pre ++ ·)) cx).toList ++ more
          match x with
          | .some v => go ((v) :: done) next
          | .none => go done next
  go [] [(⟨#[]⟩, t)]


partial def clean (t : CTrie α) : CTrie α :=
  match t with
  | .leaf x => .leaf x
  | .node1 x ax cx =>
      let sofar := cx.clean
      match sofar with
      | .leaf .none => .leaf x
      | _ => .node1 x ax sofar
  | .node x ax cx =>
      let sofar := cx.map CTrie.clean
      let rec clean_inner (bs : List ByteArray) (ts : List (CTrie α)) : Nat → List ByteArray × List (CTrie α)
        | 0 => (bs,ts)
        | n+1 =>
            let X := sofar.get! n
            match X with
            | .leaf .none => clean_inner bs ts n
            | _ => clean_inner ((ax.get! n) :: bs) (X :: ts) n
      let (nax,ncx) := clean_inner [] [] sofar.size
      match nax, ncx with
      | [], _ => .leaf x
      | [NAX], [NCX] => .node1 x NAX NCX
      | _, _ => .node x nax.toArray ncx.toArray


partial def enumerate (count : Nat) : CTrie α → ((CTrie Nat) × List (Nat × α) × Nat)
  | .leaf x =>
      match x with
      | .some v => (.leaf (.some count), [(count,v)], count + 1)
      | .none =>  (.leaf .none, [], count)
  | .node1 x ax cx =>
      match x with
      | .some v =>
          let (nt,nv,nc) := enumerate (count + 1) cx
          (.node1 (.some count) ax nt, (count,v) :: nv, nc)
      | _ =>
          let (nt,nv,nc) := enumerate count cx
          (.node1 .none ax nt, nv, nc)
  | .node x ax cx =>
      let rec inner (A : Array (CTrie Nat)) (cc: Nat) (vals : List (Nat × α)) : Nat → ((Array (CTrie Nat)) × Nat × List (Nat × α))
        | 0 => (A,cc,vals)
        | n+1 =>
            let (nt,nvals,ncc) := enumerate cc (cx.get! n)
            inner (A.set! n nt) ncc (nvals ++ vals) n
      match x with
      | .some v =>
            let ncx := Array.mkArray cx.size (.leaf .none)
            let (res,nc,nv) := inner ncx (count+1) [] cx.size
            (.node (.some count) ax res, (count,v) :: nv,nc)
      | _ =>
            let ncx := Array.mkArray cx.size (.leaf .none)
            let (res,nc,nv) := inner ncx count [] cx.size
            (.node .none ax res, nv,nc)

partial def find_max (T : CTrie Nat) : Option (String × Nat) :=
  let rec go (sofar : Option (String × Nat)) : List (ByteArray × CTrie Nat) → Option (String × Nat)
    | [] => sofar
    | nx :: more =>
        match nx.2 with
        | .leaf x =>
              match x, sofar with
              | .some v, .some w =>
                  if v > w.2
                  then go (.some (String.fromUTF8! nx.1, v)) more
                  else go sofar more
              | .some v, .none => go (.some (String.fromUTF8! nx.1, v)) more
              | _, _ => go sofar more
        | .node1 x a t =>
              match x, sofar with
              | .some v, .some w =>
                  if v > w.2
                  then go (.some (String.fromUTF8! nx.1, v)) ((nx.1 ++ a,t) :: more)
                  else go sofar ((nx.1 ++ a,t) :: more)
              | .some v, .none => go (.some (String.fromUTF8! nx.1, v)) ((nx.1 ++ a,t) :: more)
              | _, _ => go sofar ((nx.1 ++ a,t) :: more)
        | .node x as ts =>
              match x, sofar with
              | .some v, .some w =>
                  if v > w.2
                  then go (.some (String.fromUTF8! nx.1, v)) ((Array.zip (as.map (nx.1 ++ ·)) ts).toList ++ more)
                  else go sofar ((Array.zip (as.map (nx.1 ++ ·)) ts).toList ++ more)
              | .some v, .none => go (.some (String.fromUTF8! nx.1, v)) ((Array.zip (as.map (nx.1 ++ ·)) ts).toList ++ more)
              | _, _ => go sofar ((Array.zip (as.map (nx.1 ++ ·)) ts).toList ++ more)
  go .none [(⟨#[]⟩,T)]

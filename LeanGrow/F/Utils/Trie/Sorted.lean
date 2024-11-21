
import LeanGrow.F.Utils.Trie.CTrie

#check 1

namespace CTrie

private inductive upsert_help_type where
  | hit (pos : Nat) (len : Nat)
  | ins (pos : Nat)
  deriving Inhabited, BEq, Repr


private def sorted_upsert_help (cs : Array ByteArray) (i : Nat) (s : ByteArray) (si : UInt8) : upsert_help_type :=
  let rec go : Nat → upsert_help_type
    | 0 => .ins 0
    | n+1 =>
        let c := (cs.get! n)
        let j := ByteArray.getLongestMatch_wOffset i s c
        if j == 0
        then
          if si < c.get! 0
          then go n
          else .ins (n+1)
        else .hit n j
  go cs.size

partial def sorted_upsert (t : CTrie α) (s : ByteArray) (f : Option α → α) : CTrie α :=
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
                if c.get! j < s.get! sum
                then .node1 v join (.node .none #[nc,add] #[t,(.leaf (f .none))])
                else .node1 v join (.node .none #[add,nc] #[(.leaf (f .none)),t])
          else
            .node1 (f v) c t
    | .node v cs ts =>
          if i < s.size
          then
            match CTrie.sorted_upsert_help cs i s (s.get! i) with
            | .ins pos =>
                .node v (cs.insertAt! pos (s.drop i)) (ts.insertAt! pos (.leaf (f .none)))
            | .hit idx len =>
                let c := (cs.get! idx)
                let sum := (i+len)
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
                    if c.get! len < s.get! sum
                    then .node v ((cs.modify idx (fun _ => join))) (ts.modify idx (fun t => .node .none #[nc,add] #[t,(.leaf (f .none))]))
                    else .node v ((cs.modify idx (fun _ => join))) (ts.modify idx (fun t => .node .none #[add,nc] #[(.leaf (f .none)),t]))
          else
            .node (f v) cs ts
  go 0 t


partial def sorted_insert (t : CTrie α) (s : String) (val : α) : CTrie α :=
  CTrie.sorted_upsert t (s.toUTF8) (fun _ => val)



def ofList_sorted : List (String × α) → CTrie α
  | [] => CTrie.empty
  | (s,v) :: more => CTrie.sorted_insert (CTrie.ofList_sorted more) s v


partial def sorted_find? (t : CTrie α) (s : String) : Option α :=
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
            match CTrie.sorted_upsert_help cs i toB (toB.get! i) with
            | .ins _ => .none
            | .hit idx len =>
                  if len == (cs.get! idx).size
                  then go (i+len) (ts.get! idx)
                  else .none
  go 0 t



def match_nontrivial [BEq α] (l r : Option α) : Bool :=
  match l with
  | .none => false
  | .some vl =>
      match r with
      | .none => false
      | .some vr => vl == vr




partial def CountCommon [BEq α] [Repr α] (l r : CTrie α) : Nat :=
  let rec go (l r : CTrie α) (ol or : Nat) : Nat :=
    match l with
    | .leaf x =>
        match r with
        | .leaf y => if match_nontrivial x y then 1 else 0
        | .node1 y _ _ => if match_nontrivial x y then 1 else 0
        | .node y _ _ => if match_nontrivial x y then 1 else 0
    | .node1 x ax cx =>
        match r with
        | .leaf y => if match_nontrivial x y then 1 else 0
        | .node1 y ay cy =>
              let com := ByteArray.getLongestMatch_wOffsets ax ay ol or
              if ol + com == ax.size
              then
                if ax.size == ay.size
                then
                  let sofar := go cx cy 0 0
                  if match_nontrivial x y then Nat.succ sofar else sofar
                else
                  let sofar := go cx r 0 (or + com)
                  if match_nontrivial x y then Nat.succ sofar else sofar
              else
                if or + com == ay.size
                then
                  let sofar := go l cy (ol + com) 0
                  if match_nontrivial x y then Nat.succ sofar else sofar
                else
                  if match_nontrivial x y then 1 else 0
        | .node y ay cy =>
              match ByteArray.matchSingle_wOffset ax ol ay with
              | .none => if match_nontrivial x y then 1 else 0
              | .some idx =>
                  let ay' := ay.get! idx
                  let cy' := cy.get! idx
                  -- sam as ↑
                  let com := ByteArray.getLongestMatch_wOffsets ax ay' ol 0
                  if ol + com == ax.size
                  then
                    if ax.size == ay'.size
                    then
                      let sofar := go cx cy' 0 0
                      if match_nontrivial x y then Nat.succ sofar else sofar
                    else
                      let sofar := go cx (.node1 .none ay' cy') 0 0
                      if match_nontrivial x y then Nat.succ sofar else sofar
                  else
                    if com == ay.size
                    then
                      let sofar := go l cy' (ol+com) 0
                      if match_nontrivial x y then Nat.succ sofar else sofar
                    else
                      if match_nontrivial x y then 1 else 0
    | .node x ax cx =>
        match r with
        | .leaf y => if match_nontrivial x y then 1 else 0
        | .node1 y ay cy =>
              match ByteArray.matchSingle_wOffset ay or ax with
              | .none => if match_nontrivial x y then 1 else 0
              | .some idx =>
                  let ax' := ax.get! idx
                  let cx' := cx.get! idx
                  -- sam as ↑
                  let com := ByteArray.getLongestMatch_wOffsets ax' ay 0 or
                  if com == ax'.size
                  then
                    if ax'.size == ay.size
                    then
                      let sofar := go cx' cy 0 0
                      if match_nontrivial x y then Nat.succ sofar else sofar
                    else
                      let sofar := go cx' r 0 (or + com)
                      if match_nontrivial x y then Nat.succ sofar else sofar
                  else
                    if or + com == ay.size
                    then
                      let sofar := go (.node1 .none ax' cx') cy com 0
                      if match_nontrivial x y then Nat.succ sofar else sofar
                    else
                      if match_nontrivial x y then 1 else 0
        | .node y ay cy =>
              let hits := ByteArray.matchMulti ax ay
              let gone := hits.map
                (fun (ai,bi,com) =>
                  let A := ax.get! ai
                  let B := ay.get! bi
                    if com == A.size
                    then
                      if A.size == B.size
                      then
                        go (cx.get! ai) (cy.get! bi) 0 0
                      else
                        go (cx.get! ai) (.node1 .none B (cy.get! bi)) 0 com
                    else
                      if com == B.size
                      then
                        go (.node1 .none A (cx.get! ai)) (cy.get! bi) com 0
                      else
                        0
                  )
                let res := gone.foldl (fun z w => w+z) 0
                if match_nontrivial x y then Nat.succ res else res
  go l r 0 0



partial def SortedFrame [BEq α] [Repr α]
  (nonRec : Option α → Option α → β)
  (Rec : β → Option α → Option α → β)
  (RecMerge : List β → β) (MergeNoMatch : β)
  (l r : CTrie α) : β :=
  let rec go (l r : CTrie α) (ol or : Nat) : β :=
    match l with
    | .leaf x =>
        match r with
        | .leaf y => nonRec x y
        | .node1 y _ _ => nonRec x y
        | .node y _ _ => nonRec x y
    | .node1 x ax cx =>
        match r with
        | .leaf y => nonRec x y
        | .node1 y ay cy =>
              let com := ByteArray.getLongestMatch_wOffsets ax ay ol or
              if ol + com == ax.size
              then
                if ax.size == ay.size
                then
                  let sofar := go cx cy 0 0
                  Rec sofar x y
                else
                  let sofar := go cx r 0 (or + com)
                  Rec sofar x y
              else
                if or + com == ay.size
                then
                  let sofar := go l cy (ol + com) 0
                  Rec sofar x y
                else
                  nonRec x y
        | .node y ay cy =>
              match ByteArray.matchSingle_wOffset ax ol ay with
              | .none => nonRec x y
              | .some idx =>
                  let ay' := ay.get! idx
                  let cy' := cy.get! idx
                  -- sam as ↑
                  let com := ByteArray.getLongestMatch_wOffsets ax ay' ol 0
                  if ol + com == ax.size
                  then
                    if ax.size == ay'.size
                    then
                      let sofar := go cx cy' 0 0
                      Rec sofar x y
                    else
                      let sofar := go cx (.node1 .none ay' cy') 0 0
                      Rec sofar x y
                  else
                    if com == ay.size
                    then
                      let sofar := go l cy' (ol+com) 0
                      Rec sofar x y
                    else
                      nonRec x y
    | .node x ax cx =>
        match r with
        | .leaf y => nonRec x y
        | .node1 y ay cy =>
              match ByteArray.matchSingle_wOffset ay or ax with
              | .none => nonRec x y
              | .some idx =>
                  let ax' := ax.get! idx
                  let cx' := cx.get! idx
                  -- sam as ↑
                  let com := ByteArray.getLongestMatch_wOffsets ax' ay 0 or
                  if com == ax'.size
                  then
                    if ax'.size == ay.size
                    then
                      let sofar := go cx' cy 0 0
                      Rec sofar x y
                    else
                      let sofar := go cx' r 0 (or + com)
                      Rec sofar x y
                  else
                    if or + com == ay.size
                    then
                      let sofar := go (.node1 .none ax' cx') cy com 0
                      Rec sofar x y
                    else
                      nonRec x y
        | .node y ay cy =>
              let hits := ByteArray.matchMulti ax ay
              let gone := hits.map
                (fun (ai,bi,com) =>
                  let A := ax.get! ai
                  let B := ay.get! bi
                    if com == A.size
                    then
                      if A.size == B.size
                      then
                        go (cx.get! ai) (cy.get! bi) 0 0
                      else
                        go (cx.get! ai) (.node1 .none B (cy.get! bi)) 0 com
                    else
                      if com == B.size
                      then
                        go (.node1 .none A (cx.get! ai)) (cy.get! bi) com 0
                      else
                        MergeNoMatch
                  )
                let res := RecMerge gone
                Rec res x y
  go l r 0 0


def CountCommon' [BEq α] [Repr α] (l r : CTrie α) : Nat :=
  SortedFrame
    (fun x y => if match_nontrivial x y then 1 else 0)
    (fun sofar x y => if match_nontrivial x y then Nat.succ sofar else sofar)
    (fun gone =>  gone.foldl (fun z w => w+z) 0)
    (0)
    l r

def intersect_val [BEq α] [Repr α] (l r : CTrie α) : List (Option α) :=
  SortedFrame
    (fun x y => if match_nontrivial x y then [y] else [])
    (fun sofar x y => if match_nontrivial x y then [x] ++ sofar else sofar)
    (fun gone =>  gone.join)
    ([])
    l r



partial def intersect [BEq α] [Repr α] (l r : CTrie α) : CTrie α :=
  let rec go (l r : CTrie α) (ol or : Nat) : CTrie α :=
    match l with
    | .leaf x =>
        match r with
        | .leaf y => if match_nontrivial x y then .leaf y  else .leaf (.none)
        | .node1 y _ _ => if match_nontrivial x y then .leaf y  else .leaf (.none)
        | .node y _ _ => if match_nontrivial x y then .leaf y  else .leaf (.none)
    | .node1 x ax cx =>
        match r with
        | .leaf y => if match_nontrivial x y then .leaf y  else .leaf (.none)
        | .node1 y ay cy =>
              let com := ByteArray.getLongestMatch_wOffsets ax ay ol or
              if ol + com == ax.size
              then
                if ax.size == ay.size
                then
                  let sofar := go cx cy 0 0
                  if match_nontrivial x y then .node1 y ay sofar else .node1 .none ay sofar
                else
                  let sofar := go cx r 0 (or + com)
                  if match_nontrivial x y then .node1 x ax sofar else .node1 .none ax sofar
              else
                if or + com == ay.size
                then
                  let sofar := go l cy (ol + com) 0
                  if match_nontrivial x y then .node1 y ay sofar else .node1 .none ay sofar
                else
                  if match_nontrivial x y then .leaf y  else .leaf (.none)
        | .node y ay cy =>
              match ByteArray.matchSingle_wOffset ax ol ay with
              | .none => if match_nontrivial x y then .leaf y  else .leaf (.none)
              | .some idx =>
                  let ay' := ay.get! idx
                  let cy' := cy.get! idx
                  -- sam as ↑
                  let com := ByteArray.getLongestMatch_wOffsets ax ay' ol 0
                  if ol + com == ax.size
                  then
                    if ax.size == ay'.size
                    then
                      let sofar := go cx cy' 0 0
                      if match_nontrivial x y then .node1 x ax sofar else .node1 .none ax sofar
                    else
                      let sofar := go cx (.node1 .none ay' cy') 0 0
                      if match_nontrivial x y then .node1 x ax sofar else .node1 .none ax sofar
                  else
                    if com == ay.size
                    then
                      let sofar := go l cy' (ol+com) 0
                      if match_nontrivial x y then .node1 x ay' sofar else .node1 .none ay' sofar
                    else
                      if match_nontrivial x y then .leaf y  else .leaf (.none)
    | .node x ax cx =>
        match r with
        | .leaf y => if match_nontrivial x y then .leaf y  else .leaf (.none)
        | .node1 y ay cy =>
              match ByteArray.matchSingle_wOffset ay or ax with
              | .none => if match_nontrivial x y then .leaf y  else .leaf (.none)
              | .some idx =>
                  let ax' := ax.get! idx
                  let cx' := cx.get! idx
                  -- sam as ↑
                  let com := ByteArray.getLongestMatch_wOffsets ax' ay 0 or
                  if com == ax'.size
                  then
                    if ax'.size == ay.size
                    then
                      let sofar := go cx' cy 0 0
                      if match_nontrivial x y then .node1 x ax' sofar else .node1 .none ax' sofar
                    else
                      let sofar := go cx' r 0 (or + com)
                      if match_nontrivial x y then .node1 x ax' sofar else .node1 .none ax' sofar
                  else
                    if or + com == ay.size
                    then
                      let sofar := go (.node1 .none ax' cx') cy com 0
                      if match_nontrivial x y then .node1 x ay sofar else .node1 .none ay sofar
                    else
                      if match_nontrivial x y then .leaf y  else .leaf (.none)
        | .node y ay cy =>
              let hits := (ByteArray.matchMulti ax ay).reverse
              -- hits are decreasing, but we'll need them increasing
              --dbg_trace s!"{hits}"
              let gone := hits.map -- important that map preserves order
                (fun (ai,bi,com) =>
                  let A := ax.get! ai
                  let B := ay.get! bi
                    if com == A.size
                    then
                      if A.size == B.size
                      then
                        let sofar := go (cx.get! ai) (cy.get! bi) 0 0
                        (A, sofar)
                      else
                        let sofar := go (cx.get! ai) (.node1 .none B (cy.get! bi)) 0 com
                        (A, sofar)
                    else
                      if com == B.size
                      then
                        let sofar := go (.node1 .none A (cx.get! ai)) (cy.get! bi) com 0
                        (B, sofar)
                      else
                        ({}, .leaf .none)
                  )
                let (resA, resT) := (gone.filter (fun x => match x.2 with | .leaf .none => false | _ => true)).unzip
                if match_nontrivial x y then .node x resA.toArray resT.toArray else .node .none resA.toArray resT.toArray
  go l r 0 0


#eval [(1,'a'),(2,'b'),(3,'c')].unzip
#eval [1,2,3].toArray



partial def mergeMatchMulti (L R : Array ByteArray) (TL TR : Array (CTrie α)) (post : CTrie α → CTrie α → CTrie α) : (List ByteArray) × (List (CTrie α)) :=
  let rec go (l r : Nat) (doneB : List ByteArray) (doneT : List (CTrie α)) : (List ByteArray) × (List (CTrie α)) :=
    if (l < L.size)
    then
      if (r < R.size)
      then
        let a := L.get! l
        let b := R.get! r
        let com := ByteArray.getLongestMatch a b
          if com == 0
          then
            if a.get! 0 < b.get! 0
            then go (l+1) r (a :: doneB) ((TL.get! l) :: doneT)
            else go l (r+1) (b :: doneB) ((TR.get! r) :: doneT)
          else
            if com == a.size
            then
              if com == b.size
              then
                go (l+1) (r+1) (a :: doneB) (post (TL.get! l) (TR.get! r) :: doneT)
              else
                let b' := b.drop (com)
                go (l+1) (r+1) (a :: doneB) ((post (TL.get! l) (.node1 .none b' (TR.get! r))) :: doneT)
            else
              if com == b.size
              then
                let a' := a.drop (com)
                go (l+1) (r+1) (b :: doneB) ((post (.node1 .none a' (TL.get! l)) (TR.get! r)) :: doneT)
              else
                let join := a.take (com)
                let a' := a.drop (com)
                let b' := b.drop (com)
                if a.get! com < b.get! (com)
                then
                  go (l+1) (r+1) (join :: doneB) ((.node .none #[a',b'] #[(TL.get! l),(TR.get! r)]) :: doneT)
                else
                  go (l+1) (r+1) (join :: doneB) ((.node .none #[b',a'] #[(TR.get! r),(TL.get! l)]) :: doneT)
      else
        let a := L.get! l
        go (l+1) r (a :: doneB) ((TL.get! l) :: doneT)
    else
      if (r < R.size)
      then
        let b := R.get! r
        go l (r+1) (b :: doneB) ((TR.get! r) :: doneT)
      else
        (doneB, doneT)
  go 0 0  [] []



partial def merge [BEq α] [Inhabited α] (l r : CTrie α) : CTrie α  :=
  let mini_merge (x y : Option α) : Option α := (match x with | .some X => X | .none => match y with | .some Y => Y | .none => .none)
  -- so at common entries, the value from l is taken ! Maybe refactor where mini_merge can be any function ?
  let rec go (l r : CTrie α) (ol or : Nat) : CTrie α :=
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
              let com := ByteArray.getLongestMatch_wOffsets ax ay ol or
              if ol + com == ax.size
              then
                if ax.size == ay.size
                then
                  let sofar := go cx cy 0 0
                  .node1 (mini_merge x y) ax sofar
                else
                  let sofar := go cx (.node1 .none ay cy) 0 (or + com)
                  .node1 (mini_merge x y) ax sofar
              else
                if or + com == ay.size
                then
                  let sofar := go (.node1 .none ax cx) cy (ol + com) 0
                  .node1 (mini_merge x y) ay sofar
                else
                  let join := (ax.drop ol).take (com)
                  let ax' := ax.drop (ol + com)
                  let ay' := ay.drop (or + com)
                  if ax.get! (ol + com) < ay.get! (or + com)
                  then
                    .node1 (mini_merge x y) join (.node .none #[ax',ay'] #[cx,cy])
                  else
                    .node1 (mini_merge x y) join (.node .none #[ay',ax'] #[cy,cx])
        | .node y ay cy =>
              match ByteArray.matchSingleHits_wOffset ax ol ay with
              | .ins idx => .node (mini_merge x y) (ay.insertAt! idx ax) (cy.insertAt! idx cx)
              | .hit idx com =>
                  let ay' := ay.get! idx
                  let cy' := cy.get! idx
                  if ol + com == ax.size
                  then
                    if ax.size == ay'.size
                    then
                      let sofar := go cx cy' 0 0
                      .node (mini_merge x y) ay (cy.set! idx sofar)
                    else
                      let sofar := go cx (.node1 .none ay' cy') 0 com
                      .node (mini_merge x y) (ay.set! idx ax) (cy.set! idx sofar)
                  else
                    if com == ay'.size
                    then
                      let sofar := go l cy' (ol + com) 0
                      .node (mini_merge x y) ay (cy.set! idx sofar)
                    else
                      let join := (ax.drop ol).take (com)
                      let ax' := ax.drop (ol + com)
                      let ay'' := ay'.drop (com)
                      if ax.get! (ol + com) < ay'.get! (com)
                      then
                        .node (mini_merge x y) (ay.set! idx join) (cy.set! idx (.node .none #[ax',ay''] #[cx,cy']))
                      else
                        .node (mini_merge x y) (ay.set! idx join) (cy.set! idx (.node .none #[ay'',ax'] #[cy',cx]))
    | .node x ax cx =>
        match r with
        | .leaf y => .node (mini_merge x y) ax cx
        | .node1 y ay cy =>
              match ByteArray.matchSingleHits_wOffset ay or ax with
              | .ins idx => .node (mini_merge x y) (ax.insertAt! idx ay) (cx.insertAt! idx cy)
              | .hit idx com =>
                  let ax' := ax.get! idx
                  let cx' := cx.get! idx
                  if or + com == ay.size
                  then
                    if ay.size == ax'.size
                    then
                      let sofar := go cx' cy 0 0
                      .node (mini_merge x y) ax (cx.set! idx sofar)
                    else
                      let sofar := go (.node1 .none ax' cx') cy com 0
                      .node (mini_merge x y) (ax.set! idx ay) (cx.set! idx sofar)
                  else
                    if com == ax'.size
                    then
                      let sofar := go cx' r 0 com
                      .node (mini_merge x y) ax (cx.set! idx sofar)
                    else
                      let join := (ay.drop or).take (com)
                      let ay' := ay.drop (or + com)
                      let ax'' := ax'.drop (com)
                      if ax'.get! com < ay.get! (or + com)
                      then
                        .node (mini_merge x y) (ax.set! idx join) (cx.set! idx (.node .none #[ax'',ay'] #[cx',cy]))
                      else
                        .node (mini_merge x y) (ax.set! idx join) (cx.set! idx (.node .none #[ay',ax''] #[cy,cx']))
        | .node y ay cy =>
            let (as, ts) := mergeMatchMulti ax ay cx cy (go · · 0 0)
            .node (mini_merge x y) (as.reverse.toArray) (ts.reverse.toArray)
  go l r 0 0


#check Array.insertAt!

-- previously "filter"
partial def difference [BEq α] [Inhabited α] (l r : CTrie α) : CTrie α :=
  let rec go (l r : CTrie α) (ol or : Nat) : CTrie α :=
    match l with
    | .leaf x =>
        match r with
        | .leaf y => if match_nontrivial x y then .leaf .none  else .leaf x
        | .node1 y _ _ => if match_nontrivial x y then .leaf .none  else .leaf x
        | .node y _ _ => if match_nontrivial x y then .leaf .none  else .leaf x
    | .node1 x ax cx =>
        match r with
        | .leaf y => if match_nontrivial x y then .node1 .none ax cx  else .node1 x ax cx
        | .node1 y ay cy =>
              let com := ByteArray.getLongestMatch_wOffsets ax ay ol or
              if ol + com == ax.size
              then
                if ax.size == ay.size
                then
                  let sofar := go cx cy 0 0
                  if match_nontrivial x y then .node1 .none ax sofar else .node1 x ax sofar
                else
                  let sofar := go cx (.node1 .none ay cy) 0 (or + com)
                  if match_nontrivial x y then .node1 .none ax sofar else .node1 x ax sofar
              else
                if or + com == ay.size
                then
                  let sofar := go (.node1 .none ax cx) cy (ol + com) 0
                  if match_nontrivial x y then .node1 .none ay sofar else .node1 x ay sofar
                else
                  if match_nontrivial x y then .node1 .none ax cx  else .node1 x ax cx
        | .node y ay cy =>
              match ByteArray.matchSingle_wOffset ax ol ay with
              | .none => if match_nontrivial x y then .node1 .none ax cx  else .node1 x ax cx
              | .some idx =>
                  let ay' := ay.get! idx
                  let cy' := cy.get! idx
                  let com := ByteArray.getLongestMatch_wOffsets ax ay' ol or
                  if ol + com == ax.size
                  then
                    if ax.size == ay'.size
                    then
                      let sofar := go cx cy' 0 0
                      if match_nontrivial x y then .node1 .none ax sofar else .node1 x ax sofar
                    else
                      let sofar := go cx (.node1 .none ay' cy') 0 (or + com)
                      if match_nontrivial x y then .node1 .none ax sofar else .node1 x ax sofar
                  else
                    if or + com == ay.size
                    then
                      let sofar := go (.node1 .none ax cx) cy' (ol + com) 0
                      if match_nontrivial x y then .node1 .none ay' sofar else .node1 x ay' sofar
                    else
                      if match_nontrivial x y then .node1 .none ax cx  else .node1 x ax cx
    | .node x ax cx =>
        match r with
        | .leaf y => if match_nontrivial x y then .node .none ax cx  else .node x ax cx
        | .node1 y ay cy =>
              match ByteArray.matchSingle_wOffset ay or ax with
              | .none => if match_nontrivial x y then .node .none ax cx  else .node x ax cx
              | .some idx =>
                    let ax' := ax.get! idx
                    let cx' := cx.get! idx
                    let com := ByteArray.getLongestMatch_wOffsets ax' ay ol or
                    if ol + com == ax'.size
                    then
                      if ax'.size == ay.size
                      then
                        let sofar := go cx' cy 0 0
                        if match_nontrivial x y then .node .none ax (cx.set! idx sofar) else .node x ax (cx.set! idx sofar)
                      else
                        let sofar := go cx' (.node1 .none ay cy) 0 (or + com)
                        if match_nontrivial x y then .node .none ax (cx.set! idx sofar) else .node x ax (cx.set! idx sofar)
                    else
                      if or + com == ay.size
                      then
                        let sofar := go (.node1 .none ax' cx') cy (ol + com) 0
                        match sofar with
                        | .node1 .none _ ncx =>
                            if match_nontrivial x y then .node .none ax (cx.set! idx ncx) else .node x ax (cx.set! idx ncx)
                        | _ => .leaf .none  -- failure!
                      else
                        if match_nontrivial x y then .node .none ax cx  else .node x ax cx
        | .node y ay cy =>
              let hits := (ByteArray.matchMulti ax ay).reverse
              let gone := hits.map
                (fun (ai,bi,com) =>
                  let A := ax.get! ai
                  let B := ay.get! bi
                    if com == A.size
                    then
                      if A.size == B.size
                      then
                        let sofar := go (cx.get! ai) (cy.get! bi) 0 0
                        (ai,sofar)
                      else
                        let sofar := go (cx.get! ai) (.node1 .none B (cy.get! bi)) 0 com
                        (ai,sofar)
                    else
                      if com == B.size
                      then
                        let sofar := go (.node1 .none A (cx.get! ai)) (cy.get! bi) (com) 0
                        match sofar with
                        | .node1 .none _ ncx => (ai,ncx)
                        | _ => (ai,.leaf .none)  -- failure!
                      else
                        (ai,(cx.get! ai))
                )
              let rec update (C : Array (CTrie α)) :  List (Nat × CTrie α) →  Array (CTrie α)
                | [] => C
                | (li, new) :: more => update (C.set! li new) more
              if match_nontrivial x y then .node .none ax (update cx gone)  else .node x ax (update cx gone)
  go l r 0 0

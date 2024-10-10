
import LeanGrow.F.Utils.ExprTrie.Types
import LeanGrow.F.Utils.List
import LeanGrow.F.Utils.Tracing

open Lean



def CExprTrie.empty {α : Type _} : CExprTrie α  := [(0,[])]


def CExprTrie.size : CExprTrie α → Nat := List.length

def CExprTrie.modifyAtLink (T : CExprTrie α ) (link : Nat) (modify : List (CExprTrie.Branch α)  → List (CExprTrie.Branch α )) : CExprTrie α :=
  List.findModify (fun p => p.1 == link) (fun (l,b) => (l, modify b)) T


def CExprTrie.modifyAtLink_withEffects [Inhabited α] (T : CExprTrie α) (link : Nat) (modify : List (CExprTrie.Branch α) → α × List (CExprTrie.Branch α)) : α × CExprTrie α :=
  let rec help : List (Nat × List (CExprTrie.Branch α)) → α × CExprTrie α
  | [] => (default, [])
  | (t, lb) :: L =>
        if t == link
        then
          let (res, new) := (modify lb)
          (res, (t,new) :: L)
        else
          let (res, new) := help L
          (res, (t, lb) :: new)
  help T

def CExprTrie.getAtLink (T : CExprTrie α) (link : Nat) :  List (CExprTrie.Branch α) :=
  match List.find? (fun p => p.1 == link) T with
  | .some lb => lb.2
  | _ => []



def CExprTrie.Branch_getAppLinks? : List (CExprTrie.Branch α) → Option (Nat × Nat)
| [] => .none
| x :: l =>
    match x with
    | .ofApp lf la => .some (lf,la)
    | _ => CExprTrie.Branch_getAppLinks? l


def CExprTrie.Branch_getLamLinks? : List (CExprTrie.Branch α) → Option (Nat × Nat)
| [] => .none
| x :: l =>
    match x with
    | .ofLam _ lf la _ => .some (lf,la)
    | _ => CExprTrie.Branch_getLamLinks? l

def CExprTrie.Branch_getForallLinks? : List (CExprTrie.Branch α) → Option (Nat × Nat)
| [] => .none
| x :: l =>
    match x with
    | .ofForall _ lf la _ => .some (lf,la)
    | _ => CExprTrie.Branch_getForallLinks? l

def CExprTrie.Branch_getLetLinks? : List (CExprTrie.Branch α) → Option (Nat × Nat × Nat)
| [] => .none
| x :: l =>
    match x with
    | .ofLet _ lf la lz _ => .some (lf,la,lz)
    | _ => CExprTrie.Branch_getLetLinks? l


def CExprTrie.Branch_getProjLinks? : List (CExprTrie.Branch α) → Option (Nat)
| [] => .none
| x :: l =>
    match x with
    | .ofProj _ _ l => .some l
    | _ => CExprTrie.Branch_getProjLinks? l

def CExprTrie.modifyAsLeaf_Lit [BEq α] (l : Literal) (idx : α) (r : α → α → Prop) [DecidableRel r]  : List (CExprTrie.Branch α) → List (CExprTrie.Branch α)
| [] => [.ofLit l [idx]]
| x :: xs =>
    match x with
    | .ofLit L ind =>
        if L == l
        then (.ofLit L (List.orderedInsertOrLeave r idx ind)) :: xs
        else (.ofLit L ind) :: (CExprTrie.modifyAsLeaf_Lit l idx r xs)
    | _ => x :: (CExprTrie.modifyAsLeaf_Lit l idx r xs)



def CExprTrie.modifyAsLeaf_Node [BEq α]  (l : Nat) (idx : α) (r : α → α → Prop) [DecidableRel r] : List (CExprTrie.Branch α) → List (CExprTrie.Branch α)
| [] => [.ofNode l [idx]]
| x :: xs =>
    match x with
    | .ofNode L ind =>
        if L == l
        then (.ofNode L (List.orderedInsertOrLeave r idx ind)) :: xs
        else (.ofNode L ind) :: (CExprTrie.modifyAsLeaf_Node l idx r xs)
    | _ => x :: (CExprTrie.modifyAsLeaf_Node l idx r xs)


def CExprTrie.modifyAsLeaf_Bvar [BEq α]  (l : Nat) (idx : α) (r : α → α → Prop) [DecidableRel r] : List (CExprTrie.Branch α) → List (CExprTrie.Branch α)
| [] => [.ofBvar l [idx]]
| x :: xs =>
    match x with
    | .ofBvar L ind =>
        if L == l
        then (.ofBvar L (List.orderedInsertOrLeave r idx ind)) :: xs
        else (.ofBvar L ind) :: (CExprTrie.modifyAsLeaf_Bvar l idx r xs)
    | _ => x :: (CExprTrie.modifyAsLeaf_Bvar l idx r xs)

def CExprTrie.modifyAsLeaf_Sort [BEq α]  (l : Level) (idx : α) (r : α → α → Prop) [DecidableRel r] : List (CExprTrie.Branch α) → List (CExprTrie.Branch α)
| [] => [.ofSort l [idx]]
| x :: xs =>
    match x with
    | .ofSort L ind =>
        if L == l
        then (.ofSort L (List.orderedInsertOrLeave r idx ind)) :: xs
        else (.ofSort L ind) :: (CExprTrie.modifyAsLeaf_Sort l idx r xs)
    | _ => x :: (CExprTrie.modifyAsLeaf_Sort l idx r xs)

def CExprTrie.modifyAsLeaf_Const [BEq α] (n : Name) (idx : α) (r : α → α → Prop) [DecidableRel r] : List (CExprTrie.Branch α) → List (CExprTrie.Branch α)
| [] => [.ofConst n [idx]]
| x :: xs =>
    match x with
    | .ofConst L ind =>
        if L == n
        then (.ofConst L (List.orderedInsertOrLeave r idx ind)) :: xs
        else (.ofConst L ind) :: (CExprTrie.modifyAsLeaf_Const n idx r xs)
    | _ => x :: (CExprTrie.modifyAsLeaf_Const n idx r xs)




-- TODO: make more efficient
def CExprTrie.insert [BEq α] (T : CExprTrie α) (idx : α) (ce : CExpr) (r : α → α → Prop) [DecidableRel r] : CExprTrie α :=
  let rec go (T : CExprTrie α ) (idx : α) (link count : Nat) : CExpr → (Nat × CExprTrie α)
    | .failed => (count, T)
    | .app f a =>
            let lb := CExprTrie.getAtLink T link
            let links? := CExprTrie.Branch_getAppLinks? lb
            match links? with
            | .some (lf,la) =>
                  let (swf,twf) := go T idx lf count f
                  go twf idx la swf a
            | _ =>
                  let nlb := (.ofApp (count) (count+1)) :: lb
                  let nT1 := CExprTrie.modifyAtLink T link (fun _ => nlb)
                  let (ns, nT2) := go ((count, []) :: nT1) idx count (count+2) f
                  go (((count+1), []) :: nT2) idx (count+1) ns a
    | .lam n f a i =>
            let lb := CExprTrie.getAtLink T link
            let links? := CExprTrie.Branch_getLamLinks? lb
            match links? with
            | .some (lf,la) =>
                  let (swf,twf) := go T idx lf count f
                  go twf idx la swf a
            | _ =>
                  let nlb := (.ofLam n (count) (count+1) i) :: lb
                  let nT1 := CExprTrie.modifyAtLink T link (fun _ => nlb)
                  let (ns, nT2) := go ((count, []) :: nT1) idx count (count+2) f
                  go (((count+1), []) :: nT2) idx (count+1) ns a
    | .forallE n f a i =>
            let lb := CExprTrie.getAtLink T link
            let links? := CExprTrie.Branch_getForallLinks? lb
            match links? with
            | .some (lf,la) =>
                  let (swf,twf) := go T idx lf count f
                  go twf idx la swf a
            | _ =>
                  let nlb := (.ofForall n (count) (count+1) i) :: lb
                  let nT1 := CExprTrie.modifyAtLink T link (fun _ => nlb)
                  let (ns, nT2) := go ((count, []) :: nT1) idx count (count+2) f
                  go (((count+1), []) :: nT2) idx (count+1) ns a
    | .letE n f a z i =>
            let lb := CExprTrie.getAtLink T link
            let links? := CExprTrie.Branch_getLetLinks? lb
            match links? with
            | .some (lf,la,lz) =>
                  let (swf,twf) := go T idx lf count f
                  let (swa,twa) := go twf idx la swf a
                  go twa idx lz swa z
            | _ =>
                  let nlb := (.ofLet n (count) (count+1) (count+2) i) :: lb
                  let nT1 := CExprTrie.modifyAtLink T link (fun _ => nlb)
                  let (ns1, nT2) := go ((count, []) :: nT1) idx count (count+3) f
                  let (ns2, nT3) := go ((count+1, []) :: nT2) idx (count+1) ns1 a
                  go ((count+2, []) :: nT3) idx (count+2) ns2 z
    | .proj n i e =>
            let lb := CExprTrie.getAtLink T link
            let links? := CExprTrie.Branch_getProjLinks? lb
            match links? with
            | .some l => go T idx l count e
            | _ =>
                  let nlb := (.ofProj n i (count)) :: lb
                  let nT1 := CExprTrie.modifyAtLink T link (fun _ => nlb)
                  go ((count, []) :: nT1) idx count (count+1) e
    | .lit l =>
            let lb := CExprTrie.getAtLink T link
            let nlb := CExprTrie.modifyAsLeaf_Lit l idx r lb
            (count, CExprTrie.modifyAtLink T link (fun _ => nlb))
    | .node l _ =>
            let lb := CExprTrie.getAtLink T link
            let nlb := CExprTrie.modifyAsLeaf_Node l idx r lb
            (count, CExprTrie.modifyAtLink T link (fun _ => nlb))
    | .bvar l =>
            let lb := CExprTrie.getAtLink T link
            let nlb := CExprTrie.modifyAsLeaf_Bvar l idx r lb
            (count, CExprTrie.modifyAtLink T link (fun _ => nlb))
    | .sort l =>
            let lb := CExprTrie.getAtLink T link
            let nlb := CExprTrie.modifyAsLeaf_Sort l idx r lb
            (count, CExprTrie.modifyAtLink T link (fun _ => nlb))
    | .const l _ =>
            let lb := CExprTrie.getAtLink T link
            let nlb := CExprTrie.modifyAsLeaf_Const l idx r lb
            (count, CExprTrie.modifyAtLink T link (fun _ => nlb))
  (go T idx 0 T.size ce).2


def CExprTrie.ofList [BEq α] (r : α → α → Prop) [DecidableRel r] (L : List (α × CExpr)) : CExprTrie α :=
  L.foldl (fun T (idx,ce) => CExprTrie.insert T idx ce r) CExprTrie.empty


def test_list : List (Nat × CExpr) :=
  [(1, .app (.app (.const `a []) (.const `b [])) (.const `c [])),
   (4, .app (.app (.const `a []) (.const `b [])) (.const `d [])),
   (42, .app (.app (.const `a []) (.const `e [])) (.const `c [])),
   (37, .forallE `dummy (.const `x []) (.const `y []) .default)
  ]

-- #eval CExprTrie.ofList (· ≤ ·) test_list




def CExprTrie.getIndices_Lit (l : Literal) : List (CExprTrie.Branch α) → List α
| [] => []
| x :: xs =>
    match x with
    | .ofLit L ind =>
        if L == l
        then ind
        else (CExprTrie.getIndices_Lit l  xs)
    | _ => (CExprTrie.getIndices_Lit l  xs)

def CExprTrie.getIndices_Node (l : Nat) : List (CExprTrie.Branch α) → List α
| [] => []
| x :: xs =>
    match x with
    | .ofNode L ind =>
        if L == l
        then ind
        else (CExprTrie.getIndices_Node l xs)
    | _ => (CExprTrie.getIndices_Node l xs)


def CExprTrie.getIndices_Bvar (l : Nat) : List (CExprTrie.Branch α) → List α
| [] => []
| x :: xs =>
    match x with
    | .ofBvar L ind =>
        if L == l
        then ind
        else (CExprTrie.getIndices_Bvar l xs)
    | _ => (CExprTrie.getIndices_Bvar l xs)


def CExprTrie.getIndices_Sort (l : Level) : List (CExprTrie.Branch α) → List α
| [] => []
| x :: xs =>
    match x with
    | .ofSort L ind =>
        if L == l
        then ind
        else (CExprTrie.getIndices_Sort l xs)
    | _ => (CExprTrie.getIndices_Sort l xs)


def CExprTrie.getIndices_Const (l : Name) : List (CExprTrie.Branch α) → List α
| [] => []
| x :: xs =>
    match x with
    | .ofConst L ind =>
        if L == l
        then ind
        else (CExprTrie.getIndices_Const l xs)
    | _ => (CExprTrie.getIndices_Const l xs)


partial def CExprTrie.find_candidates? [BEq α] (T : CExprTrie α) (ce : CExpr) (r : α → α → Prop) [DecidableRel r] : List (List α) :=
  let rec go (done : List (List α)) : List (CExpr × Nat) → List (List α)
    | [] => done
    | (nx, link) :: more =>
        match nx with
        | .failed => []
        | .app f a =>
            let lb := CExprTrie.getAtLink T link
            let links? := CExprTrie.Branch_getAppLinks? lb
            match links? with
            | .some (lf,la) => go done ((f, lf) :: (a, la) :: more)
            | _ => []
        | .lam _ f a _ =>
            let lb := CExprTrie.getAtLink T link
            let links? := CExprTrie.Branch_getLamLinks? lb
            match links? with
            | .some (lf,la) => go done ((f, lf) :: (a, la) :: more)
            | _ => []
        | .forallE _ f a _ =>
            let lb := CExprTrie.getAtLink T link
            let links? := CExprTrie.Branch_getForallLinks? lb
            match links? with
            | .some (lf,la) => go done ((f, lf) :: (a, la) :: more)
            | _ => []
        | .letE _ f a z _ =>
            let lb := CExprTrie.getAtLink T link
            let links? := CExprTrie.Branch_getLetLinks? lb
            match links? with
            | .some (lf,la,lz) => go done ((f, lf) :: (a, la) :: (z, lz) :: more)
            | _ => []
        | .proj _ _ e =>
            let lb := CExprTrie.getAtLink T link
            let links? := CExprTrie.Branch_getProjLinks? lb
            match links? with
            | .some (le) => go done ((e, le) :: more)
            | _ => []
        | .lit l =>
            let lb := CExprTrie.getAtLink T link
            let nlb := CExprTrie.getIndices_Lit l lb
            go (nlb :: done) more
        | .node l _ =>
            let lb := CExprTrie.getAtLink T link
            let nlb := CExprTrie.getIndices_Node l lb
            go (nlb :: done) more
        | .bvar l =>
            let lb := CExprTrie.getAtLink T link
            let nlb := CExprTrie.getIndices_Bvar l lb
            go (nlb :: done) more
        | .sort l =>
            let lb := CExprTrie.getAtLink T link
            let nlb := CExprTrie.getIndices_Sort l lb
            go (nlb :: done) more
        | .const l _ =>
            let lb := CExprTrie.getAtLink T link
            let nlb := CExprTrie.getIndices_Const l lb
            go (nlb :: done) more
  go [] [(ce,0)]


-- #eval CExprTrie.find_candidates? (CExprTrie.ofList (· ≤ ·) test_list) (.app (.app (.const `a []) (.const `e [])) (.const `c [])) (· ≤ ·)


def CExprTrie.find? [BEq α] (T : CExprTrie α) (ce : CExpr) (r : α → α → Prop) [DecidableRel r] : List α :=
  let cand := CExprTrie.find_candidates? T ce r
  match cand with
  | [] => []
  | h :: t => t.foldl (fun x y => List.orderedIntersect r x y ) h


-- #eval CExprTrie.find? (CExprTrie.ofList (· ≤ ·) test_list) (.app (.app (.const `a []) (.const `e [])) (.const `c [])) (· ≤ ·)


-- TODO : make more efficient
partial def CExprTrie.buildAtLink [BEq α] [Repr α] (T : CExprTrie α) (link : Nat) (r : α → α → Prop) [DecidableRel r] : List (CExpr × List α) :=
  with_lTrace TraceFlags.off in
  let lb := CExprTrie.getAtLink T link
  let rec go : CExprTrie.Branch α → List (CExpr × List α)
    | .ofFailed => []
    | .ofApp lf la =>
          let fs := CExprTrie.buildAtLink T lf r
          let as := CExprTrie.buildAtLink T la r
          let res :=
            (fs.foldl (fun x y =>
              (as.foldl (fun X Y =>
                let inter := List.orderedIntersect r y.2 Y.2
                match inter with
                | [] => X
                | _ => (.app y.1 Y.1, inter) :: X
                )
                []) :: x
              )
              []).join
          lTrace TraceFlags.zero & s!"Building apps:\n{repr res}\n\n" & res
    | .ofLam n lf la i =>
          let fs := CExprTrie.buildAtLink T lf r
          let as := CExprTrie.buildAtLink T la r
          let res :=
            (fs.foldl (fun x y =>
              (as.foldl (fun X Y =>
                let inter := List.orderedIntersect r y.2 Y.2
                match inter with
                | [] => X
                | _ => (.lam n y.1 Y.1 i, inter) :: X
                )
                []) :: x
              )
              []).join
          lTrace TraceFlags.zero & s!"Building lams:\n{repr res}\n\n" & res
    | .ofForall n lf la i =>
          let fs := CExprTrie.buildAtLink T lf r
          let as := CExprTrie.buildAtLink T la r
          let res :=
            (fs.foldl (fun x y =>
              (as.foldl (fun X Y =>
                let inter := List.orderedIntersect r y.2 Y.2
                match inter with
                | [] => X
                | _ => (.lam n y.1 Y.1 i, inter) :: X
                )
                []) :: x
              )
              []).join
            lTrace TraceFlags.zero & s!"Building foalls:\n{repr res}\n\n" & res
    | .ofLet n lf la lz i =>
          let fs := CExprTrie.buildAtLink T lf r
          let as := CExprTrie.buildAtLink T la r
          let zs := CExprTrie.buildAtLink T lz r
          let res :=
            (fs.foldl (fun x y =>
              (as.foldl (fun X Y =>
                (zs.foldl (fun z Z =>
                  let interim := List.orderedIntersect r y.2 Y.2
                  let inter := List.orderedIntersect r Z.2 interim
                  match inter with
                  | [] => z
                  | _ => (.letE n y.1 Y.1 Z.1 i, inter) :: z
                  )
                []) :: X
                )
                []).join :: x
              )
              []).join
          lTrace TraceFlags.zero & s!"Building lets:\n{repr res}\n\n" & res
    | .ofProj n i le =>
          let es := CExprTrie.buildAtLink T le r
          let res := es.map (fun (ce,inter) => (.proj n i ce,inter))
          lTrace TraceFlags.zero & s!"Building proj:\n{repr res}\n\n" & res
    |.ofLit l ind =>
          let res := [(.lit l, ind)]
          lTrace TraceFlags.zero & s!"Building lit:\n{repr res}\n\n" & res
    |.ofNode l ind =>
          let res := [(.node l (.ofBvar 42), ind)] --fix
          lTrace TraceFlags.zero & s!"Building lit:\n{repr res}\n\n" & res
    |.ofBvar l ind =>
          let res := [(.bvar l , ind)]
          lTrace TraceFlags.zero & s!"Building lit:\n{repr res}\n\n" & res
    |.ofSort l ind =>
          let res := [(.sort l , ind)]
          lTrace TraceFlags.zero & s!"Building lit:\n{repr res}\n\n" & res
    |.ofConst l ind =>
          let res := [(.const l [], ind)] -- fix
          lTrace TraceFlags.zero & s!"Building lit:\n{repr res}\n\n" & res
  (lb.foldl (fun x y => (go y) :: x) []).join


-- #eval CExprTrie.buildAtLink (CExprTrie.ofList (· ≤ ·) test_list) 0 (· ≤ ·)


partial def CExprTrie.unify_candidates [BEq α] [Repr α] (T : CExprTrie α) (r : α → α → Prop) [DecidableRel r] (ce : CExpr) : List (Nat × List (CExpr × List α)) :=
  let rec go (done : List (Nat × List (CExpr × List α))) : List (CExpr × Nat) → List (Nat × List (CExpr × List α))
    | [] => done
    | (nx, link) :: more =>
        match nx with
        | .failed => []
        | .app f a =>
            let lb := CExprTrie.getAtLink T link
            let links? := CExprTrie.Branch_getAppLinks? lb
            match links? with
            | .some (lf,la) => go done ((f, lf) :: (a, la) :: more)
            | _ => []
        | .lam _ f a _ =>
            let lb := CExprTrie.getAtLink T link
            let links? := CExprTrie.Branch_getLamLinks? lb
            match links? with
            | .some (lf,la) => go done ((f, lf) :: (a, la) :: more)
            | _ => []
        | .forallE _ f a _ =>
            let lb := CExprTrie.getAtLink T link
            let links? := CExprTrie.Branch_getForallLinks? lb
            match links? with
            | .some (lf,la) => go done ((f, lf) :: (a, la) :: more)
            | _ => []
        | .letE _ f a z _ =>
            let lb := CExprTrie.getAtLink T link
            let links? := CExprTrie.Branch_getLetLinks? lb
            match links? with
            | .some (lf,la,lz) => go done ((f, lf) :: (a, la) :: (z, lz) :: more)
            | _ => []
        | .proj _ _ e =>
            let lb := CExprTrie.getAtLink T link
            let links? := CExprTrie.Branch_getProjLinks? lb
            match links? with
            | .some (le) => go done ((e, le) :: more)
            | _ => []
        | .lit l =>
            let lb := CExprTrie.getAtLink T link
            let nlb := CExprTrie.getIndices_Lit l lb
            match nlb with
            | [] => []
            | _ => go (done) more
        | .node l _ =>
            let builds := CExprTrie.buildAtLink T link r
            go ((l, builds) :: done) more
        | .bvar l =>
            let lb := CExprTrie.getAtLink T link
            let nlb := CExprTrie.getIndices_Bvar l lb
            match nlb with
            | [] => []
            | _ => go (done) more
        | .sort l =>
            let lb := CExprTrie.getAtLink T link
            let nlb := CExprTrie.getIndices_Sort l lb
            match nlb with
            | [] => []
            | _ => go (done) more
        | .const l _ =>
            let lb := CExprTrie.getAtLink T link
            let nlb := CExprTrie.getIndices_Const l lb
            match nlb with
            | [] => []
            | _ => go (done) more
  go [] [(ce,0)]

#eval CExprTrie.unify_candidates (CExprTrie.ofList (· ≤ ·) test_list) (· ≤ ·) (.app (.node 0 (.ofBvar 42)) (.node 1 (.ofBvar 42)))

-- #eval CExprTrie.uniunify_candidatesfy (CExprTrie.ofList (· ≤ ·) test_list) (· ≤ ·) (.forallE `dummy (.node 0 (.ofBvar 42)) (.node 1 (.ofBvar 42)) .default)

-- #eval CExprTrie.unify_candidates (CExprTrie.ofList (· ≤ ·) test_list) (· ≤ ·) (.node 0 (.ofBvar 42))

-- #eval CExprTrie.unify_candidates (CExprTrie.ofList (· ≤ ·) test_list) (· ≤ ·) (.const `nope [])

/-
TODO:

To reconstruct unification candidates, proceed as follows:
go over list & over indices ; for each, index maintain an apriori embedding (ad new one when new index encountered) ;
that embedding will store assignements of node indices to CExpre (use arrays ??) ;

In the example of the first eval above, start by building an apriori unification with 4, where 1 would be `d`.
Then build two apriori unification with 1 and 42, where 1 would be `d`.
Then modify the a priori embeddings at 1 and 4 where we set 0 to `a b`.
And so one. If conflicts arise, give up on the embedding at the index entirely ...

-/

def CExprTrie.unify_reconstruct [BEq α] [Repr α] (r : α → α → Prop) [DecidableRel r] (candidates : List (Nat × List (CExpr × List α))) : List (α × List (Nat × CExpr)) :=
    let rec go (node_idx : Nat) (sofar : List (α × List (Nat × CExpr))) : List (CExpr × List α) → List (α × List (Nat × CExpr))
        | [] => sofar
        | (assign, ind) :: rest =>
                let step := ind.foldl (fun out i => List.findModifyAdd (fun x => x.1 == i) (fun (idx, matchInfo) => (idx, (node_idx,assign) :: matchInfo)) (i, [(node_idx,assign)]) out) sofar
                go node_idx step rest
    candidates.foldl (fun out (node_idx, assign_data) => go node_idx out assign_data) []


#eval CExprTrie.unify_reconstruct (· ≤ ·) (CExprTrie.unify_candidates (CExprTrie.ofList (· ≤ ·) test_list) (· ≤ ·) (.app (.node 0 (.ofBvar 42)) (.node 1 (.ofBvar 42))))

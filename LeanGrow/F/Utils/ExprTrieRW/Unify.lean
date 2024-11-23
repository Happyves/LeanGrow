
import LeanGrow.F.Utils.ExprTrieRW.Query
import LeanGrow.F.Utils.ExprTrieRW.RWclasses
import LeanGrow.F.Utils.ExprTrieRW.DeleteOcc

import Mathlib.Data.List.Basic

open Lean


/-

Should proceed as in `Query.lean`. The difference will be at untagged lnodes.
To build a try with RW branches, we should, when encountering an RW branch, build
the CExprTrie of the class (which may itself contain RW branches).
There may be exponential growths in the number of terms considered here, but it is a necessity.

We should add a format for construction. This isn't the RWblueprint, as we're not matching the
untaged lnode to an expression, but a build-blueprint. In the non-rw context, we ended up with
a list of pair of indices of terms of the trie, together with a list representing the correspondece
of the pos-index of the lnode and the cexpr we may replace it with in the context of unification.
Now instead of a cexpr to replace the lnode with, we should have a list of CExpr, together with
some format on how they were obtained from rewrites. This should also be recorded in the
embedding data, as we'll need it when assembling the terms (note that we should build only
in the end, once we know which rewrites were actually needed in the proof)
-/

def List.dedup_beq [BEq α] : List α → List α :=
  pwFilter (fun a b => !(a == b))



inductive rwExpr (α : Sort _) where
| ofAtom (_ : CExpr)
| wRW (classId entryId : Nat) (ind : List α) (build : rwExpr α)
| app (_ : rwExpr α) (_ : rwExpr α)
| lam (n : Name) (_ : rwExpr α) (_ : rwExpr α) (i : BinderInfo)
| forallE (n : Name) (_ : rwExpr α) (_ : rwExpr α) (i : BinderInfo)
| letE (n : Name) (_ : rwExpr α) (_ : rwExpr α) (_ : rwExpr α) (i : Bool)
| proj (n : Name) (idx : Nat) (_ : rwExpr α)
deriving Inhabited, Repr, BEq



-- TODO : make more efficient
partial def CExprTrie.buildAtLink [BEq α] [Repr α] (T : CExprTrie α) (link : Nat) (r : α → α → Prop) [DecidableRel r]
  (classes : List (Nat × CExprTrie α)) : List (rwExpr α × List α) :=
  with_lTrace TraceFlags.off in
  let lb := CExprTrie.getAtLink T link
  let rec go : CExprTrie.Branch α → List (rwExpr α × List α)
    | .ofFailed => []
    | .ofApp lf la =>
          let fs := CExprTrie.buildAtLink T lf r classes
          let as := CExprTrie.buildAtLink T la r classes
          dbg_trace s!"fs : {repr fs}\nas : {repr as}"
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
          let fs := CExprTrie.buildAtLink T lf r classes
          let as := CExprTrie.buildAtLink T la r classes
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
          let fs := CExprTrie.buildAtLink T lf r classes
          let as := CExprTrie.buildAtLink T la r classes
          let res :=
            (fs.foldl (fun x y =>
              (as.foldl (fun X Y =>
                let inter := List.orderedIntersect r y.2 Y.2
                match inter with
                | [] => X
                | _ => (.forallE n y.1 Y.1 i, inter) :: X
                )
                []) :: x
              )
              []).join
            lTrace TraceFlags.zero & s!"Building foalls:\n{repr res}\n\n" & res
    | .ofLet n lf la lz i =>
          let fs := CExprTrie.buildAtLink T lf r classes
          let as := CExprTrie.buildAtLink T la r classes
          let zs := CExprTrie.buildAtLink T lz r classes
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
          let es := CExprTrie.buildAtLink T le r classes
          let res := es.map (fun (ce,inter) => (.proj n i ce,inter))
          lTrace TraceFlags.zero & s!"Building proj:\n{repr res}\n\n" & res
    |.ofLit l ind =>
          let res := [(.ofAtom (.lit l), ind)]
          lTrace TraceFlags.zero & s!"Building lit:\n{repr res}\n\n" & res
    |.ofLNode l t ind =>
          let res := [(.ofAtom (.lnode l (.ofBvar 42) t), ind)] --fix
          lTrace TraceFlags.zero & s!"Building lit:\n{repr res}\n\n" & res
    |.ofGNode l ind =>
          let res := [(.ofAtom (.gnode l (.ofBvar 42)), ind)] --fix
          lTrace TraceFlags.zero & s!"Building lit:\n{repr res}\n\n" & res
    |.ofBvar l ind =>
          let res := [(.ofAtom (.bvar l) , ind)]
          lTrace TraceFlags.zero & s!"Building lit:\n{repr res}\n\n" & res
    |.ofSort l ind =>
          let res := [(.ofAtom (.sort l) , ind)]
          lTrace TraceFlags.zero & s!"Building lit:\n{repr res}\n\n" & res
    |.ofConst l ind =>
          let res := [(.ofAtom (.const l []), ind)]
          lTrace TraceFlags.zero & s!"Building lit:\n{repr res}\n\n" & res
    |.ofRW cI eid ind =>
          match classes.find? (fun x => x.1 == cI) with
          | .none => []
          | .some (_, cData) =>
              --cData.class_cexprs.map (fun (_,cex) => (cex, ind))
              -- except that rw classes may contain rw nodes in their trees ...
              let built := (CExprTrie.buildAtLink cData 0 r classes)
              dbg_trace s!"Build: {repr built}"
              built.map (fun (cex, ori) => (.wRW cI eid ori cex, ind))
  (lb.foldl (fun x y => (go y) :: x) []).join
  -- here and above, `List.dedup_beq` is a workaround ; we should delete patterns after insetring the correspodning pointer to the RW class

--#exit

partial def CExprTrie.unify_candidates? [BEq α] [Repr α] (T : CExprTrie α) (classes : List (Nat × CExprTrie α)) (ce : CExpr) (r : α → α → Prop) [DecidableRel r] : List (List α) × (List (Nat × (List (rwExpr α × List α)))) × List (Nat × Nat × CExpr × List α × List rwDirs) :=
  with_lTrace TraceFlags.off in
  let rec go (done : List (List α)) (uni : List (Nat × (List (rwExpr α × List α)))) (todos : List (Nat × Nat × CExpr × List α × List rwDirs)) : List (CExpr × Nat × List rwDirs) → List (List α) × (List (Nat × (List (rwExpr α × List α)))) × List (Nat × Nat × CExpr × List α × List rwDirs)
    | [] => (done,uni, todos)
    | (nx, link, dirs) :: more =>
        lTrace TraceFlags.zero & s!"Call\n{repr done}\n{repr uni}\n{repr todos}\n{repr ((nx, link, dirs) :: more)}\n\n" &
        match nx with
        | .failed => ([], [], [])
        | .app f a =>
            let lb := CExprTrie.getAtLink T link
            let rws := updateTodos (.app f a) dirs [] lb
            let rws_ind := rws.map (fun x => x.2.2.2.1)
            let links? := CExprTrie.Branch_getAppLinks? lb
            match links? with
            | .some (lf,la) => go (rws_ind ++ done) uni (rws ++ todos) ((f, lf, .left :: dirs) :: (a, la, .right :: dirs) :: more)
            | _ => ([], [], [])
-- **TODO** replace here and everywhere by `go (match links? with | .some _ => done | []) (match links? with | .some (lf,la) => ((f, lf) :: (a, la) :: more) | []) ` so as to make it tail recursive
        | .lam n f a i =>
            let lb := CExprTrie.getAtLink T link
            let rws := updateTodos (.lam n f a i) dirs [] lb
            let rws_ind := rws.map (fun x => x.2.2.2.1)
            let links? := CExprTrie.Branch_getLamLinks? lb
            match links? with
            | .some (lf,la) => go (rws_ind ++ done) uni (rws ++ todos) ((f, lf, .left :: dirs) :: (a, la, .right :: dirs) :: more)
            | _ => ([], [], [])
        | .forallE n f a i =>
            let lb := CExprTrie.getAtLink T link
            let rws := updateTodos (.forallE n f a i) dirs [] lb
            let rws_ind := rws.map (fun x => x.2.2.2.1)
            let links? := CExprTrie.Branch_getForallLinks? lb
            match links? with
            | .some (lf,la) => go (rws_ind ++ done) uni (rws ++ todos) ((f, lf, .left :: dirs) :: (a, la, .right :: dirs) :: more)
            | _ => ([], [], [])
        | .letE n f a z i =>
            let lb := CExprTrie.getAtLink T link
            let rws := updateTodos (.letE n f a z i) dirs [] lb
            let rws_ind := rws.map (fun x => x.2.2.2.1)
            let links? := CExprTrie.Branch_getLetLinks? lb
            match links? with
            | .some (lf,la,lz) => go (rws_ind ++ done) uni (rws ++ todos) ((f, lf, .left :: dirs) :: (a, la, .mid :: dirs) :: (z, lz, .right :: dirs) :: more)
            | _ => ([], [], [])
        | .proj n i e =>
            let lb := CExprTrie.getAtLink T link
            let rws := updateTodos (.proj n i e) dirs [] lb
            let rws_ind := rws.map (fun x => x.2.2.2.1)
            let links? := CExprTrie.Branch_getProjLinks? lb
            match links? with
            | .some (le) => go (rws_ind ++ done) uni (rws ++ todos) ((e, le, .left :: dirs) :: more)
            | _ => ([], [], [])
        | .lit l =>
            let lb := CExprTrie.getAtLink T link
            let rws := updateTodos (.lit l) dirs [] lb
            let rws_ind := rws.map (fun x => x.2.2.2.1)
            let nlb := CExprTrie.getIndices_Lit l lb
            go (List.listConsIfNonempty nlb (rws_ind ++ done)) uni (rws ++ todos) more
        | .lnode l _ .none =>
            let builds := CExprTrie.buildAtLink T link r classes
            let index_mistery := List.orderedJoin r [] (builds.map Prod.snd)
            go (List.listConsIfNonempty index_mistery done) ((l, builds) :: uni) todos more
        | .lnode l o t =>
            let lb := CExprTrie.getAtLink T link
            let rws := updateTodos (.lnode l o t) dirs [] lb
            let rws_ind := rws.map (fun x => x.2.2.2.1)
            let nlb := CExprTrie.getIndices_lNode l t lb
            go (List.listConsIfNonempty nlb (rws_ind ++ done)) uni (rws ++ todos) more
        | .gnode l o =>
            let lb := CExprTrie.getAtLink T link
            let rws := updateTodos (.gnode l o) dirs [] lb
            let rws_ind := rws.map (fun x => x.2.2.2.1)
            let nlb := CExprTrie.getIndices_gNode l lb
            go (List.listConsIfNonempty nlb (rws_ind ++ done)) uni (rws ++ todos) more
        | .bvar l =>
            let lb := CExprTrie.getAtLink T link
            let rws := updateTodos (.bvar l) dirs [] lb
            let rws_ind := rws.map (fun x => x.2.2.2.1)
            let nlb := CExprTrie.getIndices_Bvar l lb
            go (List.listConsIfNonempty nlb (rws_ind ++ done)) uni (rws ++ todos) more
        | .sort l =>
            let lb := CExprTrie.getAtLink T link
            let rws := updateTodos (.sort l) dirs [] lb
            let rws_ind := rws.map (fun x => x.2.2.2.1)
            let nlb := CExprTrie.getIndices_Sort l lb
            go (List.listConsIfNonempty nlb (rws_ind ++ done)) uni (rws ++ todos) more
        | .const l m =>
            let lb := CExprTrie.getAtLink T link
            let rws := updateTodos (.const l m) dirs [] lb
            let rws_ind := rws.map (fun x => x.2.2.2.1)
            let nlb := CExprTrie.getIndices_Const l lb
            go (List.listConsIfNonempty nlb (rws_ind ++ done)) uni (rws ++ todos) more
  go [] [] [] [(ce,0,[])]



def CExprTrie.unify_step [BEq α] [Repr α] (T : CExprTrie α) (classes : List (Nat × CExprTrie α)) (ce : CExpr) (r : α → α → Prop) [DecidableRel r] : List α × (List (Nat × List (rwExpr α × List α))) ×  List (Nat × Nat × CExpr × List α × List rwDirs) :=
  let (cand_safe, cand_uni, cand_rw) := CExprTrie.unify_candidates? T classes ce r
  let prune :=
    match (cand_safe) with
    | [] => []
    | h :: t => t.foldl (fun x y => List.orderedIntersect r x y ) h
  let new_rw := (cand_rw.map (fun (cn,en,e,ind, dir) => (cn, en ,e, List.orderedIntersect r prune ind, dir) )).filter (fun x => !x.2.2.2.1.isEmpty)
  let rec handle (done : List (rwExpr α × List α)): List (rwExpr α × List α) → List (rwExpr α × List α)
    | [] => done
    | (ce, ind) :: more =>
        match List.orderedIntersect r prune ind with
        | [] => handle done more
        | res => handle ((ce, res) :: done) more
  let rec handle2 (done : List (Nat × List (rwExpr α × List α))): List (Nat × List (rwExpr α × List α)) → List (Nat × List (rwExpr α × List α))
    | [] => done
    | (n, data) :: more =>
        match handle [] data with
        | [] => handle2 done more
        | res => handle2 ((n, res) :: done) more
  let new_uni := handle2 [] cand_uni
  (prune, new_uni, new_rw)

inductive uRWblueprint (α : Type _) where
| exactMatch (classId : Option Nat) (entryId : Option Nat) (ind : List α) (indUni : List (α × List (Nat × rwExpr α)))
| node (classId : Option Nat) (entryId : Option Nat) (ind : List α) (indUni : List (α × List (Nat × rwExpr α))) (dirs : List (Nat × List α × List rwDirs)) (chi : List (uRWblueprint α))
deriving Inhabited, BEq, Repr

def CExprTrie.unify_reconstruct [BEq α] [Repr α] (r : α → α → Prop) [DecidableRel r] (candidates : List (Nat × List (rwExpr α × List α))) : List (α × List (Nat × rwExpr α)) :=
    let rec go (node_idx : Nat) (sofar : List (α × List (Nat × rwExpr α))) : List (rwExpr α × List α) → List (α × List (Nat × rwExpr α))
        | [] => sofar
        | (assign, ind) :: rest =>
                let step := ind.foldl (fun out i => List.findModifyAdd (fun x => x.1 == i) (fun (idx, matchInfo) => (idx, (node_idx,assign) :: matchInfo)) (i, [(node_idx,assign)]) out) sofar
                go node_idx step rest
    candidates.foldl (fun out (node_idx, assign_data) => go node_idx out assign_data) []


partial def CExprTrie.unify (ce : CExpr) (Top : CExprTrie Nat) (RW_classes : List (Nat × CExprTrie Nat)) : Option (uRWblueprint Nat) :=
    with_lTrace TraceFlags.off in
    let rec main (ce : CExpr) (classId entryId : Nat): Option (uRWblueprint Nat) :=
        lTrace TraceFlags.zero & s!"MAIN {classId} \n{repr ce}\n\n" &
        match RW_classes.find? (fun x => x.1 == classId) with
        | .none => .none
        | .some (_, Tr) =>
            let (f, uni, rw) := CExprTrie.unify_step Tr (RW_classes) ce (· ≤ ·)
            match f with
            | [] => .none
            | _ =>
                let UNI := CExprTrie.unify_reconstruct (· ≤ ·) uni
                match rw with
                | [] => .some (.exactMatch (.some classId) (.some entryId) f UNI) -- no rewrites encountered in tree
                | _ =>
                    let next? := List.recuceOptions? (rw.map (fun x => main x.2.2.1 x.1 x.2.1))
                    match next? with
                    | .none => .none
                    | .some next => .some (.node (.some classId) (.some entryId) f UNI (rw.map (fun x => (x.1,x.2.2.2.1,x.2.2.2.2))) next)
    let (first, fst_uni, fst_rws) := CExprTrie.unify_step Top RW_classes ce (· ≤ ·)
    lTrace TraceFlags.zero & s!"Init {repr first} {repr fst_uni} {repr fst_rws}\n\n" &
    match first with
    | [] => .none
    | _ =>
        let UNI := CExprTrie.unify_reconstruct (· ≤ ·) fst_uni
        match fst_rws with
        | [] => .some (.exactMatch .none .none first UNI) -- no rewrites encountered in top tree
        | _ =>
            let next? := List.recuceOptions? (fst_rws.map (fun x => main x.2.2.1 x.1 x.2.1))
            match next? with
            | .none => .none
            | .some next => .some (.node .none .none first UNI (fst_rws.map (fun x => (x.1,x.2.2.2.1,x.2.2.2.2))) next)

--#exit


#eval CExprTrie.unify (.app (.lnode 0 (.ofBvar 42) .none) (.const `c [])) tree_w_rw [(37, class37), (42, class42)]

-- To fix:
-- duplicates seem to be due to us not erasing the initial occurence of the pattern in
-- BuildTrie should return blueprints !

#eval CExprTrie.unify (.app (.app (.lnode 0 (.ofBvar 42) .none) (.const `y [])) (.const `c [])) tree_w_rw [(37, class37), (42, class42)]


#check List.dedup

#eval (CExprTrie.ofList (· ≤ ·) rw_list_3)

def class37' := (CExprTrie.addRW (CExprTrie.ofList (· ≤ ·) rw_list_3) 1 [2] 42 1 (· ≤ ·)).mitigatedDeleteCExprAtLink (· ≤ ·) ((.const `x [])) 1

#eval class37'

#eval (CExprTrie.ofList (· ≤ ·) test_list)

def tree_w_rw' := (CExprTrie.addRW (CExprTrie.ofList (· ≤ ·) test_list) 1 [1,4] 37 1 (· ≤ ·)).mitigatedDeleteCExprAtLink (· ≤ ·) (.app (.const `a []) (.const `b [])) 1

#eval tree_w_rw'

#eval CExprTrie.unify (.app (.lnode 0 (.ofBvar 42) .none) (.const `c [])) tree_w_rw' [(37, class37'), (42, class42)]

#eval CExprTrie.unify (.app (.app (.lnode 0 (.ofBvar 42) .none) (.const `y [])) (.const `c [])) tree_w_rw' [(37, class37'), (42, class42)]


#eval class42

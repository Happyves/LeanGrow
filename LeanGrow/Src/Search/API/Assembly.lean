
/-
Copyright (c) 2025 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import LeanGrow.Src.Search.IntroTree.Operations
import LeanGrow.Src.Search.BackTree.Types
import LeanGrow.Src.Search.Types
import LeanGrow.Src.Search.API.UnifyCore
import LeanGrow.Src.Search.API.IntegrateForw
import LeanGrow.Src.Search.API.IntegrateBack


open Lean Meta


#check 1


structure AssembleData where
  id_gen_goal : Nat
  fullVals : ListProd Expr UInt32Array
  partialVals : ListProd Expr UInt32Array
  backTree : BackTree
  fullValsToAssign : ListProd3 Expr UInt32Array ForwMetaData
  propaGs : ListProd Nat Expr
  goalSpawn : Array (OptionProd Nat Nat)
  proGIs : UInt32Array
deriving Inhabited, Repr




partial def instaLvlTnodeAndAbstractBindTnodes
  (l1 : LocalContext) (l2 : LocalInstances)
  (unif_assign : Array ((ListProd3 Nat Nat Expr) × (ListProd3 Nat Nat Level)))
  (unis : UInt32Array) (e : Expr) (backIdx argNum : Nat) : MetaM (Prod4 Expr Bool LocalContext LocalInstances) :=
  let rec bind (i : Nat) (e : Expr) : MetaM Expr := do
    if i != 0
    then
      let fv : FVarId := ⟨tnode backIdx (i-1)⟩
      let res := Expr.abstractPat (.fvar fv) e
      match ← fv.GetDecl l1 l2 with
      | .cdecl _ _ n t b _ => bind (i-1) (.lam n t res b)
      | .ldecl _ _ n t v b _ => bind (i-1) (.letE n t v res b) -- not really expected
    else
      return e
  let relevantLvL : ListProd3 Nat Nat Level :=
    unis.foldl .nil (fun i R =>
      let U := (unif_assign[i.toNat]!).2
      U.foldl R ListProd3.cons
      )
  let relevantE : ListProd3 Nat Nat Expr :=
    unis.foldl .nil (fun i R =>
      let U := (unif_assign[i.toNat]!).1
      U.foldl R ListProd3.cons
      )
  let onLvl (l1 : LocalContext) (l2 : LocalInstances) (lvl : Level) : MetaM (Prod4 Level Bool LocalContext LocalInstances) :=
    lvl.onAllSubtermsWiWorkerCpsSkipTravState l1 l2 false (fun l B l1 l2 => do
    match l with
    | .param (.num (.num _ b) p) | .mvar ⟨.num (.num _ b) p⟩ =>
        match relevantLvL.find? (fun x y _ => x == b && y == p) with
        | .none => return .mk (.error l) true l1 l2
        | .some _ _ rl => return .mk (.ok rl) B l1 l2 -- keep going on sublevel as replacement may contain tnodes
    | x => return .mk (.ok x) B l1 l2
    )
  do
  let e ← bind argNum e
  let .mk e B l1 l2 ← e.onAllSubtermsWiWorkerCpsSkipTravState l1 l2 false (fun e _ b l1 l2 => do
    match e with
    | .sort u =>
        let .mk l B  l1 l2 ← onLvl l1 l2 u
        if B
        then return .mk (.error e) B l1 l2
        else return .mk (.ok (.sort l)) b l1 l2
    | .const n us =>
        us.foldlMcps (.mk [] l1 l2 : Prod3 _ _ _) (fun u (.mk us l1 l2) k => do
          let .mk u B  l1 l2 ← onLvl l1 l2 u
          if B
          then return .mk (.error e) B l1 l2
          else k (.mk (u :: us) l1 l2)) <| fun (.mk us l1 l2) => do
            return .mk (.ok (.const n us.reverse)) b l1 l2
    | .fvar ⟨.num (.num _ bid) p⟩ =>
        if bid != backIdx
        then
          match relevantE.find? (fun x y _ => x == bid && y == p) with
          | .some _ _ uniE =>
              return .mk (.ok uniE) b l1 l2
          | _ =>
              -- let msg := s!"{← unif_assign.mapIdxM (fun idx l => return (idx, ← l.1.foldlM ListProd3.nil (fun t p e R => return ListProd3.cons t p (← ppExpr e) R)))}"
              -- throwError s!"[instaLvlTnodeAndAbstractBindTnodes] tnode {bid} {p} not found among relevant unis {unis} and unif_assign {msg}"
              return .mk (.ok e) true l1 l2
        else
          return .mk (.ok e) b l1 l2
    | x => return .mk (.ok x) b l1 l2)
  -- let e ← bind argNum e
  return .mk e B l1 l2




def getFirstGoalIdFromIntroArgs (args : List BackTree) : Nat :=
  match args with
  | .nil => panic s!"[getFirstGoalIdFromIntroArgs] ill form backtree, no goals found !"
  | a :: as =>
      match a with
      | .ofGoal _ gi .. | .ofPropa  _ _ gi ..=> gi
      | _ => getFirstGoalIdFromIntroArgs as


#check IntroTree.gatherUGidsToGoalIdStrict

def expandUGnodesATIntro
  (l1 : LocalContext) (l2 : LocalInstances) (meaningfulUGnode : List Nat) (e : Expr)
  : MetaM (Prod3 Expr LocalContext LocalInstances) :=
  e.onAllSubtermsMTR l1 l2 (fun e _ l1 l2 => do
    match e with
    | x@(.fvar y@⟨.num kind idx⟩) =>
        if kind != `g || kind != `u
        then return .mk x l1 l2
        else
          if !(meaningfulUGnode.orderedContains idx)
          then
            match ← y.GetDecl l1 l2 with
            | .ldecl _ _ _ _ val .. => return .mk val l1 l2
            | _ => return .mk x l1 l2
          else
            return .mk x l1 l2
    | x => return .mk x l1 l2
    )



private def helpBind (l1 : LocalContext) (l2 : LocalInstances)
  (gnIdxAndTy : ListProd FVarId Expr) (e : Expr)
  : MetaM Expr := do
    match gnIdxAndTy with
    | .cons fv _ more =>
        let res := Expr.abstractPat (.fvar fv) e
          match ← fv.GetDecl l1 l2 with
          | .cdecl _ _ n t b _ => helpBind l1 l2 more (.lam n t res b)
          | .ldecl _ _ n t v b _ => helpBind l1 l2 more (.letE n t v res b)
    | .nil => return e

private def helpBind' (l1 : LocalContext) (l2 : LocalInstances)
  (ugInds : List Nat) (uNodes : Array Nat) (e : Expr)
  : MetaM Expr := do
    match ugInds with
    | .cons fvInd more =>
        let fv : FVarId := if uNodes.contains fvInd then ⟨unode fvInd⟩ else ⟨gnode fvInd⟩
        let res := Expr.abstractPat (.fvar fv) e
          match ← fv.GetDecl l1 l2 with
          | .cdecl _ _ n t b _ => helpBind' l1 l2 more uNodes (.lam n t res b)
          | .ldecl _ _ n t v b _ => helpBind' l1 l2 more uNodes (.letE n t v res b)
    | .nil => return e


@[inline]
def Lean.Expr.getGUFVarsIdsRec (e : Expr) (l1 : LocalContext) (l2 : LocalInstances) : MetaM (Prod3 (List FVarId) LocalContext LocalInstances) :=
  e.onAllSubtermsFoldEnqueueM l1 l2 []
    (fun x d _ l1 l2 sofar => do
      match x with
      | .fvar y@⟨.num k _⟩ =>
        if k == `u || k == `g
        then
          let sofar := sofar.insert y
          match ← y.GetDecl l1 l2 with
          | .cdecl .. => return .mk (.std sofar) l1 l2
          | .ldecl _ _ _ _ v _ _ =>
              if v.hasFVar
              then return .mk (.enq sofar d v) l1 l2
              else return .mk (.std sofar) l1 l2
        else return .mk (.std sofar) l1 l2
      | _ => return .mk (.std sofar) l1 l2
      )

#check 1


def introAssemble (l1 : LocalContext) (l2 : LocalInstances) (uNodes : Array Nat)
  (IT : IntroTree UInt32Array)
  (id_gen_goal : Nat) (goalSpawn : Array (OptionProd Nat Nat))
  (go : LocalContext → LocalInstances → Nat → BackTree → Array (OptionProd Nat Nat) → MetaM (Prod3 AssembleData LocalContext LocalInstances))
  (pass back_id : Nat ) (gnIdxAndTy : ListProd FVarId Expr) (bdirs gdirs : UInt32Array)
  (args : List BackTree) : MetaM (Prod3 AssembleData LocalContext LocalInstances) :=
  do
  mtracing
  mtrace on .one with s!"[introAssemble] gnIdxAndTy to {gnIdxAndTy.foldl [] (fun x _ y => x.name :: y)}"
  let someg := getFirstGoalIdFromIntroArgs args
  mtrace on .zero with s!"[introAssemble] getFirstGoalIdFromIntroArgs found {someg}"
  --let meaningfulUGnode := IT.gatherUGidsToGoalId someg []
  let meaningfulUGnode := IT.gatherUGidsAtGoalId (fun x y => y.oContains x.toUInt32) UInt32Array.union someg
  -- let meaningfulUGnode := meaningfulUGnode.reverse
  -- -- `meaningfulUGnode` inds are in increasing order, and since ug-ind can only depend on smaller ug-ind reversing does the job
  mtrace on .zero with s!"[introAssemble] meaningfulUGnode {meaningfulUGnode}"
  let rec loop (id_gen_goal : Nat) (goalSpawn : Array (OptionProd Nat Nat)) (fV pV : ListProd Expr UInt32Array) (as : List BackTree)
    (fVtA : ListProd3 Expr UInt32Array ForwMetaData) (propaGs : ListProd Nat Expr) (proGIs : UInt32Array) : List BackTree → MetaM (Prod3 AssembleData LocalContext LocalInstances)
    | a :: moa => do
        let .mk ⟨id_gen_goal,lfV,lpV,nBT,lfVtA,newpropaGs,goalSpawn,prGI⟩ l1 l2 ← go l1 l2 id_gen_goal a goalSpawn
        mtrace on .zero with s!"[introAssemble] local return:"
        mtrace on .zero with s!"[introAssemble] id_gen_goal : {id_gen_goal}"
        mtrace on .zero with s!"[introAssemble] lfV : {← lfV.foldlM ListProd.nil (fun x y z => return .cons (← ppExpr x) y z)}"
        mtrace on .zero with s!"[introAssemble] lpV : {← lpV.foldlM ListProd.nil (fun x y z => return .cons (← ppExpr x) y z)}"
        mtrace on .zero with s!"[introAssemble] lfVtA : {← lfVtA.foldlM ListProd.nil (fun x y _ z => return .cons (← ppExpr x) y z)}"
        mtrace on .zero with s!"[introAssemble] propaGs : {← propaGs.foldlM ListProd.nil (fun y x z => return .cons y (← ppExpr x) z)}"
        mtrace on .zero with s!"[introAssemble] prGI : {prGI}"
        lfV.foldlMcps ListProd.nil (fun e unis R q => do
          mtrace on .zero with s!"[introAssemble] expanding {← ppExpr e}"
          -- We could do ↓ but ↓ ↓  is much more readable and efficient
          -- expandUGnodesATIntro meaningfulUGnode e <| fun e => do
            -- mtrace on .zero with s!"[introAssemble] expanded to {← ppExpr e}"
          let .mk bfvs l1 l2 ← e.getGUFVarsIdsRec l1 l2
          mtrace on .one with s!"[introAssemble] bfvs {bfvs.map FVarId.name}"
          let localFvs := (gnIdxAndTy.foldl bfvs (fun x _ y => x :: y)).map (fun | ⟨.num _ i⟩ => i | _ => panic! "[introAssemble] incorrect fvar format")
          let localFvs := localFvs.foldl (fun R i => R.oInsert i.toUInt32) UInt32Array.empty
          let meaningfulUGnode := UInt32Array.inter meaningfulUGnode localFvs
          let meaningfulUGnode_rev := meaningfulUGnode.foldl [] (fun i L => i.toNat :: L)
          let res ← helpBind' l1 l2 meaningfulUGnode_rev uNodes e
          mtrace on .zero with s!"[introAssemble] expanded to {← ppExpr res}"
          -- let res ← helpBind l1 l2 gnIdxAndTy e
          -- mtrace on .zero with s!"[introAssemble] bounded to {← ppExpr res}"
          q <| .cons res unis R)
          <| fun lfV => do
            let fV := lfV.append fV
            lpV.foldlMcps ListProd.nil (fun e unis R q => do
              mtrace on .zero with s!"[introAssemble] expanding {← ppExpr e}"
              -- expandUGnodesATIntro meaningfulUGnode e <| fun e => do
              --   mtrace on .zero with s!"[introAssemble] expanded to {← ppExpr e}"
              let .mk bfvs l1 l2 ← e.getGUFVarsIdsRec l1 l2
              let localFvs := (gnIdxAndTy.foldl bfvs (fun x _ y => x :: y)).map (fun | ⟨.num _ i⟩ => i | _ => panic! "[introAssemble] incorrect fvar format")
              let localFvs := localFvs.foldl (fun R i => R.oInsert i.toUInt32) UInt32Array.empty
              let meaningfulUGnode := UInt32Array.inter meaningfulUGnode localFvs
              let meaningfulUGnode_rev := meaningfulUGnode.foldl [] (fun i L => i.toNat :: L)
              let res ← helpBind' l1 l2 meaningfulUGnode_rev uNodes e
              mtrace on .zero with s!"[introAssemble] expanded to {← ppExpr res}"
              -- let res ← helpBind l1 l2 gnIdxAndTy e
              -- mtrace on .zero with s!"[introAssemble] bounded to {← ppExpr res}"
              q <| .cons res unis R)
              <| fun lpV => do
                let pV := lpV.append pV
                let as := nBT :: as
                let fVtA := lfVtA.append fVtA
                loop id_gen_goal goalSpawn fV pV as fVtA
                  (newpropaGs.append propaGs)
                  (.union proGIs prGI) -- we expect prGI to have larger indices, so add it at back to maintain sorted
                    moa
    | [] => do
      let new := BackTree.ofIntro pass back_id gnIdxAndTy bdirs (.union gdirs proGIs) as
      -- let fVtA := fV.foldl fVtA (fun e unis R => .cons back_id 0 e unis R)
      mtrace on .zero with s!"[introAssemble] new replacement branch {← new.pp 0}"
      return .mk ⟨id_gen_goal,fV,pV,new, fVtA, propaGs, goalSpawn, proGIs⟩ l1 l2
  loop id_gen_goal goalSpawn .nil .nil [] .nil .nil .empty args


#check 1
-- #exit

partial def backAssemble
  (l1 : LocalContext) (l2 : LocalInstances)
  (go : LocalContext → LocalInstances → Nat → BackTree → Array (OptionProd Nat Nat) → MetaM (Prod3 AssembleData LocalContext LocalInstances))
  (id_gen_goal : Nat) (goalSpawn : Array (OptionProd Nat Nat)) (unif_claches : ListProd Nat UInt32Array) (unif_assign : Array (ListProd3 Nat Nat Expr × ListProd3 Nat Nat Level))
  (point : BackTree) (pass back_id : Nat ) (mdata : BackStepMetadata) (backExpr : Expr) (bdirs gdirs : Array UInt32Array)
  (args : Array BackTree) : MetaM (Prod3 AssembleData LocalContext LocalInstances) :=
  do
  mtracing
  let rec nonTrivialAssigns (A : Array Expr) (i : Nat) : Bool :=
    if i < A.size
    then
      match A[i]! with
      | .fvar ⟨.num (.num _ _) j⟩ =>
          if i == j then nonTrivialAssigns A (i+1) else false
      | _ => false
    else
      true
  let rec loop (id_gen_goal : Nat) (goalSpawn : Array (OptionProd Nat Nat))
    (fV pV : ListProd (Array Expr) UInt32Array) (args : Array BackTree) (fVtA : ListProd3 Expr UInt32Array ForwMetaData)
    (propa : ListProd (ListProd3 Nat Nat Expr) UInt32Array) (propaGs : ListProd Nat Expr) (proGIs : Array UInt32Array)
    (i : Nat) : MetaM (Prod3 AssembleData LocalContext LocalInstances) := do
      mtrace on .zero with s!"[backAssemble] loop with fV {← fV.foldlM ListProd.nil (fun x y z => return .cons (← x.mapM ppExpr) y z)}"
      mtrace on .zero with s!"[backAssemble] loop with pV {← pV.foldlM ListProd.nil (fun x y z => return .cons (← x.mapM ppExpr) y z)}"
      mtrace on .zero with s!"[backAssemble] loop with propa {← propa.foldlM ListProd.nil (fun x y z => return .cons (← x.foldlM ListProd3.nil (fun a b c d => return .cons a b (← ppExpr c) d)) y z)}"
      mtrace on .zero with s!"[backAssemble] loop with propaGs {← propaGs.foldlM ListProd.nil (fun y x z => return .cons y (← ppExpr x) z)}"
      mtrace on .zero with s!"[backAssemble] prGI : {proGIs}"
      if i < args.size
      then
        mtrace on .zero with s!"[backAssemble] go-ing on argument {i}"
        let .mk ⟨id_gen_goal,lfV,lpV,nBT,lfVtA,propaGs,goalSpawn,prGI⟩ l1 l2 ← go l1 l2 id_gen_goal args[i]! goalSpawn
        mtrace on .zero with s!"[backAssemble] local return:"
        mtrace on .zero with s!"[backAssemble] id_gen_goal : {id_gen_goal}"
        mtrace on .zero with s!"[backAssemble] lfV : {← lfV.foldlM ListProd.nil (fun x y z => return .cons (← ppExpr x) y z)}"
        mtrace on .zero with s!"[backAssemble] lpV : {← lpV.foldlM ListProd.nil (fun x y z => return .cons (← ppExpr x) y z)}"
        mtrace on .zero with s!"[backAssemble] lfVtA : {← lfVtA.foldlM ListProd.nil (fun x y _ z => return .cons (← ppExpr x) y z)}"
        mtrace on .zero with s!"[backAssemble] propaGs : {← propaGs.foldlM ListProd.nil (fun y x z => return .cons y (← ppExpr x) z)}"
        let fVtA := lfVtA.append fVtA
        -- let fVtA := lfV.foldl fVtA (fun e is R => .cons back_id i e is R)
        let fV ← fV.foldlM ListProd.nil (fun candArgs cstr R => do -- in MetaM for tracing
          lfV.foldlM (R : ListProd (Array Expr) UInt32Array) (fun e locCstr R => do
            -- not type anontating R in ↑ results in universe issue in 4.18
            let relCstr := UInt32Array.diff locCstr cstr
            mtrace on .zero with s!"[backAssemble] (fV) testing for clash {relCstr} vs {cstr} for extention by {← ppExpr e}"
            if unifClashOfMemoMulti relCstr cstr unif_claches
            then
              mtrace on .zero with s!"[backAssemble] clash !"
              return R
            else
              mtrace on .zero with s!"[backAssemble] no clash! "
              return ListProd.cons (candArgs.set! i e) (.union relCstr cstr) R
            )
          )
        let pV ← pV.foldlM ListProd.nil (fun candArgs cstr R => do
          (lfV.append lpV).foldlM (.cons (candArgs.set! i (Expr.fvar ⟨tnode back_id i⟩)) cstr R) (fun e locCstr R => do
            let relCstr := UInt32Array.diff locCstr cstr
            mtrace on .zero with s!"[backAssemble] (pV) testing for clash {relCstr} vs {cstr} for extention by {← ppExpr e}"
            if unifClashOfMemoMulti relCstr cstr unif_claches
            then
              mtrace on .zero with s!"[backAssemble] clash !"
              return R
            else
              mtrace on .zero with s!"[backAssemble] no clash! "
              return .cons (candArgs.set! i e) (.union relCstr cstr) R
            )
          )
        let pV := pV.foldl ListProd.nil (fun as is R => if nonTrivialAssigns as 0 then .cons as is R else R)
        mtrace on .zero with s!"[backAssemble] pV after cleaning trivial assigements {← pV.foldlM ListProd.nil (fun x y z => return .cons (← x.mapM ppExpr) y z)}"
        let propa ← propa.foldlM ListProd.nil (fun candPropa cstr R => do
          (lfV.append lpV).foldlM (R : ListProd (ListProd3 Nat Nat Expr) UInt32Array) (fun e locCstr R => do
            let relCstr := UInt32Array.diff locCstr cstr
            mtrace on .zero with s!"[backAssemble] (propa) testing for clash {relCstr} vs {cstr} for extention by {← ppExpr e}"
            if unifClashOfMemoMulti relCstr cstr unif_claches
            then
              mtrace on .zero with s!"[backAssemble] clash !"
              return R
            else
              mtrace on .zero with s!"[backAssemble] no clash! "
              return .cons (ListProd3.cons back_id i e candPropa) (.union relCstr cstr) R
            )
          )
        propa.foldlMcps (⟨nBT,id_gen_goal,propaGs,goalSpawn⟩ : Prod4 _ _ _ _) (fun ta unif_id ⟨nBT,id_gen_goal,propaGs,goalSpawn⟩ q => do
          mtrace on .zero with s!"[backAssemble] propagateForBackAssembly for ta {← ta.foldlM ListProd3.nil (fun a b c d => return .cons a b (← ppExpr c) d)} and unif_id {unif_id}"
          let .mk x y z goalSpawn ← nBT.propagateForBackAssembly l1 l2 id_gen_goal unif_claches propaGs goalSpawn ta unif_id
          mtrace on .zero with s!"[backAssemble] return bt of propagateForBackAssembly: {← z.pp 0}"
          q ⟨z,x,y,goalSpawn⟩)
          <| fun ⟨nBT,id_gen_goal,propaGs,goalSpawn⟩ => do
            mtrace on .zero with s!"[backAssemble] next loop"
            loop id_gen_goal goalSpawn fV pV (args.set! i nBT) fVtA propa propaGs (proGIs.set! i prGI) (i+1)
      else
        let gdirs := gdirs.size.fold (fun i _ A => A.modify i (fun l => .union l proGIs[i]!)) gdirs
        let new := BackTree.ofBack pass back_id mdata backExpr bdirs gdirs args
        mtrace on .zero with s!"[backAssemble] new replacement branch: {← new.pp 0}"
        let .mk (fV, ipV) l1 l2 ← fV.foldlM (.mk (.nil, .nil) l1 l2 : Prod3 _ _ _) (fun as is (.mk R l1 l2) => do
          let .mk pre hasTN l1 l2 ← instaLvlTnodeAndAbstractBindTnodes
            l1 l2 unif_assign is backExpr back_id args.size
          mtrace on .zero with s!"[backAssemble] instaLvlTnodeAndAbstractBindTnodes on {is}: hasTN {hasTN} pre {← ppExpr pre}"
          if hasTN
          then return .mk {R with snd := ListProd.cons (mkAppN pre as) is R.2} l1 l2
          else return .mk {R with fst := ListProd.cons (mkAppN pre as) is R.1} l1 l2
          )
        mtrace on .zero with s!"[backAssemble] fV : {← fV.foldlM ListProd.nil (fun x y z => return .cons (← ppExpr x) y z)}"
        mtrace on .zero with s!"[backAssemble] lipV : {← ipV.foldlM ListProd.nil (fun x y z => return .cons (← ppExpr x) y z)}"
        let .mk pV l1 l2 ← pV.foldlM (.mk ipV l1 l2 : Prod3 _ _ _) (fun as is (.mk R l1 l2) => do
          let .mk pre _ l1 l2 ← instaLvlTnodeAndAbstractBindTnodes
            l1 l2 unif_assign is backExpr back_id args.size
          mtrace on .zero with s!"[backAssemble] instaLvlTnodeAndAbstractBindTnodes on {is}: pre {← ppExpr pre}"
          return .mk (ListProd.cons (mkAppN pre as) is R) l1 l2
          )
        mtrace on .zero with s!"[backAssemble] pV : {← pV.foldlM ListProd.nil (fun x y z => return .cons (← ppExpr x) y z)}"
        let proGIs := args.size.fold (fun i _ gs => .union proGIs[args.size - i - 1]! gs) .empty
        mtrace on .zero with s!"[backAssemble] prGI : {proGIs}"
        let md := ForwMetaData.ofBackStepMetadata mdata
        let fVtA := fV.foldl fVtA (fun e u r => .cons e u md r)
        return .mk ⟨id_gen_goal,fV,pV,new, fVtA,propaGs,goalSpawn, proGIs⟩ l1 l2
  do
  if args.size != 0
  then
    let ini := (.cons (Array.replicate args.size (failExpr "backAssemble")) .empty .nil)
    loop id_gen_goal goalSpawn ini ini args .nil .nil .nil (Array.replicate gdirs.size .empty) 0
  else
    let .mk pre hasTN l1 l2 ← instaLvlTnodeAndAbstractBindTnodes
      l1 l2 unif_assign .empty backExpr back_id args.size
    mtrace on .zero with s!"[backAssemble] instaLvlTnodeAndAbstractBindTnodes hasTN {hasTN} pre {← ppExpr pre}"
    if hasTN
    then
      return .mk ⟨id_gen_goal, .nil, .cons pre .empty .nil, point, .nil, .nil, goalSpawn,.empty⟩ l1 l2
    else
      let fV := .cons pre .empty .nil
      let md := ForwMetaData.ofBackStepMetadata mdata
      let fVtA := fV.foldl .nil (fun e u r => .cons e u md r)
      return .mk ⟨id_gen_goal, fV, .nil, point, fVtA, .nil, goalSpawn,.empty⟩ l1 l2



#check 1


partial def BackTree.assembleGather (l1 : LocalContext) (l2 : LocalInstances)
  (unif_claches : ListProd Nat UInt32Array) (unif_assign : Array (ListProd3 Nat Nat Expr × ListProd3 Nat Nat Level))
  (uNodes : Array Nat) (IT : IntroTree UInt32Array) (bt : BackTree)
  : MetaM (Prod3 (ListProd Expr UInt32Array) LocalContext LocalInstances) :=
  do
  mtracing
  let rec @[specialize] introLoop (l1 : LocalContext) (l2 : LocalInstances) (gnIdxAndTy : ListProd FVarId Expr) (meaningfulUGnode : List Nat)
    (go : LocalContext → LocalInstances → BackTree → MetaM (Prod3 (ListProd Expr UInt32Array) LocalContext LocalInstances))
    (fV : ListProd Expr UInt32Array) : List BackTree → MetaM (Prod3 (ListProd Expr UInt32Array) LocalContext LocalInstances)
    | a :: moa => do
        let .mk lfV l1 l2 ← go l1 l2 a
        mtrace on .zero with s!"[assembleGather] lfV : {← lfV.foldlM ListProd.nil (fun x y z => return .cons (← ppExpr x) y z)}"
        lfV.foldlMcps fV (fun e unis R q => do
          mtrace on .zero with s!"[assembleGather] expanding {← ppExpr e}"
          let e ← helpBind' l1 l2 meaningfulUGnode uNodes e
          mtrace on .zero with s!"[assembleGather] expanded to {← ppExpr e}"
          let res ←  helpBind l1 l2 gnIdxAndTy e
          mtrace on .zero with s!"[assembleGather] bounded to {← ppExpr res}"
          q <| .cons res unis R)
          <| fun lfV => do
            introLoop l1 l2 gnIdxAndTy meaningfulUGnode go lfV moa
    | [] => do
        return .mk fV l1 l2
  let rec @[specialize] backLoop (l1 : LocalContext) (l2 : LocalInstances) (back_id : Nat) (exp : Expr) (args : Array BackTree)
    (go : LocalContext → LocalInstances → BackTree → MetaM (Prod3 (ListProd Expr UInt32Array) LocalContext LocalInstances))
    (fV : ListProd (Array Expr) UInt32Array) (i : Nat) : MetaM (Prod3 (ListProd Expr UInt32Array) LocalContext LocalInstances) := do
    if i < args.size
    then
      let .mk lfV l1 l2 ← go l1 l2 args[i]!
      mtrace on .zero with s!"[assembleGather] lfV : {← lfV.foldlM ListProd.nil (fun x y z => return .cons (← ppExpr x) y z)}"
      let fV ← fV.foldlM ListProd.nil (fun candArgs cstr R => do -- in MetaM for tracing
        lfV.foldlM (R : ListProd (Array Expr) UInt32Array) (fun e locCstr R => do
          let relCstr := UInt32Array.diff locCstr cstr
          mtrace on .zero with s!"[assembleGather] (fV) testing for clash {relCstr} vs {cstr} for extention by {← ppExpr e}"
          if unifClashOfMemoMulti relCstr cstr unif_claches
          then
            mtrace on .zero with s!"[assembleGather] clash !"
            return R
          else
            mtrace on .zero with s!"[assembleGather] no clash! "
            return ListProd.cons (candArgs.set! i e) (.union relCstr cstr) R
          )
        )
      backLoop l1 l2 back_id exp args go fV (i+1)
    else
      if args.size != 0
      then
        let .mk fV l1 l2 ← fV.foldlM (.mk .nil l1 l2 : Prod3 _ _ _) (fun as is (.mk R l1 l2) => do
          let .mk pre hasTN l1 l2 ← instaLvlTnodeAndAbstractBindTnodes
            l1 l2 unif_assign is exp back_id args.size
          mtrace on .zero with s!"[assembleGather] instaLvlTnodeAndAbstractBindTnodes on {is}: hasTN {hasTN} pre {← ppExpr pre}"
          if hasTN
          then return .mk R l1 l2
          else return .mk (ListProd.cons (mkAppN pre as) is R) l1 l2
          )
        return .mk fV l1 l2
      else
        let .mk pre hasTN  l1 l2 ← instaLvlTnodeAndAbstractBindTnodes
            l1 l2 unif_assign .empty exp back_id args.size
        if hasTN
        then return .mk .nil l1 l2
        else return .mk (ListProd.cons pre .empty .nil) l1 l2
  let rec go (l1 : LocalContext) (l2 : LocalInstances) : BackTree → MetaM (Prod3 (ListProd Expr UInt32Array) LocalContext LocalInstances)
    | .fail .. => return .mk .nil l1 l2
    | .ofUni _ ui val => return .mk (.cons val ui .nil) l1 l2
    | .ofGoal _ _ _ _ _ args =>
        args.foldlM (fun (.mk R l1 l2) t => do
          let .mk r l1 l2 ← go l1 l2 t
          return .mk (r.append R) l1 l2) (.mk ListProd.nil l1 l2 : Prod3 _ _ _)
    | .ofPropa _ unis _ _ _ _ args =>
        args.foldlM (fun (.mk R l1 l2) t => do
          let .mk r l1 l2 ← go l1 l2 t
          return .mk ((r.foldl ListProd.nil (fun x y z => ListProd.cons x (.union unis y) z)).append R) l1 l2) (.mk ListProd.nil l1 l2 : Prod3 _ _ _)
    | .ofIntro _ _ gnIdxAndTy _ _ args => do
        let someg := getFirstGoalIdFromIntroArgs args
        mtrace on .zero with s!"[assembleGather] getFirstGoalIdFromIntroArgs found {someg}"
        let meaningfulUGnode := IT.gatherUGidsToGoalIdStrict (fun x y => y.oContains x.toUInt32) UInt32Array.union someg .empty
        let meaningfulUGnode_rev := meaningfulUGnode.foldl [] (fun i L => i.toNat :: L)
        -- `meaningfulUGnode` inds are in increasing order, and since ug-ind can only depend on smaller ug-ind reversing does the job
        mtrace on .zero with s!"[assembleGather] meaningfulUGnode {meaningfulUGnode}"
        introLoop l1 l2 gnIdxAndTy meaningfulUGnode_rev go .nil args
    | .ofBack _ back_id  _ exp _ _ args =>
        backLoop l1 l2 back_id exp args go .nil 0
  go l1 l2 bt

#check 1



partial def BackTree.assembleCore (l1 : LocalContext) (l2 : LocalInstances) (uNodes : Array Nat) (IT : IntroTree UInt32Array)
  (id_gen_goal : Nat) (goalSpawn : Array (OptionProd Nat Nat)) (unif_claches : ListProd Nat UInt32Array) (unif_assign : Array (ListProd3 Nat Nat Expr × ListProd3 Nat Nat Level))
  (passNum : Nat) (bt : BackTree) : MetaM (Prod3 AssembleData LocalContext LocalInstances) :=
  do
  mtracing
  let rec go (l1 : LocalContext) (l2 : LocalInstances) (id_gen_goal : Nat) (bt : BackTree) (goalSpawn : Array (OptionProd Nat Nat)) : MetaM (Prod3 AssembleData LocalContext LocalInstances) := do
    match bt with
    | x@(.fail _) => return .mk ⟨id_gen_goal, .nil, .nil, x, .nil, .nil, goalSpawn, .empty⟩ l1 l2
    | x@(.ofUni _ uniId val) => do
        mtrace on .one with s!"[assembleCore] ofUni {uniId} {← ppExpr val}"
        return .mk ⟨id_gen_goal,.cons val uniId .nil, .nil, x, .nil,.nil, goalSpawn, .empty⟩ l1 l2
    | x@(.ofGoal pass goal_id type bdirs gdirs args) => do
        if pass != passNum
        then
          mtrace on .one with s!"[assembleCore] enter gather mode on ofGoal {goal_id} {← ppExpr type}"
          let .mk fV l1 l2 ← x.assembleGather l1 l2 unif_claches unif_assign uNodes IT
          mtrace on .one with s!"[assembleCore] gather mode returned {← fV.foldlM ListProd.nil (fun x y z => return .cons (← ppExpr x) y z)}"
          return .mk ⟨id_gen_goal, fV, .nil, x, .nil, .nil, goalSpawn, .empty⟩ l1 l2
        else
          let mut idgg := id_gen_goal
          let mut fV : ListProd Expr UInt32Array := .nil
          let mut pV : ListProd Expr UInt32Array := .nil
          let mut as : List BackTree := []
          let mut fVtA : ListProd3 Expr UInt32Array ForwMetaData := .nil
          let mut pGs := .nil
          let mut pGI := .empty
          let mut gS := goalSpawn
          mtrace on .zero with s!"[assembleCore] at ofGoal, go-ing on args"
          let mut l1 := l1
          let mut l2 := l2
          for a in args do
            let .mk ⟨id_gen_goal,lfV,lpV,nBT,lfVtA,npGs,ngoalSpawn,prGI⟩  l1' l2' ← go l1 l2 idgg a gS
            l1 := l1'
            l2 := l2'
            mtrace on .zero with s!"[assembleCore] local return:"
            mtrace on .zero with s!"[assembleCore] id_gen_goal : {id_gen_goal}"
            mtrace on .zero with s!"[assembleCore] lfV : {← lfV.foldlM ListProd.nil (fun x y z => return .cons (← ppExpr x) y z)}"
            mtrace on .zero with s!"[assembleCore] lpV : {← lpV.foldlM ListProd.nil (fun x y z => return .cons (← ppExpr x) y z)}"
            mtrace on .zero with s!"[assembleCore] lfVtA : {← lfVtA.foldlM ListProd.nil (fun x y _ z => return .cons (← ppExpr x) y z)}"
            mtrace on .zero with s!"[assembleCore] npGs : {← npGs.foldlM ListProd.nil (fun y x z => return .cons (← ppExpr x) y z)}"
            idgg := id_gen_goal
            fV := lfV.append fV
            -- fVtA := lfV.foldl fVtA (fun e is R => .cons goal_id e is R)
            pV := lpV.append pV
            as := nBT :: as
            fVtA := lfVtA.append fVtA
            pGs := npGs.append pGs
            gS := ngoalSpawn
            pGI := .union pGI prGI
          let new := BackTree.ofGoal pass goal_id type bdirs (.union gdirs pGI) as
          mtrace on .two with s!"[assembleCore] returning branch {← new.pp 0}"
          return .mk ⟨idgg,fV,pV,new,fVtA,pGs,gS,pGI⟩ l1 l2
    | x@(.ofPropa pass uni_id goal_id type bdirs gdirs args) => do
        if pass != passNum
        then
          mtrace on .one with s!"[assembleCore] enter gather mode on ofPropa {goal_id} {← ppExpr type}"
          let .mk fV l1 l2 ← x.assembleGather l1 l2 unif_claches unif_assign uNodes IT
          mtrace on .one with s!"[assembleCore] gather mode returned {← fV.foldlM ListProd.nil (fun x y z => return .cons (← ppExpr x) y z)}"
          return .mk ⟨id_gen_goal, fV, .nil, x, .nil, .nil, goalSpawn, .empty⟩ l1 l2
        else
          let mut idgg := id_gen_goal
          let mut fV : ListProd Expr UInt32Array := .nil
          let mut pV : ListProd Expr UInt32Array := .nil
          let mut as : List BackTree := []
          let mut fVtA : ListProd3 Expr UInt32Array ForwMetaData := .nil
          let mut pGs := .nil
          let mut pGI := .empty
          let mut gS := goalSpawn
          mtrace on .zero with s!"[assembleCore] at ofPropa, go-ing on args"
          let mut l1 := l1
          let mut l2 := l2
          for a in args do
            let .mk ⟨id_gen_goal,lfV,lpV,nBT,lfVtA,npGs,ngoalSpawn,prGI⟩ l1' l2' ← go l1 l2 idgg a gS
            l1 := l1'
            l2 := l2'
            mtrace on .zero with s!"[assembleCore] local return:"
            mtrace on .zero with s!"[assembleCore] id_gen_goal : {id_gen_goal}"
            mtrace on .zero with s!"[assembleCore] lfV : {← lfV.foldlM ListProd.nil (fun x y z => return .cons (← ppExpr x) y z)}"
            mtrace on .zero with s!"[assembleCore] lpV : {← lpV.foldlM ListProd.nil (fun x y z => return .cons (← ppExpr x) y z)}"
            mtrace on .zero with s!"[assembleCore] lfVtA : {← lfVtA.foldlM ListProd.nil (fun x y _ z => return .cons (← ppExpr x) y z)}"
            mtrace on .zero with s!"[assembleCore] npGs : {← npGs.foldlM ListProd.nil (fun y x z => return .cons (← ppExpr x) y z)}"
            idgg := id_gen_goal
            let lfV := (lfV.foldl ListProd.nil (fun x y z => .cons x (y.union uni_id) z))
            fV := lfV.append fV
            fVtA := lfVtA.append fVtA
            -- fVtA := lfV.foldl fVtA (fun e is R => .cons goal_id e is R)
            pV := (lpV.foldl ListProd.nil (fun x y z => .cons x (y.union uni_id) z)).append pV
            as := nBT :: as
            pGs := npGs.append pGs
            gS := ngoalSpawn
            pGI := .union pGI prGI
          let new := BackTree.ofPropa pass uni_id goal_id type bdirs (.union gdirs pGI) as
          mtrace on .two with s!"[assembleCore] returning branch {← new.pp 0}"
          return .mk ⟨idgg,fV,pV,new, fVtA, pGs,gS,pGI⟩ l1 l2
    | x@(.ofIntro pass back_id gnIdxAndTy bdirs gdirs args) => do
        if pass != passNum
        then
          mtrace on .one with s!"[assembleCore] enter gather mode ofIntro {back_id}"
          let .mk fV l1 l2 ← x.assembleGather l1 l2 unif_claches unif_assign uNodes IT
          mtrace on .one with s!"[assembleCore] gather mode returned {← fV.foldlM ListProd.nil (fun x y z => return .cons (← ppExpr x) y z)}"
          return .mk ⟨id_gen_goal, fV, .nil, x, .nil, .nil, goalSpawn, .empty⟩ l1 l2
        else
          mtrace on .one with s!"[assembleCore] calling introAssemble"
          introAssemble l1 l2 uNodes IT id_gen_goal goalSpawn go pass back_id gnIdxAndTy bdirs gdirs args
    | x@(.ofBack pass back_id mdata thm bdirs gdirs args) => do
        if pass != passNum
        then
          mtrace on .one with s!"[assembleCore] enter gather mode ofBack {back_id}"
          let .mk fV l1 l2 ← x.assembleGather l1 l2 unif_claches unif_assign uNodes IT
          mtrace on .one with s!"[assembleCore] gather mode returned {← fV.foldlM ListProd.nil (fun x y z => return .cons (← ppExpr x) y z)}"
          return .mk ⟨id_gen_goal, fV, .nil, x, .nil, .nil, goalSpawn, .empty⟩ l1 l2
        else
          mtrace on .one with s!"[assembleCore] calling backAssemble"
          backAssemble l1 l2 go id_gen_goal goalSpawn unif_claches unif_assign x pass back_id mdata thm bdirs gdirs args
          /- We intentionally only propagate tnodes from the same backstep, as also propagating
          their branch tnodes would be redundant, as they're already in the fullVal/partialVal. -/
  go l1 l2 id_gen_goal bt goalSpawn


#check IntroTree.hasForwAtGoalId?



/--

- bumps the pass counter, so that all current branches become irrelevant until we make the
  relevant again
-/
partial def BackTree.assembleMain
  (l1 : LocalContext) (l2 : LocalInstances)  (revCountMax : Nat)
  (st : SearchState UInt32Array)
  : MetaM (Prod4 (SearchState UInt32Array) (ListProd Expr UInt32Array) LocalContext LocalInstances) :=
  do
  mtracing
  let rec @[inline] proG (l1 : LocalContext) (l2 : LocalInstances)  (st : SearchState UInt32Array)
    (q : SearchState UInt32Array → MetaM (Prod4 (SearchState UInt32Array) (ListProd Expr UInt32Array) LocalContext LocalInstances)) : ListProd Nat Expr → MetaM (Prod4 (SearchState UInt32Array) (ListProd Expr UInt32Array) LocalContext LocalInstances)
    | .nil => q st
    | .cons tar exp more => do
        mtrace on .two with s!"[assembleMain] call integratePropaedGoalStd target goal {tar} and type {← ppExpr exp}"
        let .mk newI further st l1 l2 ← integratePropaedGoalStd l1 l2 revCountMax tar exp st
        let st := {st with cycleAddForw := newI.append st.cycleAddForw, cycleAddBack := further.append st.cycleAddBack}
        mtrace on .two with s!"[assembleMain] adding → to cycleAddBack: {← further.foldlM ListProd.nil (fun y x z => return .cons (← ppExpr x) y z)}"
        proG l1 l2 st q (further.append more)
  mtrace on .two with s!"[assembleMain] call to assembleCore with:"
  mtrace on .two with s!"[assembleMain] pass {st.id_gen_apass}"
  mtrace on .two with s!"[assembleMain] goalid {st.id_gen_goal}"
  mtrace on .two with s!"[assembleMain] bt {← st.backTree.pp 0}"
  mtrace on .two with s!"[assembleMain] it {st.introTree.pp 0}"
  mtrace on .two with s!"[assembleMain] unif_claches {st.unif_claches.toListOfProd}"
  mtrace on .two with s!"[assembleMain] unif_assign {← st.unif_assign.mapIdxM (fun idx x => do let y ← x.1.foldlM ListProd3.nil (fun x y z w => do return .cons x y (← ppExpr z) w) ; return (idx,y,x.2))}"
  let .mk ⟨id_gen_goal, fV, _, bT, fVtA, pGs,ngoalSpawn,_⟩ l1 l2 ← BackTree.assembleCore l1 l2 st.uNodes st.introTree st.id_gen_goal st.goalSpawn st.unif_claches st.unif_assign st.id_gen_apass st.backTree
  mtrace on .two with s!"[assembleMain] return from assembleCore with:"
  mtrace on .two with s!"[assembleMain] id_gen_goal {id_gen_goal}"
  mtrace on .two with s!"[assembleMain] fV {← fV.foldlM ListProd.nil (fun x y z => return .cons (← ppExpr x) y z)}"
  mtrace on .two with s!"[assembleMain] pGs {← pGs.foldlM ListProd.nil (fun x y z => return .cons x (← ppExpr y) z)}"
  mtrace on .two with s!"[assembleMain] fVtA {← fVtA.foldlM ListProd.nil (fun x y _ z => return .cons (← ppExpr x) y z)}"
  mtrace on .two with s!"[assembleMain] bt {← bT.pp 0}"
  match fV with
  | .cons .. => return .mk st fV l1 l2
  | .nil =>
    let st := {st with id_gen_apass := st.id_gen_apass + 1, id_gen_goal := id_gen_goal, backTree := bT, goalSpawn := ngoalSpawn}
    mtrace on .two with s!"[assembleMain] bumped pass, set id_gen_goal, back-tree and goalSpawn"
    match fVtA, pGs with
    | .nil, .nil  => return .mk st .nil l1 l2
    | _, _ =>
        fVtA.foldlMcps (.mk st l1 l2 : Prod3 _ _ _) (fun term _ md (.mk st l1 l2) q => do
          let ty ← InferType term l1 l2
          let ugis := term.getGUFVarsIds.foldl (fun | R,  ⟨.num _ i⟩ => R.oInsert i.toUInt32 | _, _ => panic s!"[BackTree.assembleMain] getGUFVarsIds return incorrect patterns ?!?") .empty
          let .mk alreadyThere? l1 ← forwardDuplicateF? l1 ugis revCountMax ty st.introTree
          if alreadyThere?
          then
            mtrace on .two with s!"[assembleMain] not adding term {← ppExpr term} of type {← ppExpr ty} since it's a forward duplicate"
            q (.mk st l1 l2)
          else
            let ugis := term.getGUFVarsIds.foldl (fun R i =>
              match FVarId.name i with
              | .num _ j => R.oInsert j.toUInt32
              | _ => R) .empty
            mtrace on .two with s!"[assembleMain] adding term {← ppExpr term} of type {← ppExpr ty} with u-g-inds {ugis}"
            let .mk addedForwId addedForwFv addedForwE st l1 l2 ← integrateForwardStd l1 l2 revCountMax md term ugis st
            let st := {st with cycleAddForw := .cons addedForwId addedForwFv addedForwE st.cycleAddForw }
            mtrace on .two with s!"[assembleMain] adding type {← ppExpr addedForwE} with u-g-ind {addedForwId} to cycleAddForw"
            q (.mk st l1 l2)
          ) <| fun (.mk st l1 l2) => do
            proG l1 l2 st (fun  st =>
              BackTree.assembleMain l1 l2 revCountMax st
              ) pGs

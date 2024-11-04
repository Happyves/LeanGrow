
import LeanGrow.F.Data.CExpr.API
import LeanGrow.F.Data.CExpr.ReduceInferMuggle.Types
import LeanGrow.F.Data.CExpr.ReduceInferMuggle.BetaZeta


open Lean


-- maybe use use ByteArray encoding of names from the start ?
def cInferConstType (cstData : CTrie CstInfo) (c : Name) (us : List Level) : CExpr :=
  match cstData.find? (c.toString) with
  | .some info => info.type.instantiateLevelParams info.levelParams us
  | _ => .failed


def cInferAppType_1 : FlowState → FlowState
  | ⟨(.cInferAppType_1, bvCtx) :: mI, (.ofCExpr f) :: (.ofList args) :: mA⟩ =>
      ⟨(.Whnf_1, bvCtx) :: (.cInferAppType_2, bvCtx) :: mI, (.ofCExpr f) :: (.ofList args) :: mA⟩
  | _ => FailedState

def cInferAppType_2 : FlowState → FlowState
  | ⟨(.cInferAppType_2, bvCtx) :: mI, (.ofCExpr f) :: (.ofList args) :: mA⟩ =>
      let rec go (sofar : CExpr) : List CExpr → (CExpr × List CExpr)
        | [] => (sofar, [])
        | a :: as =>
            match sofar with
            | .forallE _ _ b _ => go (CExpr.instantiate a b) as
            | _ => (sofar, a :: as)
      let (gone, todo) := go f args
      match todo with
      | [] =>
          ⟨mI, (.ofCExpr gone) :: mA⟩
      | _ =>
          ⟨(.Whnf_1, bvCtx) :: (.cInferAppType_3, bvCtx) :: mI, (.ofCExpr gone) :: (.ofList todo) :: mA⟩
  | _ => FailedState


def cInferAppType_3 : FlowState → FlowState
  | ⟨(.cInferAppType_3, bvCtx) :: mI, (.ofCExpr sofar) :: (.ofList todo) :: mA⟩ =>
      match sofar, todo with
      | .forallE _ _ b _ , a :: as =>
            ⟨(.cInferAppType_2, bvCtx) :: mI, (.ofCExpr (CExpr.instantiate a b)) :: (.ofList as) :: mA⟩
      | _, _  => FailedState
  | _  => FailedState


def cInferProjType_1 : FlowState → FlowState
  | ⟨(.cInferProjType_1, bvCtx) :: mI, (.ofName structName) :: (.ofNat idx) :: (.ofCExpr e) :: mA⟩ =>
      ⟨(.InferType_1 , bvCtx) :: (.Whnf_1, bvCtx) :: (.cInferProjType_2, bvCtx) :: mI, (.ofCExpr e) :: (.ofName structName) :: (.ofNat idx) :: (.ofCExpr e) :: mA⟩
  | _  => FailedState


def cInferProjType_2 (fctx : FixCtx) : FlowState → FlowState
  | ⟨(.cInferProjType_2, bvCtx) :: mI, (.ofCExpr strucType) :: (.ofName structName) :: (.ofNat idx) :: mA⟩ =>
        let (h,ps) := CExpr.getApp strucType
        match h with
        | .const _ lvls =>
            match fctx.cstData.find? structName.toString with
            | .some (.struc _ _ ctor _) =>
                  ⟨(.cInferAppType_1, bvCtx) :: (.cInferProjType_3, bvCtx) :: mI, (.ofCExpr (.const ctor lvls)) :: (.ofList ps) :: (.ofNat idx) :: (.ofName structName) :: mA⟩
            | _  => FailedState
        | _  => FailedState
  | _  => FailedState


def cInferProjType_3 : FlowState → FlowState
  | ⟨(.cInferProjType_3, bvCtx) :: mI, (.ofCExpr ctorType) :: (.ofNat idx_todos) :: (.ofName structName) :: (.ofNat idx) :: (.ofCExpr e) :: mA⟩ =>
        let rec go (sofar : CExpr) : Nat → (CExpr × Nat)
          | 0 => (sofar, 0)
          | n+1 =>
              match sofar with
              | .forallE _ _ b _ => go (CExpr.instantiate (.proj structName (idx - 1 - n) e) b) n
              | _ => (sofar, n+1)
        let (gone, todo) := go ctorType idx_todos
        match todo with
        | 0 =>
            ⟨(.Whnf_1, bvCtx) :: (.cInferProjType_4, bvCtx) :: mI, (.ofCExpr gone) :: (.ofName structName) :: (.ofNat idx) :: (.ofCExpr e) :: mA⟩
        | _ =>
            ⟨(.Whnf_1, bvCtx) :: (.cInferProjType_3, bvCtx) :: mI, (.ofCExpr gone) :: (.ofNat todo) :: (.ofName structName) :: (.ofNat idx) :: (.ofCExpr e) :: mA⟩
  | _  => FailedState


def cInferProjType_4 : FlowState → FlowState
  | ⟨(.cInferProjType_4, _) :: mI, (.ofCExpr toProj) :: (.ofName _) :: (.ofNat _) :: (.ofCExpr _) :: mA⟩ =>
      match toProj with
      | .forallE _ t _ _ =>
          ⟨mI, (.ofCExpr t) :: mA⟩
      |  _ => FailedState
  | _  => FailedState



def cInferLambdaType_1 : FlowState → FlowState
  | ⟨(.cInferLambdaType_1, bvarCtx) :: mI, (.ofCExpr ce) :: mA⟩ =>
      match ce with
      | .lam n t b i => ⟨(.cInferLambdaType_1, (t :: bvarCtx)) :: (.cInferLambdaType_2, bvarCtx) :: mI, (.ofCExpr b) :: (.ofName n) :: (.ofCExpr t) :: (.ofBinInfo i) :: mA⟩
      | _ => ⟨(.InferType_1, bvarCtx) :: mI, (.ofCExpr ce) :: mA⟩
  | _  => FailedState



def cInferLambdaType_2 : FlowState → FlowState
  | ⟨(.cInferLambdaType_2, _) :: mI, (.ofCExpr b) :: (.ofName n) :: (.ofCExpr t) :: (.ofBinInfo i) :: mA⟩ =>
      ⟨mI, (.ofCExpr (.forallE n t b i)) :: mA⟩
  | _  => FailedState



#exit

def getLevel (fctx : FixCtx) (bvarCtx : List CExpr)
  (type : CExpr) : Level :=
  let typeType :=
    cexprWhnf fctx bvarCtx
      (cexprInferType fctx bvarCtx type)
  match typeType with
  | .sort lvl => lvl
  | _ => .mvar ⟨`failed⟩

def cInferForallType (fctx : FixCtx) (bvarCtx : List CExpr)
  (e : CExpr) : CExpr :=
  let rec go (prepend : List CExpr) (sofar : List Level) : CExpr → List Level
    | .forallE _ t b _ => go (t :: prepend) ((getLevel fctx prepend t) :: sofar) b
    | e => (getLevel fctx prepend e) :: sofar
  match (go bvarCtx [] e) with
  | [] => .failed
  | ini :: Ls =>
      let compL := Ls.foldl (fun s l => mkLevelIMax' l s) ini
      .sort compL.normalize


#eval Array.push #[1,2] 3
-- since arrays push to the back, and `inferForallType` uses `foldrM`, we should be in the right order ...

def Literal.ctype : Literal → CExpr
  | .natVal _ => .const `Nat []
  | .strVal _ => .const `String []

-- note : when adding environements for constantInfo and lnode and gnode types,
-- we should also change the types in LeanGrow.F.Data.CExpr.ReduceInfer.Magic
@[export lean_my_infer_type]
def cexprInferTypeImp
  (fctx : FixCtx) (bvarCtx : List CExpr)
  (e : CExpr) : CExpr :=
  match e with
  | .const c us    => cInferConstType fctx.cstData c us
  | .proj n i s    => cInferProjType fctx bvarCtx n i s
  | .app ..      => let (h,as) := CExpr.getApp e ; cInferAppType fctx bvarCtx h as
  | .bvar bidx     =>
        match bvarCtx.get? bidx with
        | .some T => T
        | _ => .failed
  | .lit v         => Literal.ctype v
  | .sort lvl      => .sort (mkLevelSucc lvl)
  | .forallE ..    => cInferForallType fctx bvarCtx e
  | .lam ..        => cInferLambdaType fctx bvarCtx e
  | .letE ..       => cInferLambdaType fctx bvarCtx e
  | .gnode gidx _ =>
        let (p,i) := fctx.gnodeTypesHandler gidx
        (fctx.gnodeTypes.get! p).get! i
  | .lnode pos _ tag =>
        match tag with
        | .none =>
            match fctx.current with
            | .none => .failed
            | .some thmdata => (thmdata.get! pos).cexpr
        | .some backId =>
            match fctx.ltxTypes.find? (fun x => x.1 == backId) with
            | .none => .failed
            | .some (_,thmdata) => (thmdata.get! pos).cexpr
  | .failed => .failed

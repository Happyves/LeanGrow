
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
      ⟨(.InferType_1, bvCtx) :: (.cInferAppType_2, bvCtx) :: mI, (.ofCExpr f) :: (.ofList args) :: mA⟩
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


def getLevel_1 : FlowState → FlowState
  | ⟨(.getLevel_1, bvarCtx) :: mI, (.ofCExpr type) :: mA⟩ =>
      ⟨(.InferType_1, bvarCtx) :: (.Whnf_1, bvarCtx) :: (.getLevel_2, bvarCtx) :: mI, (.ofCExpr type) ::(.ofCExpr type) :: mA⟩
  | _  => FailedState


def getLevel_2 : FlowState → FlowState
  | ⟨(.getLevel_2, _) :: mI, (.ofCExpr typeType) :: mA⟩ =>
      match typeType with
      | .sort lvl => ⟨mI, (.ofLevel lvl) :: mA⟩
      | _ => FailedState
  | _  => FailedState




def cInferForallType_1 : FlowState → FlowState
  | ⟨(.cInferForallType_1, bvarCtx) :: mI, (.ofCExpr e) :: mA⟩ =>
      ⟨(.cInferForallType_2, bvarCtx) :: mI, (.ofCExpr e) :: (.ofListLevel []) :: mA⟩
  | _  => FailedState


def cInferForallType_2 : FlowState → FlowState
  | ⟨(.cInferForallType_2, bvarCtx) :: mI, (.ofCExpr e) :: (.ofListLevel ll) :: mA⟩ =>
      match e with
      | .forallE _ t b _ =>
          ⟨(.getLevel_1, bvarCtx) :: (.cInferForallType_3, bvarCtx) :: (.cInferForallType_2, t :: bvarCtx) :: mI, (.ofCExpr t) :: (.ofCExpr b) :: (.ofListLevel ll) :: mA⟩
      | e =>
          ⟨(.getLevel_1, bvarCtx) :: (.cInferForallType_4, bvarCtx) :: (.cInferForallType_5, bvarCtx) :: mI, (.ofCExpr e) :: (.ofListLevel ll) :: mA⟩
  | _  => FailedState


def cInferForallType_3 : FlowState → FlowState
  | ⟨(.cInferForallType_3, _) :: mI, (.ofLevel l) :: (.ofCExpr b) :: (.ofListLevel ll) :: mA⟩ =>
      ⟨ mI, (.ofLevel l) :: (.ofCExpr b) :: (.ofListLevel (l :: ll)) :: mA⟩
  | _  => FailedState


def cInferForallType_4 : FlowState → FlowState
  | ⟨(.cInferForallType_4, _) :: mI, (.ofLevel l) :: (.ofListLevel ll) :: mA⟩ =>
      ⟨ mI, (.ofLevel l) :: (.ofListLevel (l :: ll)) :: mA⟩
  | _  => FailedState


def cInferForallType_5 : FlowState → FlowState
  | ⟨(.cInferForallType_5, _) :: mI, (.ofListLevel ll) :: mA⟩ =>
      match ll with
      | [] => FailedState
      | ini :: Ls =>
          let compL := Ls.foldl (fun s l => mkLevelIMax' l s) ini
          let l := .sort compL.normalize
          ⟨mI, (.ofCExpr l) :: mA⟩
  | _  => FailedState


def Literal.ctype : Literal → CExpr
  | .natVal _ => .const `Nat []
  | .strVal _ => .const `String []


def InferType_1 (fctx : FixCtx) : FlowState → FlowState
  | ⟨(.InferType_1, bvarCtx) :: mI, (.ofCExpr e) :: mA⟩ =>
      match e with
      | .const c us    =>
          let res := cInferConstType fctx.cstData c us
          ⟨mI, (.ofCExpr res) :: mA⟩
      | .proj n i s    =>
          ⟨(.cInferProjType_1, bvarCtx) :: mI, (.ofName n) :: (.ofNat i) :: (.ofCExpr s) :: mA⟩
      | .app ..      =>
          let (f,args) := CExpr.getApp e
          ⟨(.cInferAppType_1, bvarCtx) :: mI, (.ofCExpr f) :: (.ofList args) :: mA⟩
      | .bvar bidx     =>
          match bvarCtx.get? bidx with
          | .some T => ⟨mI, (.ofCExpr T) :: mA⟩
          | _ => FailedState
      | .lit v         => ⟨mI, (.ofCExpr (Literal.ctype v)) :: mA⟩
      | .sort lvl      => ⟨mI, (.ofCExpr (.sort (mkLevelSucc lvl))) :: mA⟩
      | .forallE ..    => ⟨(.cInferForallType_1, bvarCtx) :: mI, (.ofCExpr e) :: mA⟩
      | .lam ..        => ⟨(.cInferLambdaType_1, bvarCtx) :: mI, (.ofCExpr e) :: mA⟩
      | .letE ..       => ⟨(.cInferLambdaType_1, bvarCtx) :: mI, (.ofCExpr e) :: mA⟩
      | .gnode gidx _ =>
            let (p,i) := fctx.gnodeTypesHandler gidx
            let T := (fctx.gnodeTypes.get! p).get! i
            ⟨mI, (.ofCExpr T) :: mA⟩
      | .lnode pos _ tag =>
            match tag with
            | .none =>
                match fctx.current with
                | .none => FailedState
                | .some thmdata =>
                    let T := (thmdata.get! pos).cexpr
                    ⟨mI, (.ofCExpr T) :: mA⟩
            | .some backId =>
                match fctx.ltxTypes.find? (fun x => x.1 == backId) with
                | .none => FailedState
                | .some (_,thmdata) =>
                    let T := (thmdata.get! pos).cexpr
                    ⟨mI, (.ofCExpr T) :: mA⟩
      | .failed => FailedState
  | _  => FailedState

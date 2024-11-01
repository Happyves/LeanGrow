
import LeanGrow.F.Data.CExpr.API
import LeanGrow.F.Data.CExpr.ReduceInfer.Magic
import LeanGrow.F.Data.CExpr.ReduceInfer.BetaZeta


open Lean


-- maybe use use ByteArray encoding of names from the start ?
def cInferConstType (cstData : CTrie CstInfo) (c : Name) (us : List Level) : CExpr :=
  match cstData.find? (c.toString) with
  | .some info => info.type.instantiateLevelParams info.levelParams us
  | _ => .failed

def cInferAppType (gnodeTypes : List (Array CExpr)) (gnodeTypesHandler : Nat → (Nat × Nat))
  (ltxTypes : List (Array EmbedData)) (current : Option (Array EmbedData))
  (cstData : CTrie CstInfo) (bvarCtx : List CExpr)
  (f : CExpr) (args : List CExpr) : CExpr :=
  let fType := cexprInferType gnodeTypes gnodeTypesHandler ltxTypes current cstData bvarCtx f -- will need fixin
  let rec go (sofar : CExpr) : List CExpr → CExpr
    | [] => sofar
    | a :: as =>
        match sofar with
        | .forallE _ _ b _ => go (CExpr.instantiate a b) as
        | _ =>
            match (cexprWhnf gnodeTypes gnodeTypesHandler ltxTypes current cstData bvarCtx sofar) with -- will need fixin
            | .forallE _ _ b _ => go (CExpr.instantiate a b) as
            | _ => .failed
  go fType args

def cInferProjType (gnodeTypes : List (Array CExpr)) (gnodeTypesHandler : Nat → (Nat × Nat))
  (ltxTypes : List (Array EmbedData)) (current : Option (Array EmbedData))
  (cstData : CTrie CstInfo) (bvarCtx : List CExpr)
  (structName : Name) (idx : Nat) (e : CExpr) : CExpr :=
  let rec go (sofar : CExpr) : Nat → CExpr
    | 0 => sofar
    | n+1 =>
        match sofar with
        | .forallE _ _ b _ => go (CExpr.instantiate (.proj structName (idx - 1 - n) e) b) n
        | _ =>
            match (cexprWhnf gnodeTypes gnodeTypesHandler ltxTypes current cstData bvarCtx sofar) with
            | .forallE _ _ b _ => go (CExpr.instantiate (.proj structName (idx - 1 - n) e) b) n
            | _ => .failed
  let strucType :=
    cexprWhnf gnodeTypes gnodeTypesHandler ltxTypes current cstData bvarCtx
      (cexprInferType gnodeTypes gnodeTypesHandler ltxTypes current cstData bvarCtx e)
  let (h,ps) := CExpr.getApp strucType
  match h with
  | .const _ lvls =>
      match cstData.find? structName.toString with
      | .some (.struc _ _ ctor) =>
            let ctorType := cInferAppType gnodeTypes gnodeTypesHandler ltxTypes current cstData bvarCtx (.const ctor lvls) ps
            let toProj := cexprWhnf gnodeTypes gnodeTypesHandler ltxTypes current cstData bvarCtx (go ctorType idx)
            match toProj with
            | .forallE _ t _ _ => t
            |  _ => .failed
      | _ => .failed
  | _ => .failed


def cInferLambdaType (gnodeTypes : List (Array CExpr)) (gnodeTypesHandler : Nat → (Nat × Nat))
  (ltxTypes : List (Array EmbedData)) (current : Option (Array EmbedData))
  (cstData : CTrie CstInfo) (bvarCtx : List CExpr)
  (e : CExpr) : CExpr :=
  let rec go (prepend : List CExpr) : CExpr → CExpr
    | .lam n t b i => .forallE n t (go (t :: prepend) b) i
    | e =>  cexprInferType gnodeTypes gnodeTypesHandler ltxTypes current cstData prepend e
  go bvarCtx e



def getLevel (gnodeTypes : List (Array CExpr)) (gnodeTypesHandler : Nat → (Nat × Nat))
  (ltxTypes : List (Array EmbedData)) (current : Option (Array EmbedData))
  (cstData : CTrie CstInfo) (bvarCtx : List CExpr)
  (type : CExpr) : Level :=
  let typeType :=
    cexprWhnf gnodeTypes gnodeTypesHandler ltxTypes current cstData bvarCtx
      (cexprInferType gnodeTypes gnodeTypesHandler ltxTypes current cstData bvarCtx type)
  match typeType with
  | .sort lvl => lvl
  | _ => .mvar ⟨`failed⟩

def cInferForallType (gnodeTypes : List (Array CExpr)) (gnodeTypesHandler : Nat → (Nat × Nat))
  (ltxTypes : List (Array EmbedData)) (current : Option (Array EmbedData))
  (cstData : CTrie CstInfo) (bvarCtx : List CExpr)
  (e : CExpr) : CExpr :=
  let rec go (prepend : List CExpr) (sofar : List Level) : CExpr → List Level
    | .forallE _ t b _ => go (t :: prepend) ((getLevel gnodeTypes gnodeTypesHandler ltxTypes current cstData prepend t) :: sofar) b
    | e => (getLevel gnodeTypes gnodeTypesHandler ltxTypes current cstData prepend e) :: sofar
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
  (gnodeTypes : List (Array CExpr)) (gnodeTypesHandler : Nat → (Nat × Nat))
  (ltxTypes : List (Array EmbedData)) (current : Option (Array EmbedData))
  (cstData : CTrie CstInfo) (bvarCtx : List CExpr)
  (e : CExpr) : CExpr :=
  match e with
  | .const c us    => cInferConstType cstData c us
  | .proj n i s    => cInferProjType gnodeTypes gnodeTypesHandler ltxTypes current cstData bvarCtx n i s
  | .app ..      => let (h,as) := CExpr.getApp e ; cInferAppType gnodeTypes gnodeTypesHandler ltxTypes current cstData bvarCtx h as
  | .bvar bidx     =>
        match bvarCtx.get? bidx with
        | .some T => T
        | _ => .failed
  | .lit v         => Literal.ctype v
  | .sort lvl      => .sort (mkLevelSucc lvl)
  | .forallE ..    => cInferForallType gnodeTypes gnodeTypesHandler ltxTypes current cstData bvarCtx e
  | .lam ..        => cInferLambdaType gnodeTypes gnodeTypesHandler ltxTypes current cstData bvarCtx e
  | .letE ..       => cInferLambdaType gnodeTypes gnodeTypesHandler ltxTypes current cstData bvarCtx e
  | .gnode gidx _ =>
        let (p,i) := gnodeTypesHandler gidx
        (gnodeTypes.get! p).get! i
  | .lnode pos _ tag =>
        match tag with
        | .none =>
            match current with
            | .none => .failed
            | .some thmdata => (thmdata.get! pos).cexpr
        | .some backId =>
            match ltxTypes.get? backId with
            | .none => .failed
            | .some thmdata => (thmdata.get! pos).cexpr
  | .failed => .failed

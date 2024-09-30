
import LeanGrow.F.Data.CExpr.Types



def CExpr.toStringImp : CExpr → String
| .node i d => s!"CExpr.node {i} {instToStringFormat.toString (repr d)}"
| .bvar i =>  s!"CExpr.bvar {i} "
| .sort l => s!"CExpr.sort {l} "
| .const n ll => s!"CExpr.const {n} {ll}"
| .app f a => s!"(CExpr.app {f.toStringImp} {a.toStringImp})"
| .lam _ t b _ => s!"CExpr.lam {t.toStringImp} {b.toStringImp}"
| .forallE _ t b _ => s!"CExpr.forallE {t.toStringImp} {b.toStringImp}"
| .letE _ t v b _ => s!"CExpr.letE {t.toStringImp} {v.toStringImp} {b.toStringImp}"
| .lit l => s!"CExpr.lit {instToStringFormat.toString (repr l)}"
| .proj t i b => s!"CExpr.proj {t} {i} {b.toStringImp}"
| .wrapInst e => s!"CExpr.wrapInst {CExpr.toStringImp e}"
| .failed => "CExpr.failed"

instance : ToString CExpr where
  toString := CExpr.toStringImp

#synth ToString CExpr



def OriginalData.toString : OriginalData → String
| .ofBvar n => s!"OriginalData.ofBvar {n}"
| .ofFvar fv => s!"OriginalData.ofFvar ⟨`{fv.name}⟩"

def kill_hygiene : Name → String
| .num _ _ => "hopeItWorks"
| n => s!"{n}"


def CExpr.toGoodString : CExpr → String
| .node i d => s!"CExpr.node {i} ({OriginalData.toString d})"
| .bvar i =>  s!"CExpr.bvar {i} "
| .sort l => s!"CExpr.sort ({Level.toString l}) "
| .const n ll => s!"CExpr.const `{kill_hygiene n} [{String.intercalate "," (ll.map Level.toString)}]"
| .app f a => s!"CExpr.app ({CExpr.toGoodString f}) ({CExpr.toGoodString a})"
| .lam n t b B => s!"CExpr.lam `{kill_hygiene n} ({CExpr.toGoodString t}) ({CExpr.toGoodString b}) {BinderInfo.toString B}"
| .forallE n t b B => s!"CExpr.forallE `{kill_hygiene n} ({CExpr.toGoodString t}) ({CExpr.toGoodString b}) {BinderInfo.toString B}"
| .letE n t v b B => s!"CExpr.letE `{kill_hygiene n} ({CExpr.toGoodString t}) ({CExpr.toGoodString v}) ({CExpr.toGoodString b}) {Bool.toString B}"
| .proj n i b => s!"CExpr.proj `{kill_hygiene n} {i} ({CExpr.toGoodString b})"
| .lit (Literal.strVal s) => s!"CExpr.lit (Lean.Literal.strVal \"{s}\")"
| .lit (Literal.natVal n) => s!"CExpr.lit (Lean.Literal.natVal {n})"
| .wrapInst e => s!"CExpr.wrapInst ({CExpr.toGoodString e})"
| .failed => "CExpr.failed"

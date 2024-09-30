
import Lean.Expr

open Lean

def Level.toString : Level → String
  | .zero  => s!"Lean.Level.zero "
  | .succ l => s!"Lean.Level.succ ({Level.toString l})"
  | .max l r    => s!"Lean.Level.max ({Level.toString l}) ({Level.toString r})"
  | .imax l r  => s!"Lean.Level.imax ({Level.toString l}) ({Level.toString r})"
  | .param n => s!"Lean.Level.param `{n}"
  | .mvar i  => s!"Lean.Level.mvar ⟨`{i.name}⟩ "


def BinderInfo.toString : BinderInfo → String
  | .default => "Lean.BinderInfo.default"
  | .implicit => "Lean.BinderInfo.implicit"
  | .strictImplicit => "Lean.BinderInfo.strictImplicit"
  | .instImplicit => "Lean.BinderInfo.instImplicit"


def Bool.toString : Bool → String
| true => "true"
| false => "false"


def Expr.toString : Expr → String
| .bvar i => s!"Lean.Expr.bvar {i}"
| .fvar i => s!"Lean.Expr.fvar ⟨`{i.name}⟩"
| .mvar i => s!"Lean.Expr.mvar ⟨`{i.name}⟩"
| .sort l => s!"Lean.Expr.sort ({Level.toString l})"
| .const n l => s!"Lean.Expr.const `{n} [{String.intercalate "," (l.map Level.toString)}]"
| .app l r => s!"Lean.Expr.app ({Expr.toString l}) ({Expr.toString r})"
| .lam n t b B => s!"Lean.Expr.lam `{n} ({Expr.toString t}) ({Expr.toString b}) {BinderInfo.toString B}"
| .forallE n t b B => s!"Lean.Expr.forallE `{n} ({Expr.toString t}) ({Expr.toString b}) {BinderInfo.toString B}"
| .letE n t v b B => s!"Lean.Expr.letE `{n} ({Expr.toString t}) ({Expr.toString v}) ({Expr.toString b}) {Bool.toString B}"
| .proj n i b => s!"Lean.Expr.proj `{n} {i} ({Expr.toString b})"
| .mdata _ e => Expr.toString e
| .lit (Literal.strVal s) => s!"Lean.Expr.lit (Lean.Literal.strVal \"{s}\")"
| .lit (Literal.natVal n) => s!"Lean.Expr.lit (Lean.Literal.natVal {n})"

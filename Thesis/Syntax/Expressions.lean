import Thesis.Semantics.StructuredWords
import Thesis.Semantics.Operators

namespace Expr

open StructuredWords
open Operators

-- Definition 4.1.1 (Expression syntax).
inductive Expr (α : Type) : Type
| empty : Expr α
| unit : Expr α
| top : Expr α
| symbol : α → Expr α
| plus : Expr α → Expr α → Expr α
| intersection : Expr α → Expr α → Expr α
| complement : Expr α → Expr α → Expr α
| mult : Expr α → Expr α → Expr α
| star : Expr α → Expr α → Expr α
| lb : Expr α → Expr α
| la : Expr α → Expr α
| mStep : Expr α → Expr α
| laStep : Expr α → Expr α
deriving Repr

notation "∅" => Expr.empty
notation "I" => Expr.unit
notation "T" => Expr.top
prefix:max "#" => Expr.symbol
infixr:30 " + " => Expr.plus
infixl:55 " & " => Expr.intersection
infixl:30 " -" => Expr.complement
infixr:60 " • " => Expr.mult
postfix:max "*" => Expr.star
prefix:max "◁" => Expr.lb
prefix:max "▷" => Expr.la
prefix:max "↑ₘ" => Expr.mStep
prefix:max "↑ₗ" => Expr.laStep

-- Definition 4.1.2 (Denotational semantics ⟦·⟧).
def sem [DecidableEq α] (r : Expr α) : Lang α :=
  match r with
  | .empty => ∅
  | .unit => I
  | .top => T
  | .symbol x => # x
  | .plus r₁ r₂ => (sem r₁) ∪ (sem r₂)
  | .intersection r₁ r₂ => (sem r₁) ∩ (sem r₂)
  | .complement r₁ r₂ => (sem r₁) - (sem r₂)
  | .mult r₁ r₂ => (sem r₁) • (sem r₂)
  | .star r b => star (sem b) (sem r)
  | .lb r => lookbehind (sem r)
  | .la r => lookahead (sem r)
  | .mStep r => matchStep (sem r)
  | .laStep r => LAStep (sem r)

variable {α : Type} [DecidableEq α]

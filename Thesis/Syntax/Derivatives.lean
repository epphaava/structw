import Thesis.Syntax.Expressions

namespace ExprDerivatives

open Expr

-- Definition 4.2.1 (Expression derivatives).
mutual
def D [DecidableEq α] (a : α) : Expr α → Expr α
  | .empty | .unit | .lb _ | .la _ | .laStep _ => ∅
  | .top => ↑ₘT - ↑ₗT
  | .symbol b => if a = b then (↑ₘI - ↑ₗT) else ∅
  | .plus r₁ r₂ => (D a r₁) + (D a r₂)
  | .intersection r₁ r₂ => (D a r₁) & (D a r₂)
  | .complement r₁ r₂ => (D a r₁) - (D a r₂)
  | .mult r₁ r₂ => ((D a r₁) • (DLB a r₂)) + ((DLA a r₁) • (D a r₂))
  | .star r b => (Expr.star (DLA a r) I) • ((D a b) + ((D a r) • (Expr.star (DLB a r) (DLB a b))))
  | .mStep r => ↑ₘ (D a r)

  def DLB [DecidableEq α] (a : α) : Expr α → Expr α
    | .empty | .la _ | .mStep _ | .laStep _ => ∅
    | .unit => I - ↑ₗI
    | .top => T - (↑ₘT + ↑ₗT)
    | .symbol b => #b - (↑ₘ#b + ↑ₗ#b)
    | .plus r₁ r₂ => (DLB a r₁) + (DLB a r₂)
    | .intersection r₁ r₂ => (DLB a r₁) & (DLB a r₂)
    | .complement r₁ r₂ => (DLB a r₁) - (DLB a r₂)
    | .mult r₁ r₂ => DLB a r₁ • DLB a r₂
    | .star r b => .star (DLB a r) (DLB a b)
    | .lb r => ◁(D a r)

  def DLA [DecidableEq α] (a : α) : Expr α → Expr α
    | .empty | .symbol _ => ∅
    | .unit => ↑ₗI
    | .top => ↑ₗT
    | .plus r₁ r₂ => (DLA a r₁) + (DLA a r₂)
    | .intersection r₁ r₂ => (DLA a r₁) & (DLA a r₂)
    | .complement r₁ r₂ => (DLA a r₁) - (DLA a r₂)
    | .mult r₁ r₂ => (DLA a r₁) • (DLA a r₂)
    | .star r b => .star (DLA a r) (DLA a b)
    | .lb r => ↑ₗ(◁(DLA a r • ↑ₘI))
    | .la r => ▷(D a r)
    | .mStep r => ↑ₘ (DLA a r)
    | .laStep r => ↑ₗ (DLA a r)

end

-- Definition 4.2.2 — Iterated match derivative
def D_word [DecidableEq α] (w : List α) (r : Expr α) : Expr α :=
  match w with
  | [] => r
  | a :: tl => D_word tl (D a r)

def DLB_word [DecidableEq α] (w : List α) (r : Expr α) : Expr α :=
  match w with
  | [] => r
  | a :: tl => DLB_word tl (DLB a r)

-- Definition 4.2.2 — Iterated lookahead derivative
def DLA_word [DecidableEq α] (w : List α) (r : Expr α) : Expr α :=
  match w with
  | [] => r
  | a :: tl => DLA_word tl (DLA a r)

-- Definition 4.2.4 — Iterated existential derivative
def xD [DecidableEq α] (w : List α) (r : Expr α) : Expr α :=
  match w with
  | [] => r
  | hd :: tl => xD tl ((DLB hd r) + (D hd r) + (DLA hd r))

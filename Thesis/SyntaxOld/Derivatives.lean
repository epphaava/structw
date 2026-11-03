import Thesis.SyntaxOld.Expressions

namespace ExprDerivatives

open Expr

-- Definition 4.2.1 (Expression derivatives).
mutual
def D [DecidableEq α] (a : α) : Expr α → Expr α
  | .empty | .unit | .lb _ | .la _ | .laStep _ => ∅
  | .top => ↑₂T - ↑₃T
  | .symbol b => if a = b then (↑₂I - ↑₃T) else ∅
  | .plus r₁ r₂ => (D a r₁) + (D a r₂)
  | .intersection r₁ r₂ => (D a r₁) & (D a r₂)
  | .complement r₁ r₂ => (D a r₁) - (D a r₂)
  | .mult r₁ r₂ => ((D a r₁) • (DLB a r₂)) + ((DLA a r₁) • (D a r₂))
  | .star r b => (Expr.star (DLA a r) I) • ((D a b) + ((D a r) • (Expr.star (DLB a r) (DLB a b))))
  | .lbStep r => ↑₁ (D a r)
  | .mStep r => ↑₂ (D a r)

  def DLB [DecidableEq α] (a : α) : Expr α → Expr α
    | .empty | .la _ | .mStep _ | .laStep _ => ∅
    | .unit => ↑₁I - ↑₃I
    | .top => ↑₁T - (↑₂T + ↑₃T)
    | .symbol b => ↑₁#b - (↑₂#b + ↑₃#b)
    | .plus r₁ r₂ => (DLB a r₁) + (DLB a r₂)
    | .intersection r₁ r₂ => (DLB a r₁) & (DLB a r₂)
    | .complement r₁ r₂ => (DLB a r₁) - (DLB a r₂)
    | .mult r₁ r₂ => DLB a r₁ • DLB a r₂
    | .star r b => .star (DLB a r) (DLB a b)
    | .lb r => ◁(D a r)
    | .lbStep r => ↑₁(DLB a r)


  def DLA [DecidableEq α] (a : α) : Expr α → Expr α
    | .empty | .symbol _ => ∅
    | .unit => ↑₃I
    | .top => ↑₃T
    | .plus r₁ r₂ => (DLA a r₁) + (DLA a r₂)
    | .intersection r₁ r₂ => (DLA a r₁) & (DLA a r₂)
    | .complement r₁ r₂ => (DLA a r₁) - (DLA a r₂)
    | .mult r₁ r₂ => (DLA a r₁) • (DLA a r₂)
    | .star r b => .star (DLA a r) (DLA a b)
    | .lb r => ◁(DLA a r)
    | .la r => ▷(D a r)
    | .lbStep r => ↑₁ (DLA a r)
    | .mStep r => ↑₂ (DLA a r)
    | .laStep r => ↑₃ (DLA a r)

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

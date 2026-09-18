import Thesis.Semantics.StructuredWords

namespace Operators

open StructuredWords

-- Definition 3.3.1 (Structured word concatenation `wc`).

def wc {α} (u v w : Word α) : Prop :=
  match w with
  | Sum.inl ((x, xs), ys, zs) =>
    ∃ (pref: List α) (suff: List α),
      ys = pref ++ suff ∧
      u = Sum.inl ((x, xs), pref, suff ++ zs) ∧
      v = Sum.inl ((x, xs ++ pref), suff, zs)

  | Sum.inr (Sum.inl (n, (y, ys), zs)) =>
    ∃ pref suff, pref ++ suff = ys ∧
      (
        u = Sum.inr (Sum.inl (n, (y, pref), suff ++ zs)) ∧
        v = Sum.inl ((y, pref), suff, zs)
        ∨
        ∃ m k l, m + k = n ∧
        u = Sum.inr (Sum.inr (m, l, y :: ys ++ zs)) ∧
        v = Sum.inr (Sum.inl (k, (y, ys), zs))

      )

  | Sum.inr (Sum.inr (n, m, zs)) =>
    ∃ n₁ n₂ m₁', n₁ + n₂ = n ∧
    u = Sum.inr (Sum.inr (n₁, m + m₁', zs)) ∧
    v = Sum.inr (Sum.inr (n₂, m, zs))

-- Definition 3.3.2 (Language operators).
def empty {α} : Lang α := λ _ => False
notation "∅" => empty

def unit : Lang α := λ w =>
  match w with
  | Sum.inl (_, ys, _) => ys = []
  | Sum.inr (Sum.inl _) => False
  | Sum.inr (Sum.inr _) => True
notation "I" => unit

/- -- helper operator for unit
def unit_n (n : Nat) : Lang α := λ u =>
  match u with
  | Sum.inr (n', _) => n = n'
  | _ => False -/

def top : Lang α := λ _ => True
notation "T" => top

def symb {α} (a : α) : Lang α := λ w =>
  match w with
  | Sum.inl (_, ys, _) => ys = [a]
  | Sum.inr w =>
    match w with
    | Sum.inl (_, (y, []), _) => a = y
    | _ => False
prefix:max "#" => symb

def union (k l : Lang α) : Lang α := λ u =>
  k u ∨ l u
infixr:55 " ∪ " => union

def intersection (k l : Lang α) : Lang α := λ u =>
  k u ∧ l u
infixl:55 " ∩ " => intersection

def complement (k l : Lang α) : Lang α := λ u =>
  k u ∧ ¬ l u
infixl:30 " // " => complement

def concat {α} (k l : Lang α) : Lang α := λ w =>
  ∃ x y, k x ∧ l y ∧ wc x y w
infixr:60 " • " => concat

/- -- helper operator for star
inductive star_help {α} (l : Lang α) : Word α → Prop
| inUnit : ∀ n y, star_help l (Sum.inr (n, y))
| inConcat :
  ∀ x y w,
  l x →
  star_help l y →
  wc x y w →
  star_help l w
 -/
/- def star (l : Lang α) : Lang α :=
  star_help l
postfix:max "*" => star -/

def lb (l : Lang α) : Lang α := λ w =>
  match w with
  | Sum.inl (xs, [], []) => l (Sum.inr (Sum.inl (0, xs, [])))
  | Sum.inr (Sum.inr (0, 0, [])) => l (Sum.inr (Sum.inr (0, 0, [])))
  | _ => False
prefix:max "◁" => lb


def la (l : Lang α) : Lang α := λ w =>
  match w with
  | Sum.inr (Sum.inr (0, m, zs)) =>
    match zs with
    | [] => l (Sum.inr (Sum.inr (m, 0, [])))
    | z :: zs => l (Sum.inr (Sum.inl (m, (z, zs), [])))
  | _ => False
prefix:max "▷" => la

def matchStep (l : Lang α) : Lang α := λ w =>
  match w with
  | Sum.inr (Sum.inl (.succ n, ys, zs)) => l (Sum.inr (Sum.inl (n, ys, zs)))
  | Sum.inr (Sum.inr (.succ n, m, ys)) => l (Sum.inr (Sum.inr (n, m, ys)))
  | _ => False
--prefix:max "▹" => matchStep

def LAStep (l : Lang α) : Lang α := λ w =>
  match w with
  | Sum.inr (Sum.inr (n, .succ m, ys)) => l (Sum.inr (Sum.inr (n, m, ys)))
  | _ => False
--prefix:max "▹" => LAStep


end Operators

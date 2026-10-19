import Thesis.Semantics.«1_StructuredWords»

namespace Operators

open StructuredWords

-- Definition 3.3.1 (Structured word concatenation `wc`).

def wc {α} (u v w : Word α) : Prop :=
  match w with
  | .left lb main la =>
    ∃ pref suff, main = pref ++ suff ∧
    u = .left lb pref (suff ++ la) ∧
    v = .left (lb.1, lb.2 ++ pref) suff la
  | .middle mcount main la =>
    (∃ pref suff, main.2 = pref ++ suff ∧
    u = .middle mcount (main.1, pref) (suff ++ la) ∧
    v = .left (main.1, pref) suff la)
    ∨
    ∃ mc₁ mc₂, mc₁ + mc₂ = mcount ∧
    u = .right mc₁ mc₂ (toList main ++ la) ∧
    v = .middle mc₂ main la

  | .right mcount lacount la =>
    ∃ mc₁ mc₂, mcount = mc₁ + mc₂ ∧
    u = .right mc₁ (mc₂ + lacount) la ∧
    v = .right mc₂ lacount la

-- Definition 3.3.2 (Language operators).
def empty {α} : Lang α := λ _ => False
notation "∅" => empty

def unit : Lang α := λ w =>
  match w with
  | .left _ main _ => main = []
  | .middle _ _ _ => False
  | .right mcount _ _ =>  mcount = 0
notation "I" => unit

def top : Lang α := λ _ => True
notation "T" => top

def symb {α} (a : α) : Lang α := λ w =>
  match w with
  | .left _ main _ => main = [a]
  | .middle 0 (y, []) _ => a = y
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
infixl:30 " - " => complement

def concat {α} (k l : Lang α) : Lang α := λ w =>
  ∃ x y, k x ∧ l y ∧ wc x y w
infixr:60 " • " => concat

-- helper operator for star
inductive star_help {α} (base : Lang α) (l : Lang α) : Word α → Prop
| inUnit : ∀ w, base w → star_help base l w
| inConcat :
  ∀ w₁ w₂ w,
  l w₁ →
  star_help base l w₂ →
  wc w₁ w₂ w →
  star_help base l w

def star (base l : Lang α) : Lang α :=
  star_help base l

def lookbehind (l : Lang α) : Lang α := λ w =>
  match w with
  | .left lb [] la => ∃ mc, l (.middle mc lb la)
  | .right 0 0 la => ∃ mc, l (.right mc 0 la)
  | _ => False
prefix:max "◁" => lookbehind


def lookahead (l : Lang α) : Lang α := λ w =>
  match w with
  | .right 0 lacount la =>
    match la with
    | [] => l (.right lacount 0 [])
    | z :: zs => l (.middle lacount (z, zs) [])
  | _ => False
prefix:max "▷" => lookahead

def matchStep (l : Lang α) : Lang α := λ w =>
  match w with
  | .middle (.succ mcount) main la => l (.middle mcount main la)
  | .right (.succ mcount) lacount la => l (.right mcount lacount la)
  | _ => False
prefix:max "▹ₘ" => matchStep

def LAStep (l : Lang α) : Lang α := λ w =>
  match w with
  | .right mcount (.succ lacount) la => l (.right mcount lacount la)
  | _ => False
prefix:max "▹ₗ" => LAStep

end Operators

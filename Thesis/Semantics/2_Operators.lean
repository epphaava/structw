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
  | .middle mc main la =>
    (∃ pref suff, main.2 = pref ++ suff ∧
    u = .middle mc (main.1, pref) (suff ++ la) ∧
    v = .left (main.1, pref) suff la)
    ∨
    ∃ mc₁ mc₂, mc₁ + mc₂ = mc ∧
    u = .right mc₁ mc₂ (toList main ++ la) ∧
    v = .middle mc₂ main la
  | .right mc lac la =>
    ∃ mc₁ mc₂, mc = mc₁ + mc₂ ∧
    u = .right mc₁ (mc₂ + lac) la ∧
    v = .right mc₂ lac la

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
inductive star_help {α} (l : Lang α) (base : Lang α) : Word α → Prop
| inUnit : ∀ w, base w → star_help l base w
| inConcat :
  ∀ w₁ w₂ w,
  l w₁ →
  star_help l base w₂ →
  wc w₁ w₂ w →
  star_help l base w

def star (l base : Lang α) : Lang α :=
  star_help l base

def lookbehind (l : Lang α) : Lang α := λ w =>
  match w with
  | .left lb [] la => ∃ lbc, l (.middle lbc lb la)
  | .right 0 lac la => ∃ lbc, l (.right lbc lac la)
  | _ => False
prefix:max "◁" => lookbehind

def lookahead (l : Lang α) : Lang α := λ w =>
  match w with
  | .left lb [] la => l (.left lb la [])
  | .right 0 lac la =>
    match la with
    | [] => l (.right lac 0 [])
    | z :: zs => l (.middle lac (z, zs) [])
  | _ => False
prefix:max "▷" => lookahead

/- def lbStep (l : Lang α) : Lang α := λ w =>
  match w with
  | .left (.succ lbc) lb main la => l (.left lbc lb main la)
  | .middle (.succ lbc) mc main la => l (.middle lbc mc main la)
  | .right (.succ lbc) mc lac la => l (.right lbc mc lac la)
  | _ => False
prefix:max "↑₁" => lbStep -/

def matchStep (l : Lang α) : Lang α := λ w =>
  match w with
  | .middle (.succ mcount) main la => l (.middle mcount main la)
  | .right (.succ mcount) lacount la => l (.right mcount lacount la)
  | _ => False
prefix:max "↑₂" => matchStep

def laStep (l : Lang α) : Lang α := λ w =>
  match w with
  | .right mcount (.succ lacount) la => l (.right mcount lacount la)
  | _ => False
prefix:max "↑₃" => laStep

end Operators

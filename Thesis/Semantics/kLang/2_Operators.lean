import Thesis.Semantics.kLang.«1_StructuredWords»
import Thesis.Semantics.Lang.«2_Operators»

namespace kOperators

open StructuredWords
open kStructuredWords
open Operators

theorem wc_steps {u v w : Word α} (h : wc u v w) : w.word_steps ≤ u.word_steps := by
  cases w with
  | left => simp [word_steps]
  | middle _ _ _ => rcases h with ⟨_, _, _, rfl, rfl⟩ | ⟨mc₁, mc₂, hmc, rfl, rfl⟩ <;> simp [word_steps]; omega
  | right mc lac la =>
    obtain ⟨mc₁, mc₂, hmc, rfl, rfl⟩ := h
    simp [word_steps]; omega

-- Definition 3.3.2 (Language operators), restricted to kLang.

def empty : kLang α n := ⟨∅, λ _ h => h.elim⟩
notation "∅" => empty

def unit : kLang α n := ⟨λ w => w.word_steps ≤ n ∧ I w, λ _ h => h.1⟩
notation "I" => unit

def top : kLang α n := ⟨λ w => w.word_steps ≤ n, λ _ h => h⟩
notation "T" => top

def symb {α} (a : α) : kLang α n := ⟨#a, λ w h => by
  match w with
  | .left .. => simp [word_steps]
  | .middle 0 .. => simp [word_steps]
  | .middle (_ + 1) .. | .right .. => simp [Operators.symb] at h⟩
prefix:max "#" => symb

def union (k l : kLang α n) : kLang α n := ⟨k.1 ∪ l.1, λ w h => h.elim (k.2 w) (l.2 w)⟩
infixr:55 " ∪ " => union

def intersection (k l : kLang α n) : kLang α n := ⟨k.1 ∩ l.1, λ w h => k.2 w h.1⟩
infixl:55 " ∩ " => intersection

def complement (k l : kLang α n) : kLang α n := ⟨k.1 - l.1, λ w h => k.2 w h.1⟩
infixl:30 " - " => complement

def concat {α} (k l : kLang α n) : kLang α n := ⟨k.1 • l.1, λ w h => by
  obtain ⟨u, v, hu, _, hwc⟩ := h
  exact Nat.le_trans (wc_steps hwc) (k.2 u hu)⟩
infixr:60 " • " => concat

def star (l base : kLang α n) : kLang α n := ⟨Operators.star l.1 base.1, λ w h => by
  cases h with
  | inUnit _ hb => exact base.2 w hb
  | inConcat u v _ hu _ hwc => exact Nat.le_trans (wc_steps hwc) (l.2 u hu)⟩

def lookbehind (l : kLang α n) : kLang α n := ⟨◁ l.1, λ w h => by
  match w with
  | .left _ [] _ => simp [word_steps]
  | .right 0 lac la =>
    obtain ⟨_, hl⟩ := h
    have hb := l.2 _ hl; simp [word_steps] at hb ⊢; omega⟩
prefix:max "◁" => lookbehind

def lookahead (l : kLang α n) : kLang α n := ⟨▷ l.1, λ w h => by
  match w with
  | .left _ [] _ => simp [word_steps]
  | .right 0 lac [] => have := l.2 _ h; simp [word_steps] at ⊢ this; exact this
  | .right 0 lac (_ :: _) => have := l.2 _ h; simp [word_steps] at ⊢ this; exact this⟩
prefix:max "▷" => lookahead

def matchStep (l : kLang α n) : kLang α (n.succ) := ⟨↑₂ l.1, λ w h => by
  match w with
  | .middle (_ + 1) .. => have hb := l.2 _ h; simp [word_steps] at hb ⊢; omega
  | .right (_ + 1) .. => have hb := l.2 _ h; simp [word_steps] at hb ⊢; omega⟩
prefix:max "↑₂" => matchStep

def laStep (l : kLang α n) : kLang α (n.succ) := ⟨↑₃ l.1, λ w h => by
  match w with
  | .right _ (_ + 1) _ => have hb := l.2 _ h; simp [word_steps] at hb ⊢; omega⟩
prefix:max "↑₃" => laStep

end kOperators

import Thesis.Syntax.«1_Expressions»
import Thesis.Syntax.«2_Derivatives»
import Thesis.Semantics.kLang.«3_Derivatives»
import Thesis.Semantics.kLang.«5_LookbehindDerivativeLaws»
import Thesis.Semantics.kLang.«6_LookaheadDerivativeLaws»
import Thesis.Semantics.kLang.«7_DerivativeLaws»

namespace DerCorrectHelpers

open SRegex
open SRegexDerivatives

open derLaws
open StructuredWords
open kStructuredWords
open kOperators
open Operators (star_help)

theorem atom_iff {α} [DecidableEq α] (n : Nat) (ss : List Steps) (l : Lang α) (w : Word α) :
    sem.atom n ss l w ↔ w.word_steps ≤ n ∧ ∃ s ∈ ss, sem.steps s l w := Iff.rfl

theorem atom_map_iff {α} [DecidableEq α] (n : Nat) (f : Steps → Steps) (ss : List Steps) (l : Lang α) (w : Word α) :
    sem.atom n (ss.map f) l w ↔ w.word_steps ≤ n ∧ ∃ s ∈ ss, sem.steps (f s) l w := by
  simp only [sem.atom]
  constructor
  · rintro ⟨hb, t, ht, h⟩; obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht; exact ⟨hb, s, hs, h⟩
  · rintro ⟨hb, s, hs, h⟩; exact ⟨hb, f s, List.mem_map.mpr ⟨s, hs, rfl⟩, h⟩



theorem concat_congr {α} {k₁ k₂ l₁ l₂ : kLang α n} (hk : k₁ ≐ k₂) (hl : l₁ ≐ l₂) :  k₁ • l₁ ≐ k₂ • l₂ := by
  intro w
  constructor
  · rintro ⟨x, y, hx, hy, hc⟩; exact ⟨x, y, (hk x).mp hx, (hl y).mp hy, hc⟩
  · rintro ⟨x, y, hx, hy, hc⟩; exact ⟨x, y, (hk x).mpr hx, (hl y).mpr hy, hc⟩

theorem star_congr {α} {l₁ l₂ b₁ b₂ : kLang α n} (hl : l₁ ≐ l₂) (hb : b₁ ≐ b₂) : star l₁ b₁ ≐ star l₂ b₂ := by
  intro w
  constructor
  · intro h
    induction h with
    | inUnit w hu => exact star_help.inUnit w ((hb w).mp hu)
    | inConcat w₁ w₂ w h₁ _ hwc ih => exact star_help.inConcat w₁ w₂ w ((hl w₁).mp h₁) ih hwc
  · intro h
    induction h with
    | inUnit w hu => exact star_help.inUnit w ((hb w).mpr hu)
    | inConcat w₁ w₂ w h₁ _ hwc ih => exact star_help.inConcat w₁ w₂ w ((hl w₁).mpr h₁) ih hwc

@[simp] theorem symb_left {α} (a : α) (lb : NEList α) (main la : List α) :
    Operators.symb a (.left lb main la) ↔ main = [a] := by simp [Operators.symb]

@[simp] theorem symb_middle {α} (a y : α) (mc : Nat) (l la : List α) : Operators.symb a (.middle mc (y, l) la) ↔ mc = 0 ∧ l = [] ∧ a = y := by
  rcases mc with _ | _ <;> rcases l with _ | _ <;> simp [Operators.symb]

@[simp] theorem symb_right {α} (a : α) (mc lac : Nat) (la : List α) :
    ¬ Operators.symb a (.right mc lac la) := by simp [Operators.symb]

end DerCorrectHelpers

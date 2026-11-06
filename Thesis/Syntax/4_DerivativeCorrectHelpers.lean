import Thesis.Syntax.«1_Expressions»
import Thesis.Syntax.«2_Derivatives»
import Thesis.Semantics.«3_Derivatives»
import Thesis.Semantics.«5_LookbehindDerivativeLaws»
import Thesis.Semantics.«6_LookaheadDerivativeLaws»
import Thesis.Semantics.«7_DerivativeLaws»

namespace DerCorrectHelp

open SRegex
open SRegexDerivatives

open DerLaws
open StructuredWords
open Operators

theorem atom_iff {α} [DecidableEq α] (ss : List Steps) (l : Lang α) (w : Word α) : sem.atom ss l w ↔ ∃ s ∈ ss, sem.steps s l w := by
  induction ss with
  | nil => simp [sem.atom, empty]
  | cons s ss ih => simp [sem.atom, union, ih]

theorem atom_map_iff {α} [DecidableEq α] (f : Steps → Steps) (ss : List Steps) (l : Lang α) (w : Word α) : sem.atom (ss.map f) l w ↔ ∃ s ∈ ss, sem.steps (f s) l w := by
  induction ss with
  | nil => simp [sem.atom, empty]
  | cons s ss ih => simp [sem.atom, union, ih]



theorem concat_congr {α} {k₁ k₂ l₁ l₂ : Lang α} (hk : k₁ ≐ k₂) (hl : l₁ ≐ l₂) :  k₁ • l₁ ≐ k₂ • l₂ := by
  intro w
  constructor
  · rintro ⟨x, y, hx, hy, hc⟩; exact ⟨x, y, (hk x).mp hx, (hl y).mp hy, hc⟩
  · rintro ⟨x, y, hx, hy, hc⟩; exact ⟨x, y, (hk x).mpr hx, (hl y).mpr hy, hc⟩

theorem star_congr {α} {l₁ l₂ b₁ b₂ : Lang α} (hl : l₁ ≐ l₂) (hb : b₁ ≐ b₂) : star l₁ b₁ ≐ star l₂ b₂ := by
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

@[simp] theorem symb_left {α} (a : α) (lbc : Nat) (lb : NEList α) (main la : List α) :
    symb a (.left lbc lb main la) ↔ main = [a] := by simp [symb]

@[simp] theorem symb_middle {α} (a y : α) (lbc mc : Nat) (l la : List α) : symb a (.middle lbc mc (y, l) la) ↔ mc = 0 ∧ l = [] ∧ a = y := by
  rcases mc with _ | _ <;> rcases l with _ | _ <;> simp [symb]

@[simp] theorem symb_right {α} (a : α) (lbc mc lac : Nat) (la : List α) :
    ¬ symb a (.right lbc mc lac la) := by simp [symb]

end DerCorrectHelp

import Thesis.Semantics.StructuredWords
import Thesis.Semantics.Operators
import Thesis.Semantics.Derivatives

namespace DerLaws

open StructuredWords
open Operators

-- Proposition 3.4.1 (Derivative laws for structured languages).

theorem derLA_empty (a : α) : derLA a ∅ ≐ ∅ := by
  intro w
  match w with
  | .left _ _ _ => simp [derLA, empty]
  | .middle mcount _ _ => cases mcount <;> simp [derLA, empty]
  | .right mcount lacount _ => cases mcount <;> cases lacount <;> simp [derLA, empty]

theorem derLA_unit (a : α) : derLA a I ≐ ▹ₗ I := by
  intro w
  match w with
  | .left _ _ _   => simp [LAStep, derLA]
  | .middle mcount _ _  => cases mcount <;> simp [LAStep, derLA]
  | .right mcount lacount _ => cases mcount <;> cases lacount <;> simp [LAStep, derLA, unit]


theorem derLA_top (a : α) : derLA a T ≐ LAStep T := by
  intro w
  match w with
  | .left _ _ _   => simp [derLA, LAStep]
  | .middle mcount _ _  => cases mcount <;> simp [derLA, LAStep]
  | .right mcount lacount _ => cases mcount <;> cases lacount <;> simp [derLA, LAStep, top]

theorem derLA_symb (a b : α) : derLA b (#a) ≐ ∅ := by
  intro w
  match w with
  | .left _ _ _   => simp [derLA, empty]
  | .middle mcount _ _  => cases mcount <;> simp [derLA, empty]
  | .right mcount lacount _ => cases mcount <;> cases lacount <;> simp [derLA, empty, symb]

theorem derLA_union (a : α) (k l : Lang α) : derLA a (k ∪ l) ≐ derLA a k ∪ derLA a l := by
  intro w
  match w with
  | .left _ _ _   => simp [derLA, union]
  | .middle mcount _ _  => cases mcount <;> simp [derLA, union]
  | .right mcount lacount _ => cases mcount <;> cases lacount <;> simp [derLA, union]

theorem derLA_intersection (a : α) (k l : Lang α): derLA a (k ∩ l) ≐ (derLA a k) ∩ (derLA a l) := by
  intro w
  match w with
  | .left _ _ _   => simp [derLA, intersection]
  | .middle mcount _ _  => cases mcount <;> simp [derLA, intersection]
  | .right mcount lacount _ => cases mcount <;> cases lacount <;> simp [derLA, intersection]

theorem derLA_complement (a : α) (k l : Lang α): derLA a (k // l) ≐ ((derLA a k) // (derLA a l)) := by
  intro w
  match w with
  | .left _ _ _   => simp [derLA, complement]
  | .middle mcount _ _  => cases mcount <;> simp [derLA, complement]
  | .right mcount lacount _ => cases mcount <;> cases lacount <;> simp [derLA, complement]

theorem derLA_concat (a : α) (k l : Lang α) : derLA a (k • l) ≐ derLA a k • derLA a l := by
  intro w
  match w with
  | .left lb main la =>
    constructor
    . intro h; simp [derLA] at h
    . intro h; obtain ⟨w₁, _, hk, _, _, _, _, _, _⟩ := h; subst w₁; simp [derLA] at hk
  | .middle mcount _ _  =>
    constructor
    . intro h; simp [derLA] at h
    . intro h; obtain ⟨w₁, w₂, hk, hl, _, _, h⟩ := h;
      cases h with
      | inl h => obtain ⟨_, _, _⟩ := h; subst w₁; simp [derLA] at hk
      | inr h => obtain ⟨_, _, _, _, _⟩ := h; subst w₂; simp [derLA] at hl
  | .right mcount lacount la =>
    constructor
    . intro h
      cases lacount with
      | zero => simp [derLA] at h
      | succ lacount =>
        obtain ⟨w₁, w₂, hk, hl, mc₁, mc₂, hmcount, _, _⟩ := h; subst w₁ w₂; exact ⟨.right mc₁ (mc₂ + lacount).succ la, .right mc₂ lacount.succ la, hk, hl, mc₁, mc₂, hmcount, rfl, rfl⟩
    . intro h
      obtain ⟨w₁, w₂, hk, hl, mc₁, mc₂, hmcount, _, _⟩ := h; subst w₁ w₂ mcount
      cases lacount with
      | zero => simp [derLA] at hl
      | succ lacount => exact ⟨.right mc₁ (mc₂ + lacount) (a :: la), .right mc₂ lacount (a :: la), hk, hl, mc₁, mc₂, rfl, rfl, rfl⟩

/-
theorem derLA_star (a : α) (l : Lang α) : derLA a (l*) ≐ ▹I ∪ derLA a l := by
  intro w
  match w with
  | Sum.inl w => simp [derLA, union, step]
  | Sum.inr (n, v) =>
    cases n with
    | zero => simp [derLA, union, step]
    | succ n =>
      constructor
      · intro h
        left
        refine ⟨n, rfl, ?_⟩
        trivial
      · intro _
        exact star_help.inUnit (l := l) n (a :: v)
 -/

theorem derLA_lb (a : α) (l : Lang α) : derLA a (◁ l) ≐ ∅  := by
  intro w
  match w with
  | .left _ _ _   => simp [derLA, empty]
  | .middle mcount _ _  => cases mcount <;> simp [derLA, empty]
  | .right mcount lacount _ => cases mcount <;> cases lacount <;> simp [derLA, lookbehind, empty]

theorem derLA_la (a : α) (l : Lang α) : derLA a (▷ l) ≐ ▷ (der a l)  := by
  intro w
  match w with
  | .left _ _ _  => simp [derLA, lookahead]
  | .middle mcount _ _  => cases mcount <;> simp [derLA, lookahead]
  | .right mcount lacount la => cases mcount <;> cases lacount <;> cases la <;> simp [derLA, lookahead, der, toList]

theorem derLA_matchStep (a : α) (l : Lang α) : derLA a (matchStep l) ≐ matchStep (derLA a l) := by
  intro w
  match w with
  | .left _ _ _   => simp [derLA, matchStep]
  | .middle mcount _ _  =>
    cases mcount with
    | zero => simp [derLA, matchStep]
    | succ mcount => cases mcount <;> simp [derLA, matchStep]
  | .right mcount lacount _ =>
    cases mcount with
    | zero => cases lacount <;> simp [derLA, matchStep]
    | succ mcount => cases mcount <;> cases lacount <;> simp [derLA, matchStep]

theorem derLA_LAStep (a : α) (l : Lang α) : derLA a (LAStep l) ≐ LAStep (derLA a l) := by
  intro w
  match w with
  | .left _ _ _   => simp [derLA, LAStep]
  | .middle mcount _ _  =>
    cases mcount with
    | zero => simp [derLA, LAStep]
    | succ mcount => cases mcount <;> simp [derLA, LAStep]
  | .right mcount lacount _ =>
    cases lacount with
    | zero => cases mcount <;> simp [derLA, LAStep]
    | succ lacount => cases lacount <;> simp [derLA, LAStep]

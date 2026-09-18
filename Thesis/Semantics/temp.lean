import Thesis.Semantics.StructuredWords
import Thesis.Semantics.Operators
import Thesis.Semantics.Derivatives


open StructuredWords
open Operators


theorem derLA_concat (a : α) (k l : Lang α) : derLA a (k • l) ≐ derLA a k • derLA a l := by
  intro w
  match w with
  | Sum.inl ((x, xs), ys, zs) =>
    constructor
    . intro h; simp [derLA] at h
    . intro h; obtain ⟨w₁, _, hk, _, _, _, _, _, _⟩ := h; subst w₁; simp [derLA] at hk
  | Sum.inr (Sum.inl (n, (y, ys), zs)) =>
    constructor
    . intro h; simp [derLA] at h
    . intro h; obtain ⟨w₁, w₂, hk, hl, _, _, _, h⟩ := h;
      cases h with
      | inl h => obtain ⟨_, _⟩ := h; subst w₁; simp [derLA] at hk
      | inr h => obtain ⟨_, _, _, _, _, _⟩ := h; subst w₂; simp [derLA] at hl
  | Sum.inr (Sum.inr (n, m, zs)) =>
    constructor
    . intro h
      cases m with
      | zero => simp [derLA] at h
      | succ m =>
        obtain ⟨w₁, w₂, hk, hl, n₁, n₂, m₁, _, _, _⟩ := h; subst w₁ w₂ n
        refine ⟨Sum.inr (Sum.inr (n₁, (m + m₁).succ , zs)), Sum.inr (Sum.inr (n₂, m.succ, zs)), hk, hl, n₁, n₂, m₁, rfl, ?_, rfl⟩
        sorry
    . intro h
      obtain ⟨w₁, w₂, hk, hl, n₁, n₂, m₁', _, _, _⟩ := h; subst w₁ w₂ n
      cases m with
      | zero => simp [derLA] at hl
      | succ m =>
        refine ⟨Sum.inr (Sum.inr (n₁, m + m₁', a :: zs)), Sum.inr (Sum.inr (n₂, m, a :: zs)), ?_, hl, n₁, n₂, m₁', rfl, rfl, rfl⟩
        sorry

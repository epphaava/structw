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
  | Sum.inl (xs, ys, zs) => simp [derLA, empty]
  | Sum.inr (Sum.inl (n, (y, ys), zs)) => cases n <;> simp [derLA, empty]
  | Sum.inr (Sum.inr (n, m, zs)) => cases n <;> cases m <;> simp [derLA, empty]

theorem derLA_unit (a : α) : derLA a I ≐ ▹ₗ I := by
  intro w
  match w with
  | Sum.inl (xs, ys, zs) => simp [LAStep, derLA]
  | Sum.inr (Sum.inl (n, (y, ys), zs)) => cases n <;> simp [LAStep, derLA]
  | Sum.inr (Sum.inr (n, m, zs)) => cases n <;> cases m <;> simp [LAStep, derLA, unit]


theorem derLA_top (a : α) : derLA a T ≐ LAStep T := by
  intro w
  match w with
  | Sum.inl (xs, ys, zs) => simp [derLA, LAStep]
  | Sum.inr (Sum.inl (n, (y, ys), zs)) => cases n <;> simp [derLA, LAStep]
  | Sum.inr (Sum.inr (n, m, zs)) => cases n <;> cases m <;> simp [derLA, LAStep, top]

theorem derLA_symb (a b : α) : derLA b (#a) ≐ ∅ := by
  intro w
  match w with
  | Sum.inl (xs, ys, zs) => simp [derLA, empty]
  | Sum.inr (Sum.inl (n, (y, ys), zs)) => cases n <;> simp [derLA, empty]
  | Sum.inr (Sum.inr (n, m, zs)) => cases n <;> cases m <;> simp [derLA, empty, symb]

theorem derLA_union (a : α) (k l : Lang α) : derLA a (k ∪ l) ≐ derLA a k ∪ derLA a l := by
  intro w
  match w with
  | Sum.inl (xs, ys, zs) => simp [derLA, union]
  | Sum.inr (Sum.inl (n, (y, ys), zs)) => cases n <;> simp [derLA, union]
  | Sum.inr (Sum.inr (n, m, zs)) => cases n <;> cases m <;> simp [derLA, union]

theorem derLA_intersection (a : α) (k l : Lang α): derLA a (k ∩ l) ≐ (derLA a k) ∩ (derLA a l) := by
  intro w
  match w with
  | Sum.inl (xs, ys, zs) => simp [derLA, intersection]
  | Sum.inr (Sum.inl (n, (y, ys), zs)) => cases n <;> simp [derLA, intersection]
  | Sum.inr (Sum.inr (n, m, zs)) => cases n <;> cases m <;> simp [derLA, intersection]

theorem derLA_complement (a : α) (k l : Lang α): derLA a (k // l) ≐ ((derLA a k) // (derLA a l)) := by
  intro w
  match w with
  | Sum.inl (xs, ys, zs) => simp [derLA, complement]
  | Sum.inr (Sum.inl (n, (y, ys), zs)) => cases n <;> simp [derLA, complement]
  | Sum.inr (Sum.inr (n, m, zs)) => cases n <;> cases m <;> simp [derLA, complement]

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
      | inr h => obtain ⟨_, _, _⟩ := h; subst w₂; simp [derLA] at hl
  | Sum.inr (Sum.inr (n, m, zs)) =>
    constructor
    . intro h
      cases n with
      | zero => simp [derLA] at h
      | succ n =>
        cases m with
        | zero => simp [derLA] at h
        | succ m => obtain ⟨w₁, w₂, hk, hl, m₁, _, _⟩ := h; subst w₁ w₂; exact ⟨Sum.inr (Sum.inr (n.succ, m₁.succ, zs)), Sum.inr (Sum.inr (m₁.succ, m.succ, zs)), hk, hl, m₁.succ, rfl, rfl⟩
    . intro h
      obtain ⟨w₁, w₂, hk, hl, m₁, _, _⟩ := h; subst w₁ w₂
      cases n with
      | zero => simp [derLA] at hk
      | succ n =>
        cases m₁ with
        | zero => simp [derLA] at hl
        | succ m₁ =>
          cases m with
          | zero => simp [derLA] at hl
          | succ m => exact ⟨Sum.inr (Sum.inr (n, m₁, a :: zs)), Sum.inr (Sum.inr (m₁, m, a :: zs)), hk, hl, m₁, rfl, rfl⟩

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

theorem derLA_lb (a : α) (l : Lang α) : derLA a (lb l) ≐ ∅  := by
  intro w
  match w with
  | Sum.inl (xs, ys, zs) => simp [derLA, empty]
  | Sum.inr (Sum.inl (n, (y, ys), zs)) => cases n <;> simp [derLA, empty]
  | Sum.inr (Sum.inr (n, m, zs)) => cases n <;> cases m <;> simp [derLA, lb, empty]

theorem derLA_la (a : α) (l : Lang α) : derLA a (la l) ≐ la (der a l)  := by
  intro w
  match w with
  | Sum.inl (xs, ys, zs) => simp [derLA, la]
  | Sum.inr (Sum.inl (n, (y, ys), zs)) => cases n <;> simp [derLA, la]
  | Sum.inr (Sum.inr (n, m, zs)) => cases n <;> cases m <;> cases zs <;> simp [derLA, la, der]

theorem derLA_matchStep (a : α) (l : Lang α) : derLA a (matchStep l) ≐ matchStep (derLA a l) := by
  intro w
  match w with
  | Sum.inl (xs, ys, zs) => simp [derLA, matchStep]
  | Sum.inr (Sum.inl (n, (y, ys), zs)) =>
    cases n with
    | zero => simp [derLA, matchStep]
    | succ n => cases n <;> simp [derLA, matchStep]
  | Sum.inr (Sum.inr (n, m, zs)) =>
    cases n with
    | zero => simp [derLA, matchStep]
    | succ n => cases n <;> cases m <;> simp [derLA, matchStep]


theorem derLA_LAStep (a : α) (l : Lang α) : derLA a (LAStep l) ≐ LAStep (derLA a l) := by
  intro w
  match w with
  | Sum.inl (xs, ys, zs) => simp [derLA, LAStep]
  | Sum.inr (Sum.inl (n, (y, ys), zs)) =>
    cases n with
    | zero => simp [derLA, LAStep]
    | succ n => cases n <;> simp [derLA, LAStep]
  | Sum.inr (Sum.inr (n, m, zs)) =>
    cases n with
    | zero => simp [derLA, LAStep]
    | succ n =>
      cases m with
      | zero =>
        cases n <;> simp [derLA, LAStep]
      | succ m =>
        cases n <;> cases m <;> simp [derLA, LAStep]

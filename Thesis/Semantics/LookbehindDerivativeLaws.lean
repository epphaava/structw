import Thesis.Semantics.StructuredWords
import Thesis.Semantics.Operators
import Thesis.Semantics.Derivatives

namespace derLBws

open StructuredWords
open Operators

-- Proposition 3.4.1 (Derivative laws for structured languages).

theorem derLB_empty (a : α) : derLB a ∅ ≐ ∅ := by
  intro w
  match w with
  | Sum.inl ((x, xs), ys, zs) => simp [derLB, empty]
  | Sum.inr (Sum.inl (n, (y, ys), zs)) => cases n <;> simp [derLB, empty]
  | Sum.inr (Sum.inr (n, m, zs)) => cases n <;> cases m <;> simp [derLB, empty]

theorem derLB_unit (a : α) : derLB a I ≐ (I // ▹ₗ I) := by
  intro w
  match w with
  | Sum.inl ((x, xs), ys, zs) => simp [complement, derLB, LAStep, unit]
  | Sum.inr (Sum.inl (n, (y, ys), zs)) => cases n <;> simp [complement, derLB, LAStep, unit]
  | Sum.inr (Sum.inr (n, m, zs)) => cases n <;> cases m <;> simp [complement, derLB, LAStep, unit]

theorem derLB_top (a : α) : derLB a T ≐ (T // (▹ T )) := by
  intro w
  match w with
  | Sum.inl ((x, xs), ys, zs) => simp [complement, derLB,  top]
  | Sum.inr (Sum.inl (n, (y, ys), zs)) =>
    cases n <;> simp [complement, union, top, matchStep, derLB, LAStep]
  | Sum.inr (Sum.inr (n, m, zs)) =>
    cases n with
    | zero =>
      cases m with
      | zero =>
        simp [complement, derLB, union, matchStep, matchStep, top, LAStep]

      | succ m =>
        simp [complement, derLB]

    | succ n =>
      cases m with
      | zero =>
        simp [complement, derLB, union, matchStep, matchStep, top, LAStep]

      | succ m =>
        simp [complement, derLB, union, matchStep, matchStep, top,  LAStep]


theorem derLB_symb (a b : α) : derLB b (#a) ≐ (#a // (matchStep #a ∪ LAStep #a)):= by
  intro w
  match w with
  | Sum.inl ((x, xs), ys, zs) => simp [derLB, complement, union, matchStep, LAStep, symb]
  | Sum.inr (Sum.inl (n, (y, ys), zs)) =>
    cases n with
    | zero =>
      cases ys <;> simp [derLB, complement, union, matchStep, LAStep, symb, Eq.symm]
    | succ n =>
      simp [derLB, complement, union, matchStep, LAStep, symb]
  | Sum.inr (Sum.inr (n, m, zs)) => cases n <;> cases m <;> simp [derLB, complement, union, matchStep, LAStep, symb]

theorem derLB_union (a : α) (k l : Lang α) : derLB a (k ∪ l) ≐ derLB a k ∪ derLB a l := by
  intro w
  match w with
  | Sum.inl ((x, xs), ys, zs) => simp [complement, derLB, union, LAStep, matchStep, unit]
  | Sum.inr (Sum.inl (n, (y, ys), zs)) => cases n <;> simp [complement, derLB, union, LAStep, matchStep, unit]
  | Sum.inr (Sum.inr (n, m, zs)) => cases n <;> cases m <;> simp [complement, derLB, union, LAStep, matchStep, unit]


theorem derLB_intersection (a : α) (k l : Lang α): derLB a (k ∩ l) ≐ (derLB a k) ∩ (derLB a l) := by
  intro w
  match w with
  | Sum.inl ((x, xs), ys, zs) => simp [complement, derLB, union, LAStep, matchStep, unit]
  | Sum.inr (Sum.inl (n, (y, ys), zs)) => cases n <;> simp [complement, derLB, union, LAStep, matchStep, unit]
  | Sum.inr (Sum.inr (n, m, zs)) => cases n <;> cases m <;> simp [complement, derLB, union, LAStep, matchStep, unit]
]

theorem derLB_complement (a : α) (k l : Lang α): derLB a (k // l) ≐ ((derLB a k) // (derLB a l)) := by
  intro w
  match w with
  | Sum.inl ((x, xs), ys, zs) => simp [complement, derLB, union, LAStep, matchStep, unit]
  | Sum.inr (Sum.inl (n, (y, ys), zs)) => cases n <;> simp [complement, derLB, union, LAStep, matchStep, unit]
  | Sum.inr (Sum.inr (n, m, zs)) => cases n <;> cases m <;> simp [complement, derLB, union, LAStep, matchStep, unit]

/-
theorem derLB_concat (a : α) (k l : Lang α) : derLB a (k • l) ≐ derLB a k • derLB a l := by
  intro w
  match w with
  | Sum.inl ((x, xs), ys, zs) =>
    constructor
    . intro h; simp [derLB] at h
    . intro h; obtain ⟨w₁, _, hk, _, _, _, _, _, _⟩ := h; subst w₁; simp [derLB] at hk
  | Sum.inr (Sum.inl (n, (y, ys), zs)) =>
    constructor
    . intro h; simp [derLB] at h
    . intro h; obtain ⟨w₁, w₂, hk, hl, _, _, _, h⟩ := h;
      cases h with
      | inl h => obtain ⟨_, _⟩ := h; subst w₁; simp [derLB] at hk
      | inr h => obtain ⟨_, _, _, _, _, _⟩ := h; subst w₂; simp [derLB] at hl
  | Sum.inr (Sum.inr (n, m, zs)) =>
    constructor
    . intro h
      cases m with
      | zero => simp [derLB] at h
      | succ m =>
        obtain ⟨w₁, w₂, hk, hl, n₁, n₂, m₁, _, _, _⟩ := h; subst w₁ w₂ n
        refine ⟨Sum.inr (Sum.inr (n₁, (m + m₁).succ , zs)), Sum.inr (Sum.inr (n₂, m.succ, zs)), hk, hl, n₁, n₂, m₁, rfl, ?_, rfl⟩
        sorry
    . intro h
      obtain ⟨w₁, w₂, hk, hl, n₁, n₂, m₁', _, _, _⟩ := h; subst w₁ w₂ n
      cases m with
      | zero => simp [derLB] at hl
      | succ m =>
        refine ⟨Sum.inr (Sum.inr (n₁, m + m₁', a :: zs)), Sum.inr (Sum.inr (n₂, m, a :: zs)), ?_, hl, n₁, n₂, m₁', rfl, rfl, rfl⟩
        sorry -/
/-
theorem derLB_star (a : α) (l : Lang α) : derLB a (l*) ≐ ▹I ∪ derLB a l := by
  intro w
  match w with
  | Sum.inl w => simp [derLB, union, step]
  | Sum.inr (n, v) =>
    cases n with
    | zero => simp [derLB, union, step]
    | succ n =>
      constructor
      · intro h
        left
        refine ⟨n, rfl, ?_⟩
        trivial
      · intro _
        exact star_help.inUnit (l := l) n (a :: v)
 -/

theorem derLB_la (a : α) (l : Lang α) : derLB a (la l) ≐ la (der a l) := by
  intro w
  cases w with
  | inl w =>
    cases w with | mk u v =>
      cases u with | mk hd tl => simp [derLB, la]
  | inr w =>
    match w with
    | Sum.inl (_, _, _) => simp [derLB, la]
    | Sum.inr (n, m, zs) =>
      cases m with
      | zero =>  cases n <;> cases zs <;> simp [derLB, la, der]
      | succ m => cases n <;> cases zs <;> simp [derLB, la, der]

theorem derLB_matchStep (a : α) (l : Lang α) : derLB a (matchStep l) ≐ matchStep (derLB a l) := by
  intro w
  cases w with
  | inl w =>
    cases w with | mk u v =>
      cases u with | mk hd tl => simp [matchStep, derLB]
  | inr w =>
    match w with
    | Sum.inl (n, ys, zs) => cases n <;> simp [derLB, matchStep]
    | Sum.inr (n, m, zs) => cases m <;> cases n <;> cases zs <;> simp [derLB, matchStep]

theorem derLB_LAStep (a : α) (l : Lang α) : derLB a (LAStep l) ≐ LAStep (derLB a l) := by
  intro w
  cases w with
  | inl w =>
    cases w with | mk u v =>
      cases u with | mk hd tl => simp [derLB, LAStep]
  | inr w =>
    match w with
    | Sum.inl (n, ys, zs) => cases n <;> simp [derLB, LAStep]
    | Sum.inr (n, m, zs) =>
      cases m with
      | zero => cases n <;> cases zs <;> simp [derLB,LAStep]
      | succ m => cases m <;> cases n <;> cases zs <;> simp [derLB,LAStep]

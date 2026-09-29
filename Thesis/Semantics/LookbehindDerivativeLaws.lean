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
  | .left _ _ _ => simp [derLB, empty]
  | .middle mcount _ _ => cases mcount <;> simp [derLB, empty]
  | .right mcount lacount _ => cases mcount <;> cases lacount <;> simp [derLB, empty]

theorem derLB_unit (a : α) : derLB a I ≐ (I // ▹ₗ I) := by
  intro w
  match w with
  | .left _ _ _ => simp [complement, derLB, LAStep, unit]
  | .middle mcount _ _ => cases mcount <;> simp [complement, derLB, LAStep, unit, toList]
  | .right mcount lacount _ => cases mcount <;> cases lacount <;> simp [complement, derLB, LAStep, unit]

theorem derLB_top (a : α) : derLB a T ≐ (T // (▹ₘ T ∪ ▹ₗ T )) := by
  intro w
  match w with
  | .left _ _ _ => simp [union, complement, derLB, matchStep, LAStep, top]
  | .middle mcount _ _ =>
    cases mcount <;> simp [union, complement, derLB, matchStep, LAStep, top]
  | .right mcount lacount _ => cases mcount <;> cases lacount <;> simp [union, complement, derLB, matchStep, LAStep, top]

theorem derLB_symb (a b : α) : derLB b (#a) ≐ (#a // (matchStep #a ∪ LAStep #a)):= by
  intro w
  match w with
  | .left _ _ _ => simp [derLB, complement, union, matchStep, LAStep, symb]
  | .middle mcount (y, ys) _ =>
    cases mcount with
    | zero => cases ys <;> simp [derLB, complement, union, matchStep, LAStep, symb, toList, Eq.comm]
    | succ n => simp [derLB, complement, union, matchStep, LAStep, symb]
  | .right mcount lacount _ => cases mcount <;> cases lacount <;> simp [derLB, complement, union, matchStep, LAStep, symb]

theorem derLB_union (a : α) (k l : Lang α) : derLB a (k ∪ l) ≐ derLB a k ∪ derLB a l := by
  intro w
  match w with
  | .left _ _ _ => simp [derLB, union]
  | .middle mcount _ _ => cases mcount <;> simp [derLB, union]
  | .right mcount lacount _ => cases mcount <;> cases lacount <;> simp [derLB, union]

theorem derLB_intersection (a : α) (k l : Lang α): derLB a (k ∩ l) ≐ (derLB a k) ∩ (derLB a l) := by
  intro w
  match w with
  | .left _ _ _ => simp [intersection, derLB]
  | .middle mcount _ _ => cases mcount <;> simp [intersection, derLB]
  | .right mcount lacount _ => cases mcount <;> cases lacount <;> simp [intersection, derLB]

theorem derLB_complement (a : α) (k l : Lang α): derLB a (k // l) ≐ ((derLB a k) // (derLB a l)) := by
  intro w
  match w with
  | .left _ _ _ => simp [complement, derLB]
  | .middle mcount _ _ => cases mcount <;> simp [complement, derLB]
  | .right mcount lacount _ => cases mcount <;> cases lacount <;> simp [complement, derLB]

/-
theorem derLB_concat (a : α) (k l : Lang α) : derLB a (k • l) ≐ derLB a k • derLB a l := by
  intro w
  match w with
  | .left _ _ _ =>
    constructor
    . intro h; simp [derLB] at h
    . intro h; obtain ⟨w₁, _, hk, _, _, _, _, _, _⟩ := h; subst w₁; simp [derLB] at hk
  | .middle mcount _ _ =>
    constructor
    . intro h; simp [derLB] at h
    . intro h; obtain ⟨w₁, w₂, hk, hl, _, _, _, h⟩ := h;
      cases h with
      | inl h => obtain ⟨_, _⟩ := h; subst w₁; simp [derLB] at hk
      | inr h => obtain ⟨_, _, _, _, _, _⟩ := h; subst w₂; simp [derLB] at hl
  | .right mcount lacount _ =>
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

theorem derLB_lb (a : α) (l : Lang α) : derLB a (◁ l) ≐ ◁ (der a l)  := by
  intro w
  match w with
  | .left (x, xs) main la =>
    constructor
    . intro h; cases main <;> cases la <;> obtain ⟨mc, h⟩ := h; exact ⟨mc.succ, h⟩
    . intro h; cases main <;> cases la <;> obtain ⟨mc, h⟩ := h;
      cases mc with
      | zero => simp [der] at h
      | succ mc => exact ⟨mc, h⟩
  | .middle mcount main la  => cases mcount <;> simp [derLB, lookbehind, toList]
  | .right mcount lacount la =>
    cases mcount with
    | zero =>
      cases lacount with
      | zero =>
        cases la <;> simp [derLB, lookbehind]
        constructor
        . intro ⟨mc, h⟩; refine ⟨mc.succ, h⟩
        . intro ⟨mc, h⟩; cases mc with
          | zero => simp [der] at h
          | succ mc => refine ⟨mc, h⟩
      | succ lacount => simp [derLB, lookbehind]
    | succ mcount => cases la <;> simp [derLB, lookbehind]

theorem derLB_la (a : α) (l : Lang α) : derLB a (▷ l) ≐ ∅ := by
  intro w
  match w with
  | .left _ _ _  => simp [derLB, lookahead, empty]
  | .middle mcount _ _  => cases mcount <;> simp [derLB, lookahead, empty]
  | .right mcount lacount la => cases mcount <;> cases lacount <;> cases la <;> simp [derLB, lookahead, empty]

theorem derLB_matchStep (a : α) (l : Lang α) : derLB a (matchStep l) ≐ ∅ := by
  intro w
  match w with
  | .left _ _ _   => simp [derLB, matchStep, empty]
  | .middle mcount _ _  => cases mcount <;> simp [derLB, matchStep, empty]
  | .right mcount lacount _ => cases mcount <;> cases lacount <;> simp [derLB, matchStep, empty]

theorem derLB_LAStep (a : α) (l : Lang α) : derLB a (LAStep l) ≐ ∅  := by
  intro w
  match w with
  | .left _ _ _   => simp [derLB, LAStep, empty]
  | .middle mcount _ _  => cases mcount <;> simp [derLB, LAStep, empty]
  | .right mcount lacount _ => cases lacount <;> cases mcount <;> simp [derLB, LAStep, empty]

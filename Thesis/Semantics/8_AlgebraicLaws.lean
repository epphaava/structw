import Thesis.Semantics.«1_StructuredWords»
import Thesis.Semantics.«2_Operators»

namespace AlgebraicLaws

open StructuredWords
open Operators

-- Proposition 3.5.1 (Basic algebraic laws).

-- Equation (3.1)
theorem union_assoc (K L M : Lang α) : K ∪ (L ∪ M) ≐ (K ∪ L) ∪ M := by intro w; simp [union, or_assoc]

-- Equation (3.2)
theorem union_comm (K L : Lang α) : K ∪ L ≐ L ∪ K := by intro w; simp [union, or_comm]

-- Equation (3.3)
theorem union_idempotent (L : Lang α) : L ∪ L ≐ L := by intro w; simp [union]

-- Equation (3.4)
theorem union_identity (L : Lang α) : L ∪ ∅ ≐ L := by intro w; simp [empty, union]

-- Equation (3.5)
theorem intersection_assoc (K L M : Lang α) : K ∩ (L ∩ M) ≐ (K ∩ L) ∩ M := by
  intro w; simp [intersection, and_assoc]

-- Equation (3.6)
theorem intersection_comm (K L : Lang α) : K ∩ L ≐ L ∩ K := by
  intro w; simp [intersection, and_comm]

-- Equation (3.7)
theorem intersection_idempotent (L : Lang α) : L ∩ L ≐ L := by intro w; simp [intersection]

-- Equation (3.8)
theorem intersection_top (L : Lang α) : T ∩ L ≐ L := by intro w; simp [top, intersection]

-- Equation (3.9)
theorem complement_empty (L : Lang α) : (L - ∅) ≐ L := by intro w; simp [empty, complement]

-- Equation (3.10)
theorem complement_self (L : Lang α) : (L - L) ≐ ∅ := by intro w; simp [complement, empty]

-- Equation (3.11)
theorem complement_top (L : Lang α) : (L - T) ≐ ∅ := by intro w; simp [top, complement, empty]

-- Equation (3.12)
theorem concat_distrib_union_left (p q r : Lang α) : p • (q ∪ r) ≐ (p • q) ∪ (p • r) := by
  intro w
  match w with
  | .left lbc lb main la =>
    constructor
    . intro ⟨x, y, hx, hy, hc⟩
      cases hy with
      | inl hy => left; exact ⟨x, y, hx, hy, hc⟩
      | inr hy => right; exact ⟨x, y, hx, hy, hc⟩
    . intro h
      cases h with
      | inl h => obtain ⟨x, y, hx, hy, hc⟩ := h; exact ⟨x, y, hx, Or.inl hy, hc⟩
      | inr h => obtain ⟨x, y, hx, hy, hc⟩ := h; exact ⟨x, y, hx, Or.inr hy, hc⟩
  | .middle lbc mcount main la =>
    constructor
    . intro ⟨x, y, hx, hy, hwc⟩
      cases hwc with
      | inl h =>
        obtain ⟨pref, suff, hmain, xsub, ysub⟩ := h
        cases hy with
        | inl hy => left; exact ⟨x, y, hx, hy, Or.inl ⟨pref, suff, hmain, xsub, ysub⟩⟩
        | inr hy => right; exact ⟨x, y, hx, hy, Or.inl ⟨pref, suff, hmain, xsub, ysub⟩⟩
      | inr h =>
        obtain ⟨mc₁, mc₂, hmcount, xsub, ysub⟩ := h
        cases hy with
        | inl hy => left; refine ⟨x, y, hx, hy, Or.inr ⟨mc₁, mc₂, hmcount, xsub, ysub⟩⟩
        | inr hy => right; exact ⟨x, y, hx, hy, Or.inr ⟨mc₁, mc₂, hmcount, xsub, ysub⟩⟩
    . intro h
      cases h with
      | inl h => obtain ⟨x, y, hx, hy, hc⟩ := h; exact ⟨x, y, hx, Or.inl hy, hc⟩
      | inr h => obtain ⟨x, y, hx, hy, hc⟩ := h; exact ⟨x, y, hx, Or.inr hy, hc⟩
  | .right lbc mcount lacount la =>
    constructor
    . intro ⟨w₁, w₂, hp, hqr, n₁, n₂, hn, hw₁, hw₂⟩
      cases hqr with
      | inl hq => left; exact ⟨w₁, w₂, hp, hq, n₁, n₂, hn, hw₁, hw₂⟩
      | inr hr => right; exact ⟨w₁, w₂, hp, hr, n₁, n₂, hn, hw₁, hw₂⟩
    . intro h
      cases h with
      | inl h => obtain ⟨w₁, w₂, hp, hq, n₁, n₂, hn, hw₁, hw₂⟩ := h; refine ⟨w₁, w₂, hp, Or.inl hq, n₁, n₂, hn, hw₁, hw₂⟩
      | inr h => obtain ⟨w₁, w₂, hp, hr, n₁, n₂, hn, hw₁, hw₂⟩ := h; refine ⟨w₁, w₂, hp, Or.inr hr, n₁, n₂, hn, hw₁, hw₂⟩


-- Equation (3.13)
theorem concat_distrib_union_right (p q r : Lang α) : (p ∪ q) • r ≐ (p • r) ∪ (q • r) := by
  intro w
  match w with
  | .left lbc lb main la =>
    constructor
    . intro ⟨w₁, w₂, hpq, hr, hc⟩
      cases hpq with
      | inl hp => left; refine ⟨w₁, w₂, hp, hr, hc⟩
      | inr hq => right; exact ⟨w₁, w₂, hq, hr, hc⟩
    . intro h
      cases h with
      | inl h => obtain ⟨w₁, w₂, hp, hr, hc⟩ := h; exact ⟨w₁, w₂, Or.inl hp, hr, hc⟩
      | inr h => obtain ⟨w₁, w₂, hq, hr, hc⟩ := h; exact ⟨w₁, w₂, Or.inr hq, hr, hc⟩
  | .middle lbc mcount main la =>
    constructor
    . intro ⟨w₁, w₂, hpq, hr, h⟩
      cases hpq with
      | inl hp =>
        cases h with
        | inl h => obtain ⟨pref, suff, hmain, hw₁, hw₂⟩ := h; left; exact ⟨w₁, w₂, hp, hr, Or.inl ⟨pref, suff, hmain, hw₁, hw₂⟩⟩
        | inr h => obtain ⟨mc₁, mc₂, hmcount, hw₁, hw₂⟩ := h; left; exact ⟨w₁, w₂, hp, hr, Or.inr ⟨mc₁, mc₂, hmcount, hw₁, hw₂⟩⟩
      | inr hq =>
        cases h with
        | inl h => right; obtain ⟨pref, suff, hmain, hw₁, hw₂⟩ := h; exact ⟨w₁, w₂, hq, hr, Or.inl ⟨pref, suff, hmain, hw₁, hw₂⟩⟩
        | inr h => right; obtain ⟨mc₁, mc₂, hmcount, hw₁, hw₂⟩ := h; exact ⟨w₁, w₂, hq, hr, Or.inr ⟨mc₁, mc₂, hmcount, hw₁, hw₂⟩⟩
    . intro h
      cases h with
      | inl h =>
        obtain ⟨x, y, hp, hr, h⟩ := h; cases h with
        | inl h => obtain ⟨pref, suff, hmain, hx, hy⟩ := h; exact ⟨x, y, Or.inl hp, hr, Or.inl ⟨pref, suff, hmain, hx, hy⟩⟩
        | inr h => obtain ⟨pref, suff, hmain, hx, hy⟩ := h; exact ⟨x, y, Or.inl hp, hr, Or.inr ⟨pref, suff, hmain, hx, hy⟩⟩
      | inr h =>
        obtain ⟨x, y, hq, hr, h⟩ := h; cases h with
        | inl h => obtain ⟨pref, suff, hmain, hx, hy⟩ := h; exact ⟨x, y, Or.inr hq, hr, Or.inl ⟨pref, suff, hmain, hx, hy⟩⟩
        | inr h => obtain ⟨pref, suff, hmain, hx, hy⟩ := h; exact ⟨x, y, Or.inr hq, hr, Or.inr ⟨pref, suff, hmain, hx, hy⟩⟩
  | .right lbc mcount lacount la =>
    constructor
    . intro ⟨w₁, w₂, hpq, hr, n₁, n₂, hn, hw₁, hw₂⟩
      cases hpq with
      | inl hp => left; exact ⟨w₁, w₂, hp, hr, n₁, n₂, hn, hw₁, hw₂⟩
      | inr hq => right; exact ⟨w₁, w₂, hq, hr, n₁, n₂, hn, hw₁, hw₂⟩
    . intro h
      cases h with
      | inl h => obtain ⟨w₁, w₂, hp, hr, n₁, n₂, hn, hw₁, hw₂⟩ := h; refine ⟨w₁, w₂, Or.inl hp, hr, n₁, n₂, hn, hw₁, hw₂⟩
      | inr h => obtain ⟨w₁, w₂, hq, hr, n₁, n₂, hn, hw₁, hw₂⟩ := h; refine ⟨w₁, w₂, Or.inr hq, hr, n₁, n₂, hn, hw₁, hw₂⟩


-- Equation (3.14)
theorem empty_concat_left (L : Lang α) : ∅ • L ≐ ∅ := by
  intro w
  match w with
  | .left _ _ _ _ => simp [concat, empty]
  | .middle _ _ _ _ => simp [concat, empty]
  | .right _ _ _ _ => simp [concat, empty]

theorem empty_concat_right (L : Lang α) : L • ∅ ≐ ∅ := by
  intro w
  match w with
  | .left _ _ _ _ => simp [concat, empty]
  | .middle _ _ _ _ => simp [concat, empty]
  | .right _ _ _ _ => simp [concat, empty]

-- Equation (3.15)
theorem star_unfold (base l : Lang α) : (star l base) ≐ base ∪ (l • (star l base)) := by
  intro w; constructor
  . intro h
    cases h with
    | inUnit _ hb => exact .inl hb
    | inConcat w₁ w₂ _ hl hs hwc => exact .inr ⟨w₁, w₂, hl, hs, hwc⟩
  . intro h
    rcases h with hb | ⟨w₁, w₂, hl, hs, hwc⟩
    . exact .inUnit _ hb
    . exact .inConcat w₁ w₂ _ hl hs hwc


-- Proposition 3.5.3 (Left identity).
theorem concat_left_identity (L : Lang α) : I • L ≐ L  := by
  intro w
  match w with
  | .left lbc (x, xs) main la =>
    constructor
    . rintro ⟨_, _, hunit, hl, pref, suff, hmain, rfl, rfl⟩; simp [unit] at hunit; subst pref main; simp at hl; exact hl
    . intro h; exact ⟨.left lbc (x, xs) [] (main ++ la), .left lbc (x, xs) main la, by simp [unit], h, [], main, rfl, rfl, by simp⟩
  | .middle lbc mcount main la =>
    constructor
    . intro ⟨w₁, w₂, hunit, hl, h⟩; cases h with
      | inl h => obtain ⟨_ ,_, _, rfl, _⟩ := h; simp [unit] at hunit
      | inr h => obtain ⟨mc₁, mc₂, hmcount, rfl, rfl⟩ := h; simp [unit] at hunit; subst mc₁ mcount; simp at ⊢ hl; exact hl
    . intro h; exact ⟨.right lbc 0 mcount ((toList main) ++ la), .middle lbc mcount main la, by simp [unit], h, Or.inr ⟨0, mcount, by simp, rfl, rfl⟩⟩
  | .right lbc mcount lacount la =>
    constructor
    . intro ⟨w₁, w₂, hunit, hl, mc₁, mc₂, _, _, _⟩;
      cases mc₁ with
      | zero => subst w₂ mcount; simp at ⊢ hl; exact hl
      | succ mc₁ => subst w₁; simp [unit] at hunit
    . intro h; exact ⟨.right lbc 0 (mcount + lacount) la, .right lbc mcount lacount la, by simp [unit], h, 0, mcount, by simp, rfl, rfl⟩

-- Proposition 3.5.4 (Right identity).
theorem concat_right_identity (L : Lang α) : L • I ≐ L := by
  intro w
  match w with
  | .left lbc (x, xs) main la =>
    constructor
    . intro ⟨w₁, w₂, hl, hunit, pref, suff, hmain, _, _⟩; subst w₁ w₂; simp [unit] at hunit; subst suff main; simp at ⊢ hl; exact hl
    . intro h; exact ⟨ .left lbc (x, xs) main la, .left lbc (x, xs ++ main) [] la, h, by simp [unit], main, [], by simp, rfl, rfl⟩
  | .middle lbc mcount main la =>
    constructor
    . intro ⟨w₁, w₂, hl, hunit, h⟩; cases h with
      | inl h => obtain ⟨pref, suff, hmain, _, _⟩ := h; subst w₁ w₂; simp [unit] at hunit; subst suff; simp at hmain; subst pref; exact hl
      | inr h => obtain ⟨mc₁, mc₂, hmcount, _, _⟩ := h; subst w₁ w₂; simp [unit] at hunit
    . intro h; exact ⟨.middle lbc mcount main la, .left (lbc + mcount) (main.fst, main.snd) [] la, h, by simp [unit], Or.inl ⟨main.snd, [], by simp, rfl, rfl⟩⟩
  | .right lbc mcount lacount la =>
    constructor
    . intro ⟨w₁, w₂, hl, hunit, mc₁, mc₂, hmcount, _, _⟩;
      cases mc₁ with
      | zero =>
        cases mc₂ with
        | zero => subst w₁ mcount; simp at hl; exact hl
        | succ mc₂ => subst w₂; simp [unit] at hunit
      | succ mc₁ => subst w₁ w₂ ; simp [unit] at hunit; subst mc₂ mcount; simp at hl; exact hl
    . intro h; exact ⟨.right lbc mcount lacount la, .right (lbc + mcount) 0 lacount la, h, by simp [unit], mcount, 0, rfl, by simp, rfl⟩

-- Proposition 3.5.6 (Associativity).
theorem concat_assoc (k l m : Lang α) : k • (l • m) ≐ (k • l) • m := by
  intro w
  match w with
  | .left lbc lb main la =>
    constructor
    . rintro ⟨w₁, w₂₃, hk, ⟨w₂, w₃, hl, hm, hwc₂₃⟩ , pref₁, suff₁, hmain, hw₁, rfl⟩
      obtain ⟨pref₂, suff₂, hsuff₁, hw₂, hw₃⟩ := hwc₂₃
      have hwc₁₂ : wc w₁ w₂ (.left lbc lb (pref₁ ++ pref₂) (suff₂ ++ la)) := by exact ⟨pref₁, pref₂, rfl, by simp [hsuff₁] at hw₁; exact hw₁, hw₂⟩
      have concat₁ : (k • l) (.left lbc lb (pref₁ ++ pref₂) (suff₂ ++ la)) := by exact ⟨w₁, w₂, hk, hl, hwc₁₂⟩
      exact ⟨.left lbc lb (pref₁ ++ pref₂) (suff₂ ++ la), w₃, concat₁, hm, (pref₁ ++ pref₂), suff₂, by simp [hsuff₁, hmain], rfl, by simp at hw₃; exact hw₃⟩
    . rintro ⟨w₁₂, w₃, ⟨w₁, w₂, hk, hl, hwc₁₂⟩, hm, pref₁, suff₁, rfl, rfl, hw₃⟩
      obtain ⟨pref₂, suff₂, rfl, hw₁, hw₂⟩ := hwc₁₂;
      have hwc₂₃ : wc w₂ w₃ (.left lbc (lb.fst, lb.snd ++ pref₂) (suff₂ ++ suff₁) la) := by exact ⟨suff₂, suff₁, rfl, hw₂, by simp; exact hw₃⟩
      have concat₂ : (l • m) (.left lbc (lb.fst, lb.snd ++ pref₂) (suff₂ ++ suff₁) la) := by exact ⟨w₂, w₃, hl, hm, hwc₂₃⟩
      exact ⟨w₁, .left lbc (lb.fst, lb.snd ++ pref₂) (suff₂ ++ suff₁) la, hk, concat₂, pref₂, (suff₂ ++ suff₁), by simp, by simp; exact hw₁, rfl⟩
  | .middle lbc mcount (y, ys) la =>
    constructor
    . intro ⟨w₁, w₂₃, hk, ⟨w₂, w₃, hl, hm, hwc₂₃⟩, h⟩
      cases h with
      | inl h =>
        obtain ⟨pref₁, suff₁, hys, hw₁, rfl⟩ := h
        obtain ⟨pref₂, suff₂, rfl, hw₂, hw₃⟩ := hwc₂₃; simp at hys; subst hys
        have hwc₁₂ : wc w₁ w₂ (.middle lbc mcount (y, pref₁ ++ pref₂) (suff₂ ++ la)) := by exact Or.inl ⟨pref₁, pref₂, rfl, ⟨by simp at hw₁ ⊢; exact hw₁, hw₂⟩⟩
        have concat₁ : (k • l) (.middle lbc mcount (y, pref₁ ++ pref₂) (suff₂ ++ la)) := by exact ⟨w₁, w₂, hk, hl, hwc₁₂⟩
        exact ⟨(.middle lbc mcount (y, pref₁ ++ pref₂) (suff₂ ++ la)), w₃, concat₁, hm, Or.inl ⟨(pref₁ ++ pref₂), suff₂, by simp, rfl, by simp at hw₃; exact hw₃⟩⟩
      | inr h =>
        obtain ⟨mc₁, mc₂, rfl, hw₁, rfl⟩ := h;
        cases hwc₂₃ with
        | inl h =>
          obtain ⟨pref, suff, hys, hw₂, hw₃⟩ := h; simp at hys; subst ys
          have hwc₁₂ : wc w₁ w₂ (.middle lbc (mc₁ + mc₂) (y, pref) (suff ++ la)) := by exact Or.inr ⟨mc₁, mc₂, rfl, by simp [toList] at hw₁; exact hw₁, hw₂⟩
          have concat₁ : (k • l) (.middle lbc (mc₁ + mc₂) (y, pref) (suff ++ la)) := by exact ⟨w₁, w₂, hk, hl, hwc₁₂⟩
          exact ⟨.middle lbc (mc₁ + mc₂) (y, pref) (suff ++ la), w₃, concat₁, hm, Or.inl ⟨pref, suff, rfl, rfl, by rw [←Nat.add_assoc]; exact hw₃⟩⟩
        | inr h =>
          obtain ⟨mc₁', mc₂', rfl, hw₂, hw₃⟩ := h;
          have hwc₁₂ : wc w₁ w₂ (.right lbc (mc₁ + mc₁') mc₂' (y :: ys ++ la)) := by exact ⟨mc₁, mc₁', rfl, hw₁, hw₂⟩
          have concat₁ : (k • l) (.right lbc (mc₁ + mc₁') mc₂' (y :: ys ++ la)) := by exact ⟨w₁, w₂, hk, hl, hwc₁₂⟩
          exact ⟨(.right lbc (mc₁ + mc₁') mc₂' (y :: ys ++ la)), w₃, concat₁, hm, Or.inr ⟨(mc₁ + mc₁'), mc₂', by simp [Nat.add_assoc], rfl, by rw [←Nat.add_assoc]; exact hw₃⟩⟩
    . intro ⟨w₁₂, w₃, ⟨w₁, w₂, hk, hl, hwc₁₂⟩, hm, h⟩
      cases h with
      | inl h =>
        obtain ⟨pref₁, suff₁, hys, rfl, hw₃⟩ := h;
        cases hwc₁₂ with
        | inl h =>
          obtain ⟨pref₂, suff₂, hpref₁, hw₁, hw₂⟩ := h; simp at hpref₁ hys; subst pref₁ ys
          have hwc₂₃ : wc w₂ w₃ (.left (lbc + mcount) (y, pref₂) (suff₂ ++ suff₁) la) := by exact ⟨suff₂, suff₁, rfl, hw₂, hw₃⟩
          have concat₂ : (l • m) (.left (lbc + mcount) (y, pref₂) (suff₂ ++ suff₁) la) := by exact ⟨w₂, w₃, hl, hm, hwc₂₃⟩
          exact ⟨w₁, (.left (lbc + mcount) (y, pref₂) (suff₂ ++ suff₁) la), hk, concat₂, Or.inl ⟨pref₂, (suff₂ ++ suff₁), by simp, by simp; exact hw₁, rfl⟩⟩
        | inr h =>
          obtain ⟨mc₁, mc₂, rfl, hw₁, hw₂⟩ := h; simp at hys; subst ys
          have hwc₂₃ : wc w₂ w₃ (.middle (lbc + mc₁) mc₂ (y, pref₁ ++ suff₁) la) := by exact Or.inl ⟨pref₁, suff₁, rfl, hw₂, by simp [Nat.add_assoc]; exact hw₃⟩
          have concat₂ : (l • m) (.middle (lbc + mc₁) mc₂ (y, pref₁ ++ suff₁) la) := by exact ⟨w₂, w₃, hl, hm, hwc₂₃⟩
          exact ⟨w₁, (.middle (lbc + mc₁) mc₂ (y, pref₁ ++ suff₁) la), hk, concat₂, Or.inr ⟨mc₁, mc₂, rfl, by simp [toList] at hw₁ ⊢; exact hw₁, rfl⟩⟩
      | inr h =>
        obtain ⟨mc₁, mc₂, rfl, rfl, hw₃⟩ := h; obtain ⟨mc₁', mc₂', rfl, hw₁, hw₂⟩ := hwc₁₂;
        have hwc₂₃ : wc w₂ w₃ (.middle (lbc + mc₁') (mc₂' + mc₂) (y, ys) la) := by exact Or.inr ⟨mc₂', mc₂, rfl, hw₂, by simp [Nat.add_assoc]; exact hw₃⟩
        have concat₂ : (l • m) (.middle (lbc + mc₁') (mc₂' + mc₂) (y, ys) la) := by exact ⟨w₂, w₃, hl, hm, hwc₂₃⟩
        exact ⟨w₁, (.middle (lbc + mc₁') (mc₂' + mc₂) (y, ys) la), hk, concat₂, Or.inr ⟨mc₁', (mc₂' + mc₂), by simp [Nat.add_assoc], hw₁, rfl⟩⟩
  | .right lbc mcount lacount la =>
    constructor
    . rintro ⟨w₁, w₂₃, hk, ⟨w₂, w₃, hl, hm, hwc₂₃⟩, mc₁, mc₂, rfl, hw₁, rfl⟩; obtain ⟨mc₁', mc₂', rfl, hw₂, hw₃⟩ := hwc₂₃;
      have hwc₁₂ : wc w₁ w₂ (.right lbc (mc₁ + mc₁') (mc₂' + lacount) la) := by exact ⟨mc₁, mc₁', rfl, by simp [Nat.add_assoc] at hw₁; exact hw₁, hw₂⟩
      have concat₁ : (k • l) (.right lbc (mc₁ + mc₁') (mc₂' + lacount) la) := by exact ⟨w₁, w₂, hk, hl, hwc₁₂⟩
      exact ⟨(.right lbc (mc₁ + mc₁') (mc₂' + lacount) la), w₃, concat₁, hm, (mc₁ + mc₁'), mc₂', by simp [Nat.add_assoc], rfl, by rw [←Nat.add_assoc]; exact hw₃⟩
    . rintro ⟨w₁₂, w₃, ⟨w₁, w₂, hk, hl, hwc₁₂⟩, hm, mc₁, mc₂, rfl, rfl, hw₃⟩; obtain ⟨mc₁', mc₂', rfl, hw₁, hw₂⟩ := hwc₁₂;
      have hwc₂₃ : wc w₂ w₃ (.right (lbc + mc₁') (mc₂' + mc₂) lacount la) := by exact ⟨mc₂', mc₂, rfl, hw₂, by rw [Nat.add_assoc]; exact hw₃⟩
      have concat₂ : (l • m) (.right (lbc + mc₁') (mc₂' + mc₂) lacount la) := by exact ⟨w₂, w₃, hl, hm, hwc₂₃⟩
      exact ⟨w₁, (.right (lbc + mc₁') (mc₂' + mc₂) lacount la), hk, concat₂, mc₁', (mc₂' + mc₂), by simp [Nat.add_assoc], by simp [Nat.add_assoc]; exact hw₁, rfl⟩

end AlgebraicLaws

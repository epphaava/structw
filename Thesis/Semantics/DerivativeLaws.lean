import Thesis.Semantics.StructuredWords
import Thesis.Semantics.Operators
import Thesis.Semantics.Derivatives

namespace DerLaws

open StructuredWords
open Operators

-- Proposition 3.4.1 (Derivative laws for structured languages).

-- ======== DER ==========
theorem der_empty (a : α) : der a ∅ ≐ ∅ := by
  intro w
  match w with
  | .left lb main la => simp [der, empty]
  | .middle mcount main la => cases mcount <;> simp [der, empty]
  | .right mcount lacount la => cases mcount <;> cases lacount <;> simp [der, empty]

theorem der_unit (a : α) : der a I ≐ ∅ := by
  intro w
  match w with
  | .left lb main la => simp [der, empty]
  | .middle mcount main la => cases mcount <;> simp [der, unit, empty]
  | .right mcount lacount la => cases mcount <;> cases lacount <;> simp [der, unit, empty]

theorem der_top (a : α): (der a T) ≐ (▹ₘ T // ▹ₗ T) := by
  intro w
  match w with
  | .left lb main la => simp [complement, der, matchStep]
  | .middle mcount main la => cases mcount <;> simp [complement, der, matchStep, LAStep, top]
  | .right mcount lacount la => cases mcount <;> cases lacount <;> simp [complement, der, matchStep, LAStep, top]


theorem der_symb_match (a b: α) (h : a = b) : der b (#a) ≐ (▹ₘ I // ▹ₗ T) := by
  intro w
  match w with
  | .left lb main la => simp [complement, der, matchStep, LAStep]
  | .middle mcount main la => cases mcount <;> simp [complement, der, matchStep, LAStep, symb, unit, toList]
  | .right mcount lacount la =>
    cases mcount with
    | zero => cases lacount <;> simp [complement, der, matchStep, LAStep]
    | succ mcount => cases mcount <;> cases lacount <;> simp [complement, der, matchStep, LAStep, symb, unit, h , top]

theorem der_symb_no_match (a b: α) (h : ¬ (a = b)) : der b (#a) ≐ ∅ := by
  intro w
  match w with
  | .left lb main la => simp [der, empty]
  | .middle mcount main la => cases mcount <;> simp [der, symb, empty, toList]
  | .right mcount lacount la =>
    cases mcount with
    | zero => cases lacount <;> simp [der, empty]
    | succ mcount => cases mcount <;> cases lacount <;> simp [der, symb, empty, h]

theorem der_union (a : α) (k l : Lang α): der a (k ∪ l) ≐ (der a k) ∪ (der a l) := by
  intro w
  match w with
  | .left lb main la => simp [der, union]
  | .middle mcount main la => cases mcount <;> simp [der, union]
  | .right mcount lacount la => cases mcount <;> cases lacount <;> simp [der, union]

theorem der_intersection (a : α) (k l : Lang α): der a (k ∩ l) ≐ (der a k) ∩ (der a l) := by
  intro w
  match w with
  | .left lb main la => simp [der, intersection]
  | .middle mcount main la => cases mcount <;> simp [der, intersection]
  | .right mcount lacount la => cases mcount <;> cases lacount <;> simp [der, intersection]

theorem der_complement (a : α) (k l : Lang α): der a (k // l) ≐ ((der a k) // (der a l)) := by
  intro w
  match w with
  | .left lb main la => simp [der, complement]
  | .middle mcount main la => cases mcount <;> simp [der, complement]
  | .right mcount lacount la => cases mcount <;> cases lacount <;> simp [der, complement]

theorem der_concat (a : α) (k l : Lang α) :
  der a (concat k l) ≐  ((der a k) • (derLB a l)) ∪ ((derLA a k) • (der a l)) := by
  intro w
  match w with
  | .left lb main la =>
    constructor
    . intro h; simp [der] at h
    . intro h
      cases h with
      | inl h => obtain ⟨w₁, _, hk, _, ⟨_, _, _, _, _⟩⟩ := h; subst w₁; simp [der] at hk
      | inr h => obtain ⟨w₁, _, hk, _, ⟨_, _, _, _, _⟩⟩ := h; subst w₁; simp [derLA] at hk
  | .middle mcount main la =>
    constructor
    . intro h
      cases mcount with
      | zero => simp [der] at h
      | succ mcount =>
        obtain ⟨w₁, w₂, hk, hl, h⟩ := h
        cases h with
        | inl h =>
          obtain ⟨pref, suff, hmain, _, _⟩ := h; subst w₁ w₂; left
          cases pref with
          | nil => simp at hmain; subst suff; exact ⟨.right mcount.succ 0 (toList main ++ la), .middle 0 main la, hk, hl, Or.inr ⟨mcount.succ, 0, rfl, rfl, rfl⟩⟩
          | cons u us => simp [toList] at hmain; exact ⟨.middle mcount.succ (u, us) (suff ++ la), .left (u, us) suff la, hk, hl, Or.inl ⟨us, suff, hmain.2, by simp [hmain.1]⟩⟩
        | inr h =>
          obtain ⟨mc₁, mc₂, hmcount, _, _⟩ := h; subst w₁ w₂ mcount; right; exact ⟨.right mc₁ mc₂.succ (toList main ++ la), .middle mc₂.succ main la, hk, hl, Or.inr ⟨mc₁, mc₂.succ, rfl, rfl, rfl⟩⟩
    . intro h
      cases mcount with
      | zero =>
        cases h with
        | inl h =>
          obtain ⟨w₁, _, hk, _, h⟩ := h;
          cases h with
          | inl h => obtain ⟨_, _, _, _, _⟩ := h; subst w₁; simp [der] at hk
          | inr h => obtain ⟨mc₁, _, hmcount, _, _⟩ := h; subst w₁; cases mc₁ <;> simp [der] at hk; simp at hmcount
        | inr h =>
          obtain ⟨w₁, w₂, hk, hl, h⟩ := h
          cases h with
          | inl h => obtain ⟨_, _, _, _, _⟩ := h; subst w₁; simp [derLA] at hk
          | inr h => obtain ⟨mc₁, mc₂, hmcount, _, _⟩ := h; subst w₁ w₂; cases mc₁ <;> cases mc₂ <;> simp [der, derLA] at hk hl <;> simp at hmcount
      | succ mcount =>
        cases h with
        | inl h =>
          obtain ⟨w₁, w₂, hk, hl, h⟩ := h
          cases h with
          | inl h => obtain ⟨pref, suff, hmain, _, _⟩ := h; subst w₁ w₂; exact ⟨.middle mcount (a, main.1 :: pref) (suff ++ la), .left (a, main.1 :: pref) suff la, hk, hl, Or.inl ⟨main.1 :: pref, suff, by simp [toList]; exact hmain, rfl, rfl⟩⟩
          | inr h =>
            obtain ⟨mc₁, mc₂, hmcount, _, _⟩ := h; subst w₁ w₂;
            cases mc₁ with
            | zero => simp [der] at hk
            | succ mc₁ =>
              cases mc₂ <;> simp [derLB, der] at hl hk; simp at hmcount; subst mcount
              exact ⟨.middle mc₁ (a, []) (toList main ++ la), .left (a, []) (toList main) la, hk, hl, Or.inl ⟨[], (toList main), rfl, by simp [toList], rfl⟩⟩
        | inr h =>
          obtain ⟨w₁, w₂, hk, hl, h⟩ := h;
          cases h with
          | inl h => obtain ⟨_, _, h⟩ := h; simp [h, derLA] at hk
          | inr h =>
            obtain ⟨mc₁, mc₂, hmcount, _, _⟩ := h; subst w₁ w₂
            cases mc₂ with
            | zero => simp [der] at hl
            | succ mc₂ => exact ⟨.right mc₁ mc₂ (a :: (toList main) ++ la), .middle mc₂ (a, toList main) la, hk, hl, Or.inr ⟨mc₁, mc₂, by rw [←Nat.add_assoc, Nat.add_one_inj] at hmcount; exact hmcount, rfl, rfl⟩⟩
  | .right mcount lacount la =>
    cases lacount with
    | zero =>
      constructor
      . intro h
        cases mcount with
        | zero => simp [der] at h
        | succ mcount =>
          obtain ⟨w₁, w₂, hk, hl, h⟩ := h;
          cases h with
          | inl h => obtain ⟨pref, suff, hmain, _, _⟩ := h; simp at hmain; obtain ⟨_, _⟩ := hmain; subst w₁ w₂ pref suff; left; exact ⟨.right mcount.succ 0 la, .right 0 0 la, hk, hl, mcount.succ, 0, rfl, rfl, rfl⟩
          | inr h => obtain ⟨mc₁, mc₂, hmcount, _, _⟩ := h; subst w₁ w₂ mcount; right; exact ⟨.right mc₁ mc₂.succ la, .right mc₂.succ 0 la, hk, hl, mc₁, mc₂.succ, rfl, rfl, rfl⟩
      . intro h
        cases mcount with
        | zero =>
          cases h with
          | inl h => obtain ⟨w₁, _, hk, _, mc₁, mc₂, hmcount, _, _⟩ := h; subst w₁; cases mc₁ <;> cases mc₂ <;> simp [der] at hk; simp at hmcount
          | inr h => obtain ⟨_, w₂, _, hl, _, mc₂, hmcount, _, _⟩ := h; subst w₂; cases mc₂ <;> simp [der] at hl; simp at hmcount
        | succ mcount =>
          cases h with
          | inl h =>
            obtain ⟨w₁, w₂, hk, hl, mc₁, mc₂, hmcount, _, _⟩ := h; subst w₁ w₂;
            cases mc₂ with
            | zero => simp at hmcount; subst mc₁; exact ⟨.middle mcount (a, []) la, .left (a, []) [] la, hk, hl, Or.inl ⟨[], [], rfl, rfl, rfl⟩⟩
            | succ mc₂ => simp [der] at hk
          | inr h =>
            obtain ⟨w₁, w₂, hk, hl, mc₁, mc₂, hmcount, _, _⟩ := h; subst w₁ w₂;
            cases mc₂ with
            | zero => simp [derLA] at hk
            | succ mc₂ => rw [←Nat.add_assoc, Nat.add_one_inj] at hmcount; exact ⟨.right mc₁ mc₂ (a :: la), .middle mc₂ (a, []) la, hk, hl, Or.inr ⟨mc₁, mc₂, hmcount.symm, rfl, rfl⟩⟩
    | succ m =>
      constructor
      . simp [der]
      . intro h
        cases h with
        | inl h => obtain ⟨_, w₂, _, hl, _, _, _, _, _⟩ := h; subst w₂; simp [derLB] at hl
        | inr h => obtain ⟨_, w₂, _, hl, _, _, _, _, _⟩ := h; subst w₂; simp [der] at hl

theorem der_star (a : α) (l : Lang α) : der a (l*) ≐ ((der a l) • (derLB a l*)) ∪ ((derLA a l) • (der a l*)) := by
  sorry

theorem der_lb (a : α) (l : Lang α) : der a (◁ l) ≐ ∅  := by
  intro w
  match w with
  | .left lb main la => simp [der, empty]
  | .middle mcount main la => cases mcount <;> simp [der, lookbehind, empty]
  | .right mcount lacount la => cases mcount <;> cases lacount <;> simp [der, lookbehind, empty]

theorem der_la (a : α) (l : Lang α) : der a (▷ l) ≐ ∅  := by
  intro w
  match w with
  | .left lb main la => simp [der, empty]
  | .middle mcount main la => cases mcount <;> simp [der, empty, lookahead]
  | .right mcount lacount la => cases mcount <;> cases lacount <;> simp [der, lookahead, empty]

theorem der_matchStep (a : α) (l : Lang α) : der a (matchStep l) ≐ matchStep (der a l) := by
  intro w
  match w with
  | .left lb main la => simp [der, matchStep]
  | .middle mcount main la =>
    cases mcount with
    | zero => simp [der, matchStep]
    | succ mcount => cases mcount <;> simp [der, matchStep]
  | .right mcount lacount la =>
    cases mcount with
    | zero => simp [der, matchStep]
    | succ mcount => cases mcount <;> cases lacount <;> simp [der, matchStep]

theorem der_LAStep (a : α) (l : Lang α) : der a (LAStep l) ≐ ∅ := by
  intro w
  match w with
  | .left lb main la => simp [der, empty]
  | .middle mcount main la => cases mcount <;> simp [der, LAStep, empty]
  | .right mcount lacount la => cases mcount <;> cases lacount <;> simp [der, LAStep, empty]

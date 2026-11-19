import Thesis.Semantics.«1_StructuredWords»
import Thesis.Semantics.«2_Operators»
import Thesis.Semantics.«3_Derivatives»
import Thesis.Semantics.Helpers.«5_LookbehindDerivativeLaws»

namespace derLBLaws

open StructuredWords
open Operators
open derLBLawsHelpers

-- Proposition 3.4.1 (Derivative laws for structured languages).

theorem derLB_empty (a : α) : derLB a ∅ ≐ ∅ := by
  intro w
  match w with
  | .left _ _ _ => simp [derLB, empty]
  | .middle mcount _ _ => cases mcount <;> simp [derLB, empty]
  | .right mcount lacount _ => cases mcount <;> cases lacount <;> simp [derLB, empty]

theorem derLB_unit (a : α) : derLB a I ≐ (I - ↑₃ I) := by
  intro w
  match w with
  | .left _ _ _ => simp [complement, derLB, laStep, unit]
  | .middle mcount _ _ => cases mcount <;> simp [complement, derLB, laStep, unit, toList]
  | .right mcount lacount _ => cases mcount <;> cases lacount <;> simp [complement, derLB, laStep, unit]

theorem derLB_top (a : α) : derLB a T ≐ (T - (↑₂ T ∪ ↑₃ T )) := by
  intro w
  match w with
  | .left _ _ _ => simp [union, complement, derLB, matchStep, laStep, top]
  | .middle mcount _ _ => cases mcount <;> simp [union, complement, derLB, matchStep, laStep, top]
  | .right mcount lacount _ => cases mcount <;> cases lacount <;> simp [union, complement, derLB, matchStep, laStep, top]

theorem derLB_symb (a b : α) : derLB b (#a) ≐ (#a - (↑₂ #a ∪ ↑₃ #a)):= by
  intro w
  match w with
  | .left _ _ _ => simp [derLB, complement, union, matchStep, laStep, symb]
  | .middle mcount (y, ys) _ =>
    cases mcount with
    | zero => cases ys <;> simp [derLB, complement, union, matchStep, laStep, symb, toList, Eq.comm]
    | succ n => simp [derLB, complement, union, matchStep, laStep, symb]
  | .right mcount lacount _ => cases mcount <;> cases lacount <;> simp [derLB, complement, union, matchStep, laStep, symb]

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

theorem derLB_complement (a : α) (k l : Lang α): derLB a (k - l) ≐ ((derLB a k) - (derLB a l)) := by
  intro w
  match w with
  | .left _ _ _ => simp [complement, derLB]
  | .middle mcount _ _ => cases mcount <;> simp [complement, derLB]
  | .right mcount lacount _ => cases mcount <;> cases lacount <;> simp [complement, derLB]



theorem derLB_concat (a : α) (k l : Lang α) : derLB a (k • l) ≐ derLB a k • derLB a l := by
  intro w
  match w with
  | .left lb main la =>
    constructor
    . rintro ⟨w₁, w₂, hk, hl, pref, suff, hmain, rfl, rfl⟩; exact ⟨.left lb pref (suff ++ la), .left (lb.fst, lb.snd ++ pref) suff la, hk, hl, pref, suff, hmain, rfl, rfl⟩
    . rintro ⟨w₁, w₂, hk, hl, pref, suff, hmain, rfl, rfl⟩; exact ⟨.left (a, toList lb) pref (suff ++ la), .left (a, (toList lb) ++ pref) suff la, hk, hl, pref, suff, hmain, rfl, rfl⟩
  | .middle mcount main la =>
    constructor
    . cases mcount with
      | zero =>
        rintro ⟨_, _, hk, hl, pref, suff, hmain, rfl, rfl⟩
        cases pref with
        | nil => simp [toList] at hmain; exact ⟨.right 0 0 (suff ++ la), .middle 0 main la, hk, by simp [←hmain] at hl; exact hl, Or.inr ⟨0, 0, rfl, by simp [toList, hmain], rfl⟩⟩
        | cons y ys  => simp [toList] at hmain; exact ⟨.middle 0 (y, ys) (suff ++ la), .left (y, ys) suff la, hk, hl, Or.inl ⟨ys, suff, hmain.2, by simp [hmain], by simp [hmain]⟩⟩
      | succ mcount => simp [derLB]
    . cases mcount with
      | zero =>
        rintro ⟨_ , _, hk, hl, h⟩;
        cases h with
        | inl h => obtain ⟨pref, suff, hmain, rfl, rfl⟩ := h; exact ⟨.left (a, []) (main.fst :: pref) (suff ++ la), .left (a, main.fst :: pref) suff la, hk, hl, (main.fst :: pref), suff, by simp [toList, hmain], rfl, rfl⟩
        | inr h => obtain ⟨_ , _, hmcount, rfl, rfl⟩ := h; simp at hmcount; obtain ⟨rfl, rfl⟩ := hmcount; exact ⟨.left (a, []) [] (toList main ++ la), .left (a, []) (toList main) la, hk, hl, [], (toList main), rfl, rfl, rfl⟩
      | succ mcount =>
        rintro ⟨w₁, w₂, hk, hl, h⟩
        cases h with
        | inl h => obtain ⟨_, _, _, rfl, _⟩ := h; simp [derLB] at hk
        | inr h => obtain ⟨mc₁, mc₂, hmcount, rfl, rfl⟩ := h; cases mc₁ <;> cases mc₂ <;> simp [derLB] at hk hl; simp at hmcount
  | .right mcount lacount la =>
    cases mcount with
    | zero =>
      cases lacount with
      | zero =>
        constructor
        . rintro ⟨_, _, hk, hl, pref, suff, hmain, rfl, rfl⟩; simp at hmain; obtain ⟨rfl, rfl⟩ := hmain; exact ⟨.right 0 0 la, .right 0 0 la, hk, hl, 0, 0, rfl, rfl, rfl⟩
        . rintro ⟨_, _, hk, hl, mc₁, mc₂, hmcount, rfl, rfl⟩; symm at hmcount; simp [Nat.add_eq_zero_iff] at hmcount; obtain ⟨rfl, rfl⟩ := hmcount
          exact ⟨.left (a, []) [] la, .left (a, []) [] la, hk, hl, [], [], rfl, rfl, rfl⟩
      | succ lacount => simp [derLB]; rintro ⟨_, _, hk, _, _, _, _, rfl, _⟩; simp [derLB] at hk
    | succ mcount =>
      cases lacount with
      | zero => simp [derLB]; rintro ⟨_, _, hk, hl, mc₁, mc₂, hmcount, rfl, rfl⟩; cases mc₁ <;> cases mc₂ <;> simp [derLB] at hk hl hmcount
      | succ lacounct => simp [derLB]; rintro ⟨_, _, hk, hl, mc₁, mc₂, hmcount, rfl, rfl⟩; cases mc₁ <;> cases mc₂ <;> simp [derLB] at hk hl hmcount


theorem derLB_star (a : α) (l base : Lang α) : derLB a (star l base) ≐ star (derLB a l) (derLB a base) := by
  intro w
  match w with
  | .left (x, xs) main la => exact derLB_star_left a l base x xs main la
  | .middle mcount main la =>
    cases mcount with
    | zero => exact derLB_star_middle a l base main la
    | succ mcount =>
      simp [derLB]; intro h
      cases h with
      | inUnit w hunit => simp [derLB] at hunit
      | inConcat w₁ w₂ w hl _ hwc =>
        rcases hwc with ⟨_, _, _, rfl, _⟩ | ⟨mc₁, mc₂, hmcount, rfl, _⟩
        · simp [derLB] at hl
        · cases mc₁ with
          | zero =>
            cases mc₂ with
            | zero => simp at hmcount
            | succ mc₂ => simp [derLB] at hl
          | succ mc₁ => simp [derLB] at hl
  | .right mcount lacount la =>
    cases mcount with
    | zero =>
      cases lacount with
      | zero => exact derLB_star_right a l base la
      | succ lacount =>
        simp [derLB]; intro h
        cases h with
        | inUnit w hunit => simp [derLB] at hunit
        | inConcat w₁ w₂ w hl _ hwc =>
          obtain ⟨mc₁, mc₂, _, rfl, _⟩ := hwc; cases mc₁ <;> simp [derLB] at hl
    | succ mcount =>
      simp [derLB]; intro h
      cases h with
      | inUnit w hunit => simp [derLB] at hunit
      | inConcat w₁ w₂ w hl _ hwc =>
        obtain ⟨mc₁, mc₂, hmcount, rfl, _⟩ := hwc
        cases mc₁ with
        | zero =>
          cases lacount with
          | zero => cases mc₂ <;> simp [derLB] at hl <;> simp at hmcount
          | succ lacount => cases mc₂ <;> simp [derLB] at hl
        | succ mc₁ => simp [derLB] at hl



theorem derLB_lb (a : α) (l : Lang α) : derLB a (◁ l) ≐ ◁ (der a l)  := by
  intro w
  match w with
  | .left lb main la =>
    cases main with
    | nil => exact (exists_der_middle a l lb la).symm
    | cons _ _ => simp [derLB, lookbehind]
  | .middle mcount main la  => cases mcount <;> simp [derLB, lookbehind, toList]
  | .right mcount lacount la =>
    cases mcount with
    | succ _ => simp [derLB, lookbehind]
    | zero =>
      cases lacount with
      | zero => exact (exists_der_right a l la).symm
      | succ _ => simp [derLB, lookbehind, der]

theorem derLB_la (a : α) (l : Lang α) : derLB a (▷ l) ≐ ▷ (derLB a l) := by
  intro w
  match w with
  | .left _ main _  => cases main <;> simp [derLB, lookahead]
  | .middle mcount _ _  => cases mcount <;> simp [derLB, lookahead, toList]
  | .right mcount lacount la => cases mcount <;> cases lacount <;> cases la <;> simp [derLB, lookahead, toList]

/- theorem derLB_lbStep (a : α) (l : Lang α) : derLB a (↑₁ l) ≐ ↑₁ (derLB a l) := by
  intro w
  match w with
  | .left lbcount _ _ _   => rcases lbcount with _ | _ | _ <;> simp [derLB, lbStep, toList]
  | .middle lbcount mcount _ _  => rcases lbcount with _ | _ | _ <;> cases mcount <;> simp [derLB, lbStep]
  | .right lbcount mcount lacount _ => rcases lbcount with _ | _ | _ <;> cases mcount <;> cases lacount <;> simp [derLB, lbStep]
 -/
theorem derLB_matchStep (a : α) (l : Lang α) : derLB a (↑₂ l) ≐ ∅ := by
  intro w
  match w with
  | .left _ _ _   => simp [derLB, matchStep, empty]
  | .middle mcount _ _  => cases mcount <;> simp [derLB, matchStep, empty]
  | .right mcount lacount _ => cases mcount <;> cases lacount <;> simp [derLB, matchStep, empty]

theorem derLB_LAStep (a : α) (l : Lang α) : derLB a (↑₃ l) ≐ ∅  := by
  intro w
  match w with
  | .left _ _ _   => simp [derLB, laStep, empty]
  | .middle mcount _ _  => cases mcount <;> simp [derLB, laStep, empty]
  | .right mcount lacount _ => cases mcount <;> cases lacount <;> simp [derLB, laStep, empty]

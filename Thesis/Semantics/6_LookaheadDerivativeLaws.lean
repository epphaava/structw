import Thesis.Semantics.«1_StructuredWords»
import Thesis.Semantics.«2_Operators»
import Thesis.Semantics.«3_Derivatives»
import Thesis.Semantics.Helpers.«6_LookaheadDerivativeLaws»

namespace derLALaws

open StructuredWords
open Operators
open derLALawsHelpers

-- Proposition 3.4.1 (Derivative laws for structured languages).

theorem derLA_empty (a : α) : derLA a ∅ ≐ ∅ := by
  intro w
  match w with
  | .left _ _ _ => simp [derLA, empty]
  | .middle _ _ _ => simp [derLA, empty]
  | .right mcount lacount _ => cases mcount <;> cases lacount <;> simp [derLA, empty]

theorem derLA_unit (a : α) : derLA a I ≐ ↑₃ I := by
  intro w
  match w with
  | .left _ _ _ => simp [laStep, derLA]
  | .middle _ _ _ => simp [laStep, derLA]
  | .right mcount lacount _ => cases mcount <;> cases lacount <;> simp [laStep, derLA, unit]

theorem derLA_top (a : α) : derLA a T ≐ ↑₃ T := by
  intro w
  match w with
  | .left _ _ _ => simp [derLA, laStep]
  | .middle _ _ _ => simp [derLA, laStep]
  | .right mcount lacount _ => cases mcount <;> cases lacount <;> simp [derLA, laStep, top]

theorem derLA_symb (a b : α) : derLA b (#a) ≐ ∅ := by
  intro w
  match w with
  | .left _ _ _ => simp [derLA, empty]
  | .middle _ _ _ => simp [derLA, empty]
  | .right mcount lacount _ => cases mcount <;> cases lacount <;> simp [derLA, empty, symb]

theorem derLA_union (a : α) (k l : Lang α) : derLA a (k ∪ l) ≐ derLA a k ∪ derLA a l := by
  intro w
  match w with
  | .left _ _ _ => simp [derLA, union]
  | .middle _ _ _ => simp [derLA, union]
  | .right mcount lacount _ => cases mcount <;> cases lacount <;> simp [derLA, union]

theorem derLA_intersection (a : α) (k l : Lang α): derLA a (k ∩ l) ≐ (derLA a k) ∩ (derLA a l) := by
  intro w
  match w with
  | .left _ _ _ => simp [derLA, intersection]
  | .middle _ _ _ => simp [derLA, intersection]
  | .right mcount lacount _ => cases mcount <;> cases lacount <;> simp [derLA, intersection]

theorem derLA_complement (a : α) (k l : Lang α): derLA a (k - l) ≐ ((derLA a k) - (derLA a l)) := by
  intro w
  match w with
  | .left _ _ _ => simp [derLA, complement]
  | .middle _ _ _ => simp [derLA, complement]
  | .right mcount lacount _ => cases mcount <;> cases lacount <;> simp [derLA, complement]

theorem derLA_concat (a : α) (k l : Lang α) : derLA a (k • l) ≐ derLA a k • derLA a l := by
  intro w
  match w with
  | .left _ _ _ =>
    constructor
    . simp [derLA]
    . rintro ⟨_, _, hk, _, _, _, _, rfl, _⟩; simp [derLA] at hk
  | .middle _ _ _ =>
    constructor
    . simp [derLA]
    . rintro ⟨_, _, hk, hl, ⟨_, _, _, rfl, _⟩ | ⟨_, _, _, _, rfl⟩⟩
      · simp [derLA] at hk
      · simp [derLA] at hl
  | .right mcount lacount la =>
    constructor
    . cases lacount with
      | zero => simp [derLA]
      | succ lacount => rintro ⟨_, _, hk, hl, mc₁, mc₂, hmcount, rfl, rfl⟩; exact ⟨.right mc₁ (mc₂ + lacount).succ la, .right mc₂ lacount.succ la, hk, hl, mc₁, mc₂, hmcount, rfl, rfl⟩
    . rintro ⟨_, _, hk, hl, mc₁, mc₂, rfl, rfl, rfl⟩;
      cases lacount with
      | zero => simp [derLA] at hl
      | succ lacount => exact ⟨.right mc₁ (mc₂ + lacount) (a :: la), .right mc₂ lacount (a :: la), hk, hl, mc₁, mc₂, rfl, rfl, rfl⟩


theorem derLA_star (a : α) (l base : Lang α) : derLA a (star l base) ≐ star (derLA a l) (derLA a base) := by
  intro w
  match w with
  | .left _ _ _ =>
    simp [derLA]; intro h
    cases h with
    | inUnit _ hu => simp [derLA] at hu
    | inConcat w₁ _ _ hl _ hwc => obtain ⟨_, _, _, rfl, _⟩ := hwc; simp [derLA] at hl
  | .middle mcount main la =>
    simp [derLA]
    suffices key : ∀ w, star_help (derLA a l) (derLA a base) w →
        ∀ mcount main la, w = .middle mcount main la → False from
      fun h => key _ h mcount main la rfl
    intro _ h
    induction h with
    | inUnit _ hu => intro _ _ _ hw; subst hw; simp [derLA] at hu
    | inConcat w₁ w₂ _ hl _ hwc ih =>
      intro _ _ _ rfl;
      rcases hwc with ⟨_, _, _, rfl, _⟩ | ⟨_, _, _, _, rfl⟩
      · simp [derLA] at hl
      · exact ih _ _ _ rfl
  | .right mcount lacount la =>
    cases lacount with
    | zero =>
      simp [derLA]
      suffices key : ∀ w, star_help (derLA a l) (derLA a base) w →
          ∀ mcount la, w = .right mcount 0 la → False from
        fun h => key _ h mcount la rfl
      intro _ h
      induction h with
      | inUnit _ hu => intro _ _ hw; subst hw; simp [derLA] at hu
      | inConcat w₁ w₂ _ hl _ hwc ih => intro _ _ rfl; obtain ⟨_, _, _, _, rfl⟩ := hwc; exact ih _ _ rfl
    | succ lacount => exact derLA_star_right a l base mcount lacount la


theorem derLA_lb (a : α) (l : Lang α) : derLA a (◁ l) ≐ (◁ (derLA a l)) := by
  intro w
  match w with
  | .left _ main _ => cases main <;> simp [lookbehind, derLA]
  | .middle _ _ _ => simp [lookbehind, derLA]
  | .right mcount lacount _ => cases mcount <;> cases lacount <;> simp [derLA, lookbehind]

theorem derLA_la (a : α) (l : Lang α) : derLA a (▷ l) ≐ ▷ (der a l)  := by
  intro w
  match w with
  | .left _ main _ => cases main <;> simp [derLA, lookahead, der]
  | .middle _ _ _ => simp [derLA, lookahead]
  | .right mcount lacount la => cases mcount <;> cases lacount <;> cases la <;> simp [derLA, lookahead, der, toList]

/- theorem derLA_lbStep (a : α) (l : Lang α) : derLA a (↑₁ l) ≐ ↑₁ (derLA a l) := by
  intro w
  match w with
  | .left lbc _ _ _ => cases lbc <;> simp [derLA, lbStep]
  | .middle lbc mcount _ _ => cases lbc <;> cases mcount <;> simp [derLA, lbStep]
  | .right lbc mcount lacount _ => cases lbc <;> cases mcount <;> cases lacount <;> simp [derLA, lbStep] -/

theorem derLA_matchStep (a : α) (l : Lang α) : derLA a (↑₂ l) ≐ ↑₂ (derLA a l) := by
  intro w
  match w with
  | .left _ _ _ => simp [derLA, matchStep]
  | .middle mcount _ _ => cases mcount <;> simp [derLA, matchStep]
  | .right mcount lacount _ => cases mcount <;> cases lacount <;> simp [derLA, matchStep]

theorem derLA_laStep (a : α) (l : Lang α) : derLA a (↑₃ l) ≐ ↑₃ (derLA a l) := by
  intro w
  match w with
  | .left _ _ _ => simp [derLA, laStep]
  | .middle mcount _ _ => cases mcount <;> simp [derLA, laStep]
  | .right mcount lacount _ => rcases lacount with _ | _ | _ <;> cases mcount <;> simp [derLA, laStep]

import Thesis.Semantics.«1_StructuredWords»
import Thesis.Semantics.«2_Operators»
import Thesis.Semantics.«3_Derivatives»

namespace derLALaws

open StructuredWords
open Operators

-- Proposition 3.4.1 (Derivative laws for structured languages).

theorem derLA_empty (a : α) : derLA a ∅ ≐ ∅ := by
  intro w
  match w with
  | .left _ _ _ _ => simp [derLA, empty]
  | .middle _ _ _ _ => simp [derLA, empty]
  | .right _ mcount lacount _ => cases mcount <;> cases lacount <;> simp [derLA, empty]

theorem derLA_unit (a : α) : derLA a I ≐ ↑₃ I := by
  intro w
  match w with
  | .left _ _ _ _ => simp [laStep, derLA]
  | .middle _ _ _ _ => simp [laStep, derLA]
  | .right _ mcount lacount _ => cases mcount <;> cases lacount <;> simp [laStep, derLA, unit]

theorem derLA_top (a : α) : derLA a T ≐ ↑₃ T := by
  intro w
  match w with
  | .left _ _ _ _ => simp [derLA, laStep]
  | .middle _ _ _ _ => simp [derLA, laStep]
  | .right _ mcount lacount _ => cases mcount <;> cases lacount <;> simp [derLA, laStep, top]

theorem derLA_symb (a b : α) : derLA b (#a) ≐ ∅ := by
  intro w
  match w with
  | .left _ _ _ _ => simp [derLA, empty]
  | .middle _ _ _ _ => simp [derLA, empty]
  | .right _ mcount lacount _ => cases mcount <;> cases lacount <;> simp [derLA, empty, symb]

theorem derLA_union (a : α) (k l : Lang α) : derLA a (k ∪ l) ≐ derLA a k ∪ derLA a l := by
  intro w
  match w with
  | .left _ _ _ _ => simp [derLA, union]
  | .middle _ _ _ _ => simp [derLA, union]
  | .right _ mcount lacount _ => cases mcount <;> cases lacount <;> simp [derLA, union]

theorem derLA_intersection (a : α) (k l : Lang α): derLA a (k ∩ l) ≐ (derLA a k) ∩ (derLA a l) := by
  intro w
  match w with
  | .left _ _ _ _ => simp [derLA, intersection]
  | .middle _ _ _ _ => simp [derLA, intersection]
  | .right _ mcount lacount _ => cases mcount <;> cases lacount <;> simp [derLA, intersection]

theorem derLA_complement (a : α) (k l : Lang α): derLA a (k - l) ≐ ((derLA a k) - (derLA a l)) := by
  intro w
  match w with
  | .left _ _ _ _ => simp [derLA, complement]
  | .middle _ _ _ _ => simp [derLA, complement]
  | .right _ mcount lacount _ => cases mcount <;> cases lacount <;> simp [derLA, complement]

theorem derLA_concat (a : α) (k l : Lang α) : derLA a (k • l) ≐ derLA a k • derLA a l := by
  intro w
  match w with
  | .left _ _ _ _ =>
    constructor
    . simp [derLA]
    . rintro ⟨_, _, hk, _, _, _, _, rfl, _⟩; simp [derLA] at hk
  | .middle _ _ _ _ =>
    constructor
    . simp [derLA]
    . rintro ⟨_, _, hk, hl, ⟨_, _, _, rfl, _⟩ | ⟨_, _, _, _, rfl⟩⟩
      · simp [derLA] at hk
      · simp [derLA] at hl
  | .right lbc mcount lacount la =>
    constructor
    . cases lacount with
      | zero => simp [derLA]
      | succ lacount => rintro ⟨_, _, hk, hl, mc₁, mc₂, hmcount, rfl, rfl⟩; exact ⟨.right lbc mc₁ (mc₂ + lacount).succ la, .right (lbc + mc₁) mc₂ lacount.succ la, hk, hl, mc₁, mc₂, hmcount, rfl, rfl⟩
    . rintro ⟨_, _, hk, hl, mc₁, mc₂, rfl, rfl, rfl⟩;
      cases lacount with
      | zero => simp [derLA] at hl
      | succ lacount => exact ⟨.right lbc mc₁ (mc₂ + lacount) (a :: la), .right (lbc + mc₁) mc₂ lacount (a :: la), hk, hl, mc₁, mc₂, rfl, rfl, rfl⟩

theorem derLA_star_right (a : α) (l base : Lang α) : ∀ (lbc mc lac : Nat) (la : List α),
    star_help l base (.right lbc mc lac (a :: la)) ↔ star_help (derLA a l) (derLA a base) (.right lbc mc (lac + 1) la) := by
  intro lbc mc lac la
  constructor
  · suffices key : ∀ w, star_help l base w → ∀ lbc mc lac la, w = .right lbc mc lac (a :: la) →
        star_help (derLA a l) (derLA a base) (.right lbc mc (lac + 1) la) from fun h => key _ h lbc mc lac la rfl
    intro _ h
    induction h with
    | inUnit w hu => intro _ _ _ _ hw; subst hw; exact star_help.inUnit _ hu
    | inConcat w₁ w₂ w hl _ hwc ih =>
      intro lbc mc lac la rfl; obtain ⟨mc₁, mc₂, rfl, rfl, rfl⟩ := hwc;
      exact star_help.inConcat (.right lbc mc₁ (mc₂ + (lac + 1)) la) (.right (lbc + mc₁) mc₂ (lac + 1) la) _
        hl (ih (lbc + mc₁) mc₂ lac la rfl) ⟨mc₁, mc₂, rfl, rfl, rfl⟩
  · suffices key : ∀ w, star_help (derLA a l) (derLA a base) w → ∀ lbc mc lac la, w = .right lbc mc (lac + 1) la →
        star_help l base (.right lbc mc lac (a :: la)) from fun h => key _ h lbc mc lac la rfl
    intro _ h
    induction h with
    | inUnit w hu => intro _ _ _ _ hw; subst hw; exact star_help.inUnit _ hu
    | inConcat w₁ w₂ w hl _ hwc ih =>
      intro lbc mc lac la rfl; obtain ⟨mc₁, mc₂, rfl, rfl, rfl⟩ := hwc;
      exact star_help.inConcat (.right lbc mc₁ (mc₂ + lac) (a :: la)) (.right (lbc + mc₁) mc₂ lac (a :: la)) _
        hl (ih (lbc + mc₁) mc₂ lac la rfl) ⟨mc₁, mc₂, rfl, rfl, rfl⟩

theorem derLA_star (a : α) (l base : Lang α) : derLA a (star l base) ≐ star (derLA a l) (derLA a base) := by
  intro w
  match w with
  | .left _ _ _ _ =>
    simp [derLA]; intro h
    cases h with
    | inUnit _ hu => simp [derLA] at hu
    | inConcat w₁ _ _ hl _ hwc => obtain ⟨_, _, _, rfl, _⟩ := hwc; simp [derLA] at hl
  | .middle lbc mcount main la =>
    simp [derLA]
    suffices key : ∀ w, star_help (derLA a l) (derLA a base) w →
        ∀ lbc mcount main la, w = .middle lbc mcount main la → False from
      fun h => key _ h lbc mcount main la rfl
    intro _ h
    induction h with
    | inUnit _ hu => intro _ _ _ _ hw; subst hw; simp [derLA] at hu
    | inConcat w₁ w₂ _ hl _ hwc ih =>
      intro _ _ _ _ rfl;
      rcases hwc with ⟨_, _, _, rfl, _⟩ | ⟨_, _, _, _, rfl⟩
      · simp [derLA] at hl
      · exact ih _ _ _ _ rfl
  | .right lbc mcount lacount la =>
    cases lacount with
    | zero =>
      simp [derLA]
      suffices key : ∀ w, star_help (derLA a l) (derLA a base) w →
          ∀ lbc mcount la, w = .right lbc mcount 0 la → False from
        fun h => key _ h lbc mcount la rfl
      intro _ h
      induction h with
      | inUnit _ hu => intro _ _ _ hw; subst hw; simp [derLA] at hu
      | inConcat w₁ w₂ _ hl _ hwc ih => intro _ _ _ rfl; obtain ⟨_, _, _, _, rfl⟩ := hwc; exact ih _ _ _ rfl
    | succ lacount => exact derLA_star_right a l base lbc mcount lacount la


theorem derLA_lb (a : α) (l : Lang α) : derLA a (◁ l) ≐ (◁ (derLA a l)) := by
  intro w
  match w with
  | .left _ _ main _ => cases main <;> simp [lookbehind, derLA]
  | .middle _ _ _ _ => simp [lookbehind, derLA]
  | .right _ mcount lacount _ => cases mcount <;> cases lacount <;> simp [derLA, lookbehind]

theorem derLA_la (a : α) (l : Lang α) : derLA a (▷ l) ≐ ▷ (der a l)  := by
  intro w
  match w with
  | .left _ _ main _ => cases main <;> simp [derLA, lookahead, der]
  | .middle _ _ _ _ => simp [derLA, lookahead]
  | .right _ mcount lacount la => cases mcount <;> cases lacount <;> cases la <;> simp [derLA, lookahead, der, toList]

theorem derLA_lbStep (a : α) (l : Lang α) : derLA a (↑₁ l) ≐ ↑₁ (derLA a l) := by
  intro w
  match w with
  | .left lbc _ _ _ => cases lbc <;> simp [derLA, lbStep]
  | .middle lbc mcount _ _ => cases lbc <;> cases mcount <;> simp [derLA, lbStep]
  | .right lbc mcount lacount _ => cases lbc <;> cases mcount <;> cases lacount <;> simp [derLA, lbStep]

theorem derLA_matchStep (a : α) (l : Lang α) : derLA a (↑₂ l) ≐ ↑₂ (derLA a l) := by
  intro w
  match w with
  | .left _ _ _ _ => simp [derLA, matchStep]
  | .middle _ mcount _ _ => cases mcount <;> simp [derLA, matchStep]
  | .right _ mcount lacount _ => cases mcount <;> cases lacount <;> simp [derLA, matchStep]

theorem derLA_laStep (a : α) (l : Lang α) : derLA a (↑₃ l) ≐ ↑₃ (derLA a l) := by
  intro w
  match w with
  | .left _ _ _ _ => simp [derLA, laStep]
  | .middle _ mcount _ _ => cases mcount <;> simp [derLA, laStep]
  | .right _ mcount lacount _ => rcases lacount with _ | _ | _ <;> cases mcount <;> simp [derLA, laStep]

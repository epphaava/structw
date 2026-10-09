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
    . intro h; obtain ⟨w₁, w₂, hk, hl, h⟩ := h;
      cases h with
      | inl h => obtain ⟨_, _, _, _, _⟩ := h; subst w₁; simp [derLA] at hk
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

theorem derLA_star_right (a : α) (l : Lang α) : ∀ (mc lac : Nat) (la : List α),
    star_help I l (.right mc lac (a :: la)) ↔ star_help (derLA a I) (derLA a l) (.right mc (lac + 1) la) := by
  intro mc lac la
  constructor
  · suffices key : ∀ w, star_help I l w → ∀ mc lac la, w = .right mc lac (a :: la) →
        star_help (derLA a I) (derLA a l) (.right mc (lac + 1) la) by exact fun h => key _ h mc lac la rfl
    intro w h
    induction h with
    | inUnit w hu => intro mc lac la _; subst w;  exact star_help.inUnit _ hu
    | inConcat w₁ w₂ w hl _ hwc ih =>
      intro mc lac la _; subst w; obtain ⟨mc₁, mc₂, rfl, rfl, rfl⟩ := hwc
      exact star_help.inConcat (.right mc₁ (mc₂ + (lac + 1)) la) (.right mc₂ (lac + 1) la) _
        hl (ih mc₂ lac la rfl) ⟨mc₁, mc₂, rfl, rfl, rfl⟩
  · suffices key : ∀ w, star_help (derLA a I) (derLA a l) w → ∀ mc lac la, w = .right mc (lac + 1) la →
        star_help I l (.right mc lac (a :: la)) by exact fun h => key _ h mc lac la rfl
    intro w h
    induction h with
    | inUnit w hu => rintro mc lac la _; subst w; exact star_help.inUnit _ hu
    | inConcat w₁ w₂ w hl _ hwc ih =>
      intro mc lac la _; subst w; obtain ⟨mc₁, mc₂, rfl, rfl, rfl⟩ := hwc
      exact star_help.inConcat (.right mc₁ (mc₂ + lac) (a :: la)) (.right mc₂ lac (a :: la)) _
        hl (ih mc₂ lac la rfl) ⟨mc₁, mc₂, rfl, rfl, rfl⟩

theorem derLA_star (a : α) (l : Lang α) : derLA a (l*) ≐ star (derLA a I) (derLA a l) := by
  intro w
  match w with
  | .left lb main la =>
    simp [derLA]; intro h
    cases h with
    | inUnit _ hu => simp [derLA] at hu
    | inConcat w₁ _ _ hl _ hwc => obtain ⟨_, _, _, rfl, _⟩ := hwc; simp [derLA] at hl
  | .middle mcount main la =>
    simp [derLA]
    suffices key : ∀ w, star_help (derLA a I) (derLA a l) w → ∀ mcount main la, w = .middle mcount main la → False by
      exact fun h => key _ h mcount main la rfl
    intro w h
    induction h with
    | inUnit _ hu => intro mcount main la rfl; simp [derLA] at hu
    | inConcat w₁ w₂ _ hl _ hwc ih =>
      intro mcount main la rfl
      rcases hwc with ⟨_, _, _, rfl, _⟩ | ⟨_, _, _, _, rfl⟩
      · simp [derLA] at hl
      · exact ih _ _ _ rfl
  | .right mcount lacount la =>
    cases lacount with
    | zero =>
      simp [derLA]
      suffices key : ∀ w, star_help (derLA a I) (derLA a l) w → ∀ mcount la, w = .right mcount 0 la → False by
        exact fun h => key _ h mcount la rfl
      intro w h
      induction h with
      | inUnit _ hu => intro mcount la rfl; simp [derLA] at hu
      | inConcat w₁ w₂ _ hl _ hwc ih => intro mcount la rfl; obtain ⟨_, _, _, _, rfl⟩ := hwc; exact ih _ _ rfl
    | succ lacount => exact derLA_star_right a l mcount lacount la



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
    | succ mcount =>
      cases mcount <;> cases lacount with
      | zero => simp [derLA, matchStep]
      | succ lacount => cases lacount <;> simp [derLA, matchStep]

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

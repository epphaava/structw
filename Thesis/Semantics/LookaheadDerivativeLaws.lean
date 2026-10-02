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

theorem derLA_star (a : α) (l : Lang α) : derLA a (l*) ≐ ▹ₗ I ∪ (derLA a l • derLA a (l*)) := by
  intro w
  match w with
  | .left lb main la => simp [derLA, LAStep, union]; intro ⟨w₁, _, hk, _, ⟨_, _, _, _, _⟩⟩; subst w₁; simp [derLA] at hk
  | .middle mcount main la =>
    simp [derLA, LAStep, union]
    rintro ⟨_, _, hk, hl, ⟨_, _, _, rfl, _⟩ | ⟨_, _, _, _, rfl⟩⟩
    · simp [derLA] at hk
    · simp [derLA] at hl
  | .right mcount lacount la =>
    cases lacount with
    | zero => simp [derLA, LAStep, union]; intro ⟨_, w₂, _, hstar, _, _, _, _, _⟩; subst w₂; simp [derLA] at hstar
    | succ lacount =>
      constructor
      · intro h
        simp only [derLA] at h
        cases h with
        | inUnit _ hu => left; cases mcount <;> simp [LAStep, unit] at hu ⊢
        | inConcat w₁ w₂ _ hl hs hwc =>
          obtain ⟨mc₁, mc₂, rfl, rfl, rfl⟩ := hwc; right
          exact ⟨.right mc₁ (mc₂ + (lacount + 1)) la, .right mc₂ (lacount + 1) la, hl, hs, mc₁, mc₂, rfl, rfl, rfl⟩
      · rintro (hu | ⟨x, y, hx, hy, mc₁, mc₂, rfl, rfl, rfl⟩)
        · exact star_help.inUnit _ (by cases mcount <;> simp [LAStep, unit] at hu ⊢)
        · exact star_help.inConcat (.right mc₁ (mc₂ + lacount) (a :: la)) (.right mc₂ lacount (a :: la)) _ hx hy ⟨mc₁, mc₂, rfl, rfl, rfl⟩

theorem derLA_star_right_help (a : α) (l : Lang α) : ∀ (mc n : Nat) (la : List α),
    star_help l (.right mc n (a :: la)) ↔ star_help (derLA a l) (.right mc (n + 1) la) := by
  intro mc n la
  constructor
  · suffices key : ∀ w, star_help l w → ∀ mc n la, w = .right mc n (a :: la) →
        star_help (derLA a l) (.right mc (n + 1) la) by exact fun h => key _ h mc n la rfl
    intro w h
    induction h with
    | inUnit _ hu => rintro mc n la rfl; exact star_help.inUnit _ (by simpa [unit] using hu)
    | inConcat w₁ w₂ _ hl _ hwc ih =>
      rintro mc n la rfl
      obtain ⟨mc₁, mc₂, rfl, rfl, rfl⟩ := hwc
      exact star_help.inConcat (.right mc₁ (mc₂ + (n + 1)) la) (.right mc₂ (n + 1) la) _
        hl (ih mc₂ n la rfl) ⟨mc₁, mc₂, rfl, rfl, rfl⟩
  · suffices key : ∀ w, star_help (derLA a l) w → ∀ mc n la, w = .right mc (n + 1) la →
        star_help l (.right mc n (a :: la)) by exact fun h => key _ h mc n la rfl
    intro w h
    induction h with
    | inUnit _ hu => rintro mc n la rfl; exact star_help.inUnit _ (by simpa [unit] using hu)
    | inConcat w₁ w₂ _ hl _ hwc ih =>
      rintro mc n la rfl
      obtain ⟨mc₁, mc₂, rfl, rfl, rfl⟩ := hwc
      exact star_help.inConcat (.right mc₁ (mc₂ + n) (a :: la)) (.right mc₂ n (a :: la)) _
        hl (ih mc₂ n la rfl) ⟨mc₁, mc₂, rfl, rfl, rfl⟩

theorem derLA_star' (a : α) (l : Lang α) : derLA a (l*) ≐ ((derLA a l)* ∩ ▹ₗ T) := by
  intro w
  match w with
  | .left _ _ _ => simp [derLA, intersection, LAStep]
  | .middle _ _ _ => simp [derLA, intersection, LAStep]
  | .right mc 0 la => simp [derLA, intersection, LAStep]
  | .right mc (n + 1) la =>
    simp [derLA, intersection, LAStep, top, star]
    constructor
    · suffices key : ∀ w, star_help l w → ∀ mc n la, w = .right mc n (a :: la) →
          star_help (derLA a l) (.right mc (n + 1) la) by exact fun h => key _ h mc n la rfl
      intro w h
      induction h with
      | inUnit _ hu => rintro mc n la rfl; exact star_help.inUnit _ (by simpa [unit] using hu)
      | inConcat w₁ w₂ _ hl _ hwc ih =>
        rintro mc n la rfl
        obtain ⟨mc₁, mc₂, rfl, rfl, rfl⟩ := hwc
        exact star_help.inConcat (.right mc₁ (mc₂ + (n + 1)) la) (.right mc₂ (n + 1) la) _
          hl (ih mc₂ n la rfl) ⟨mc₁, mc₂, rfl, rfl, rfl⟩
    · suffices key : ∀ w, star_help (derLA a l) w → ∀ mc n la, w = .right mc (n + 1) la →
          star_help l (.right mc n (a :: la)) by exact fun h => key _ h mc n la rfl
      intro w h
      induction h with
      | inUnit _ hu => rintro mc n la rfl; exact star_help.inUnit _ (by simpa [unit] using hu)
      | inConcat w₁ w₂ _ hl _ hwc ih =>
        rintro mc n la rfl
        obtain ⟨mc₁, mc₂, rfl, rfl, rfl⟩ := hwc
        exact star_help.inConcat (.right mc₁ (mc₂ + n) (a :: la)) (.right mc₂ n (a :: la)) _
          hl (ih mc₂ n la rfl) ⟨mc₁, mc₂, rfl, rfl, rfl⟩


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

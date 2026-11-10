import Thesis.Semantics.«1_StructuredWords»
import Thesis.Semantics.«2_Operators»
import Thesis.Semantics.«3_Derivatives»

namespace derLBLaws

open StructuredWords
open Operators

-- Proposition 3.4.1 (Derivative laws for structured languages).

theorem derLB_empty (a : α) : derLB a ∅ ≐ ∅ := by
  intro w
  rcases w with ⟨_, _, _⟩ | ⟨_ | _, _, _⟩ | ⟨_ | _, _ | _, _⟩ <;> simp [derLB, empty]

theorem derLB_unit (a : α) : derLB a I ≐ (I - ↑₃ I) := by
  intro w
  rcases w with ⟨_, _, _⟩ | ⟨_ | _, _, _⟩ | ⟨_ | _, _ | _, _⟩ <;> simp [complement, derLB, laStep, unit, toList]

theorem derLB_top (a : α) : derLB a T ≐ (T - (↑₂ T ∪ ↑₃ T)) := by
  intro w
  rcases w with ⟨_, _, _⟩ | ⟨_ | _, _, _⟩ | ⟨_ | _, _ | _, _⟩ <;> simp [union, complement, derLB, matchStep, laStep, top]

theorem derLB_symb (a b : α) : derLB b (#a) ≐ (#a - (↑₂ #a ∪ ↑₃ #a)) := by
  intro w
  rcases w with ⟨_, _, _⟩ | ⟨_ | _, ⟨y, _ | _⟩, _⟩ | ⟨_ | _, _ | _, _⟩ <;>
    simp [derLB, complement, union, matchStep, laStep, symb, toList, Eq.comm]

theorem derLB_union (a : α) (k l : Lang α) : derLB a (k ∪ l) ≐ derLB a k ∪ derLB a l := by
  intro w
  rcases w with ⟨_, _, _⟩ | ⟨_ | _, _, _⟩ | ⟨_ | _, _ | _, _⟩ <;> simp [derLB, union]

theorem derLB_intersection (a : α) (k l : Lang α) : derLB a (k ∩ l) ≐ (derLB a k) ∩ (derLB a l) := by
  intro w
  rcases w with ⟨_, _, _⟩ | ⟨_ | _, _, _⟩ | ⟨_ | _, _ | _, _⟩ <;> simp [intersection, derLB]

theorem derLB_complement (a : α) (k l : Lang α) : derLB a (k - l) ≐ ((derLB a k) - (derLB a l)) := by
  intro w
  rcases w with ⟨_, _, _⟩ | ⟨_ | _, _, _⟩ | ⟨_ | _, _ | _, _⟩ <;> simp [complement, derLB]


theorem derLB_concat (a : α) (k l : Lang α) : derLB a (k • l) ≐ derLB a k • derLB a l := by
  intro w
  match w with
  | .left lb main la =>
    constructor
    · rintro ⟨_, _, hk, hl, pref, suff, hmain, rfl, rfl⟩
      exact ⟨.left lb pref (suff ++ la), .left (lb.fst, lb.snd ++ pref) suff la, hk, hl, pref, suff, hmain, rfl, rfl⟩
    · rintro ⟨_, _, hk, hl, pref, suff, hmain, rfl, rfl⟩
      exact ⟨.left (a, toList lb) pref (suff ++ la), .left (a, toList lb ++ pref) suff la, hk, hl, pref, suff, hmain, rfl, rfl⟩
  | .middle mcount main la =>
    cases mcount with
    | zero =>
      constructor
      · rintro ⟨_, _, hk, hl, pref, suff, hmain, rfl, rfl⟩
        cases pref with
        | nil =>
          simp [toList] at hmain
          exact ⟨.right 0 0 (suff ++ la), .middle 0 main la, hk, by simp [← hmain] at hl; exact hl,
            Or.inr ⟨0, 0, rfl, by simp [toList, hmain], rfl⟩⟩
        | cons y ys =>
          simp [toList] at hmain
          exact ⟨.middle 0 (y, ys) (suff ++ la), .left (y, ys) suff la, hk, hl,
            Or.inl ⟨ys, suff, hmain.2, by simp [hmain], by simp [hmain]⟩⟩
      · rintro ⟨_, _, hk, hl, h⟩
        cases h with
        | inl h =>
          obtain ⟨pref, suff, hmain, rfl, rfl⟩ := h
          exact ⟨.left (a, []) (main.fst :: pref) (suff ++ la), .left (a, main.fst :: pref) suff la, hk, hl,
            main.fst :: pref, suff, by simp [toList, hmain], rfl, rfl⟩
        | inr h =>
          obtain ⟨_, _, hmcount, rfl, rfl⟩ := h
          simp at hmcount; obtain ⟨rfl, rfl⟩ := hmcount
          exact ⟨.left (a, []) [] (toList main ++ la), .left (a, []) (toList main) la, hk, hl,
            [], toList main, rfl, rfl, rfl⟩
    | succ mcount =>
      simp [derLB]
      rintro ⟨_, _, hk, hl, ⟨_, _, _, rfl, _⟩ | ⟨mc₁, mc₂, hmcount, rfl, rfl⟩⟩
      · simp [derLB] at hk
      · cases mc₁ <;> cases mc₂ <;> simp [derLB] at hk hl <;> omega
  | .right mcount lacount la =>
    cases mcount with
    | zero =>
      cases lacount with
      | zero =>
        constructor
        · rintro ⟨_, _, hk, hl, pref, suff, hmain, rfl, rfl⟩
          simp at hmain; obtain ⟨rfl, rfl⟩ := hmain
          exact ⟨.right 0 0 la, .right 0 0 la, hk, hl, 0, 0, rfl, rfl, rfl⟩
        · rintro ⟨_, _, hk, hl, mc₁, mc₂, hmcount, rfl, rfl⟩
          obtain ⟨rfl, rfl⟩ : mc₁ = 0 ∧ mc₂ = 0 := by omega
          exact ⟨.left (a, []) [] la, .left (a, []) [] la, hk, hl, [], [], rfl, rfl, rfl⟩
      | succ lacount =>
        simp [derLB]
        rintro ⟨_, _, hk, _, mc₁, mc₂, _, rfl, _⟩
        cases mc₁ <;> simp [derLB] at hk
    | succ mcount =>
      simp [derLB]
      rintro ⟨_, _, hk, hl, mc₁, mc₂, hmcount, rfl, rfl⟩
      cases mc₁ <;> cases mc₂ <;> cases lacount <;> simp [derLB] at hk hl <;> omega


theorem derLB_star_left (a : α) (l base : Lang α) : ∀ (x : α) (xs main la : List α),
    star_help l base (.left (a, x :: xs) main la) ↔ star_help (derLB a l) (derLB a base) (.left (x, xs) main la) := by
  intro x xs main la
  constructor
  · suffices key : ∀ w, star_help l base w →
        ∀ x xs main la, w = .left (a, x :: xs) main la →
          star_help (derLB a l) (derLB a base) (.left (x, xs) main la) by
      intro h; exact key _ h x xs main la rfl
    intro _ h
    induction h with
    | inUnit w hunit => intro _ _ _ _ hw; subst hw; exact star_help.inUnit _ hunit
    | inConcat w₁ w₂ w hl _ hwc ih =>
      intro x xs main la hw; subst hw
      obtain ⟨pref, suff, hmain, h₁, h₂⟩ := hwc; subst h₁ h₂
      exact star_help.inConcat (.left (x, xs) pref (suff ++ la)) (.left (x, xs ++ pref) suff la) _
        hl (ih x (xs ++ pref) suff la rfl) ⟨pref, suff, hmain, rfl, rfl⟩
  · suffices key : ∀ w, star_help (derLB a l) (derLB a base) w →
        ∀ x xs main la, w = .left (x, xs) main la →
          star_help l base (.left (a, x :: xs) main la) by
      intro h; exact key _ h x xs main la rfl
    intro _ h
    induction h with
    | inUnit w hunit => intro _ _ _ _ hw; subst hw; exact star_help.inUnit _ hunit
    | inConcat w₁ w₂ w hl _ hwc ih =>
      intro x xs main la hw; subst hw
      obtain ⟨pref, suff, hmain, h₁, h₂⟩ := hwc; subst h₁ h₂
      exact star_help.inConcat (.left (a, x :: xs) pref (suff ++ la)) (.left (a, x :: (xs ++ pref)) suff la) _
        hl (ih x (xs ++ pref) suff la rfl) ⟨pref, suff, hmain, rfl, rfl⟩

theorem derLB_star_middle (a : α) (l base : Lang α) : ∀ (main : NEList α) (la : List α),
    star_help l base (.left (a, []) (toList main) la) ↔ star_help (derLB a l) (derLB a base) (.middle 0 main la) := by
  intro main la
  constructor
  · suffices key : ∀ w, star_help l base w →
        ∀ (main : NEList α) la, w = .left (a, []) (toList main) la →
          star_help (derLB a l) (derLB a base) (.middle 0 main la) by
      intro h; exact key _ h main la rfl
    intro _ h
    induction h with
    | inUnit w hunit => intro _ _ hw; subst hw; exact star_help.inUnit _ hunit
    | inConcat w₁ w₂ w hl hstar hwc ih =>
      intro main la hw; subst hw
      obtain ⟨pref, suff, hmain, h₁, h₂⟩ := hwc; subst h₁ h₂
      cases pref with
      | nil => exact ih main la (by simp [hmain])
      | cons y ys =>
        simp [toList] at hmain; obtain ⟨hy, hys⟩ := hmain
        exact star_help.inConcat (.middle 0 (y, ys) (suff ++ la)) (.left (y, ys) suff la) _
          hl ((derLB_star_left a l base y ys suff la).mp hstar)
          (Or.inl ⟨ys, suff, hys, by simp [hy], by simp [hy]⟩)
  · suffices key : ∀ w, star_help (derLB a l) (derLB a base) w →
        ∀ (main : NEList α) la, w = .middle 0 main la →
          star_help l base (.left (a, []) (toList main) la) by
      intro h; exact key _ h main la rfl
    intro _ h
    induction h with
    | inUnit w hunit => intro _ _ hw; subst hw; exact star_help.inUnit _ hunit
    | inConcat w₁ w₂ w hl hstar hwc ih =>
      intro main la hw; subst hw
      rcases hwc with ⟨pref, suff, hmain, h₁, h₂⟩ | ⟨mc₁, mc₂, hmcount, _, hw₂⟩
      · subst h₁ h₂
        exact star_help.inConcat (.left (a, []) (main.1 :: pref) (suff ++ la))
          (.left (a, main.1 :: pref) suff la) _
          hl ((derLB_star_left a l base main.1 pref suff la).mpr hstar)
          ⟨main.1 :: pref, suff, by simp [toList, hmain], rfl, rfl⟩
      · obtain ⟨rfl, rfl⟩ : mc₁ = 0 ∧ mc₂ = 0 := by omega
        exact ih main la hw₂

theorem derLB_star_right (a : α) (l base : Lang α) : ∀ (la : List α),
    star_help l base (.left (a, []) [] la) ↔ star_help (derLB a l) (derLB a base) (.right 0 0 la) := by
  intro la
  constructor
  · suffices key : ∀ w, star_help l base w →
        ∀ la, w = .left (a, []) [] la →
          star_help (derLB a l) (derLB a base) (.right 0 0 la) by
      intro h; exact key _ h la rfl
    intro _ h
    induction h with
    | inUnit w hunit => intro _ hw; subst hw; exact star_help.inUnit _ hunit
    | inConcat w₁ w₂ w hl _ hwc ih =>
      intro la hw; subst hw
      obtain ⟨pref, suff, hmain, h₁, h₂⟩ := hwc; subst h₁ h₂
      obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp hmain.symm
      exact star_help.inConcat (.right 0 0 la) (.right 0 0 la) _ hl (ih la rfl) ⟨0, 0, rfl, rfl, rfl⟩
  · suffices key : ∀ w, star_help (derLB a l) (derLB a base) w →
        ∀ la, w = .right 0 0 la →
          star_help l base (.left (a, []) [] la) by
      intro h; exact key _ h la rfl
    intro _ h
    induction h with
    | inUnit w hunit => intro _ hw; subst hw; exact star_help.inUnit _ hunit
    | inConcat w₁ w₂ w hl _ hwc ih =>
      intro la hw; subst hw
      obtain ⟨mc₁, mc₂, hmcount, h₁, h₂⟩ := hwc
      obtain ⟨rfl, rfl⟩ : mc₁ = 0 ∧ mc₂ = 0 := by omega
      subst h₁
      exact star_help.inConcat (.left (a, []) [] la) (.left (a, []) [] la) _ hl (ih la h₂) ⟨[], [], rfl, rfl, rfl⟩

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


theorem exists_der_middle (a : α) (l : Lang α) (main : NEList α) (la : List α) :
    (∃ k, der a l (.middle k main la)) ↔ ∃ k, l (.middle k (a, toList main) la) :=
  ⟨fun ⟨k, h⟩ => by cases k with
    | zero => simp [der] at h
    | succ k => exact ⟨k, h⟩,
   fun ⟨k, h⟩ => ⟨k + 1, h⟩⟩

theorem exists_der_right (a : α) (l : Lang α) (lac : Nat) (la : List α) :
    (∃ k, der a l (.right k lac la)) ↔ lac = 0 ∧ ∃ k, l (.middle k (a, []) la) :=
  ⟨fun ⟨k, h⟩ => by
    cases k with
    | zero => simp [der] at h
    | succ k => cases lac with
      | zero => exact ⟨rfl, k, h⟩
      | succ => simp [der] at h,
   fun ⟨hlac, k, h⟩ => ⟨k + 1, by subst hlac; exact h⟩⟩

theorem derLB_lb (a : α) (l : Lang α) : derLB a (◁ l) ≐ ◁ (der a l) := by
  intro w
  match w with
  | .left lb [] la => exact (exists_der_middle a l lb la).symm
  | .left _ (_ :: _) _ => simp [derLB, lookbehind]
  | .middle 0 _ _ => simp [derLB, lookbehind, toList]
  | .middle (_ + 1) _ _ => simp [derLB, lookbehind]
  | .right 0 lac la =>
    show derLB a (◁ l) (.right 0 lac la) ↔ ∃ k, der a l (.right k lac la)
    rw [exists_der_right]
    cases lac <;> simp [derLB, lookbehind]
  | .right (_ + 1) _ _ => simp [derLB, lookbehind]

theorem derLB_la (a : α) (l : Lang α) : derLB a (▷ l) ≐ ▷ (derLB a l) := by
  intro w
  rcases w with ⟨_, _ | _, _⟩ | ⟨_ | _, _, _⟩ | ⟨_ | _, _ | _, _ | _⟩ <;> simp [derLB, lookahead, toList]

theorem derLB_matchStep (a : α) (l : Lang α) : derLB a (↑₂ l) ≐ ∅ := by
  intro w
  rcases w with ⟨_, _, _⟩ | ⟨_ | _, _, _⟩ | ⟨_ | _, _ | _, _⟩ <;> simp [derLB, matchStep, empty]

theorem derLB_LAStep (a : α) (l : Lang α) : derLB a (↑₃ l) ≐ ∅ := by
  intro w
  rcases w with ⟨_, _, _⟩ | ⟨_ | _, _, _⟩ | ⟨_ | _, _ | _, _⟩ <;> simp [derLB, laStep, empty]

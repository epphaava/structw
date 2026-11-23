import Thesis.Semantics.Lang.«1_StructuredWords»
import Thesis.Semantics.Lang.«2_Operators»
import Thesis.Semantics.Lang.«3_Derivatives»

namespace derLBLawsHelpers

open StructuredWords
open Operators
open Derivatives

theorem exists_der_middle (a : α) (l : Lang α) (main : NEList α) (la : List α) :
    (∃ n, der a l (.middle n main la)) ↔ ∃ n, l (.middle n (a, toList main) la) := by
  constructor
  · rintro ⟨n, h⟩
    cases n with
    | zero => simp [der] at h
    | succ n => exact ⟨n, h⟩
  · rintro ⟨n, h⟩; exact ⟨n + 1, h⟩

theorem exists_der_right (a : α) (l : Lang α) (la : List α) :
    (∃ n, der a l (.right n 0 la)) ↔ ∃ n, l (.middle n (a, []) la) := by
  constructor
  · rintro ⟨n, h⟩
    cases n with
    | zero => simp [der] at h
    | succ n => exact ⟨n, h⟩
  · rintro ⟨n, h⟩; exact ⟨n + 1, h⟩


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

end derLBLawsHelpers

import Thesis.Semantics.«1_StructuredWords»
import Thesis.Semantics.«2_Operators»
import Thesis.Semantics.«3_Derivatives»

namespace derLBLawsHelpers

open StructuredWords
open Operators


theorem derLB_star_left (a : α) (l base : Lang α) : ∀ (lbcount : Nat) (x : α) (xs main la : List α),
    star_help l base (.left lbcount (a, x :: xs) main la) ↔ star_help (derLB a l) (derLB a base) (.left lbcount.succ (x, xs) main la) := by
  intro lbcount x xs main la
  constructor
  · suffices key : ∀ w, star_help l base w →
        ∀ lbcount x xs main la, w = .left lbcount (a, x :: xs) main la →
          star_help (derLB a l) (derLB a base) (.left lbcount.succ (x, xs) main la) by
      intro h; exact key _ h lbcount x xs main la rfl
    intro _ h
    induction h with
    | inUnit w hunit => intro _ _ _ _ _ hw; subst hw; exact star_help.inUnit _ hunit
    | inConcat w₁ w₂ w hl _ hwc ih =>
      intro lbc x xs main la hw; subst hw
      obtain ⟨pref, suff, hmain, h₁, h₂⟩ := hwc; subst h₁ h₂
      exact star_help.inConcat (.left lbc.succ (x, xs) pref (suff ++ la)) (.left lbc.succ (x, xs ++ pref) suff la) _
        hl (ih lbc x (xs ++ pref) suff la rfl) ⟨pref, suff, hmain, rfl, rfl⟩
  · suffices key : ∀ w, star_help (derLB a l) (derLB a base) w →
        ∀ lbcount x xs main la, w = .left lbcount.succ (x, xs) main la →
          star_help l base (.left lbcount (a, x :: xs) main la) by
      intro h; exact key _ h lbcount x xs main la rfl
    intro _ h
    induction h with
    | inUnit w hunit => intro _ _ _ _ _ hw; subst hw; exact star_help.inUnit _ hunit
    | inConcat w₁ w₂ w hl _ hwc ih =>
      intro lbc x xs main la hw; subst hw
      obtain ⟨pref, suff, hmain, h₁, h₂⟩ := hwc; subst h₁ h₂
      exact star_help.inConcat (.left lbc (a, x :: xs) pref (suff ++ la)) (.left lbc (a, x :: (xs ++ pref)) suff la) _
        hl (ih lbc x (xs ++ pref) suff la rfl) ⟨pref, suff, hmain, rfl, rfl⟩

theorem derLB_star_middle (a : α) (l base : Lang α) : ∀ (lbcount : Nat) (main : NEList α) (la : List α),
    star_help l base (.left lbcount (a, []) (toList main) la) ↔ star_help (derLB a l) (derLB a base) (.middle lbcount.succ 0 main la) := by
  intro lbcount main la
  constructor
  · suffices key : ∀ w, star_help l base w →
        ∀ lbcount (main : NEList α) la, w = .left lbcount (a, []) (toList main) la →
          star_help (derLB a l) (derLB a base) (.middle lbcount.succ 0 main la) by
      intro h; exact key _ h lbcount main la rfl
    intro _ h
    induction h with
    | inUnit w hunit => intro _ _ _ hw; subst hw; exact star_help.inUnit _ hunit
    | inConcat w₁ w₂ w hl hstar hwc ih =>
      intro lbc main la hw; subst hw
      obtain ⟨pref, suff, hmain, h₁, h₂⟩ := hwc; subst h₁ h₂
      cases pref with
      | nil => exact ih lbc main la (by simp [hmain])
      | cons y ys =>
        simp [toList] at hmain; obtain ⟨hy, hys⟩ := hmain
        exact star_help.inConcat (.middle lbc.succ 0 (y, ys) (suff ++ la)) (.left lbc.succ (y, ys) suff la) _
          hl ((derLB_star_left a l base lbc y ys suff la).mp hstar)
          (Or.inl ⟨ys, suff, hys, by simp [hy], by simp [hy]⟩)
  · suffices key : ∀ w, star_help (derLB a l) (derLB a base) w →
        ∀ lbcount (main : NEList α) la, w = .middle lbcount.succ 0 main la →
          star_help l base (.left lbcount (a, []) (toList main) la) by
      intro h; exact key _ h lbcount main la rfl
    intro _ h
    induction h with
    | inUnit w hunit => intro _ _ _ hw; subst hw; exact star_help.inUnit _ hunit
    | inConcat w₁ w₂ w hl hstar hwc ih =>
      intro lbc main la hw; subst hw
      rcases hwc with ⟨pref, suff, hmain, h₁, h₂⟩ | ⟨mc₁, mc₂, hmcount, _, hw₂⟩
      · subst h₁ h₂
        exact star_help.inConcat (.left lbc (a, []) (main.1 :: pref) (suff ++ la))
          (.left lbc (a, main.1 :: pref) suff la) _
          hl ((derLB_star_left a l base lbc main.1 pref suff la).mpr hstar)
          ⟨main.1 :: pref, suff, by simp [toList, hmain], rfl, rfl⟩
      · obtain ⟨rfl, rfl⟩ : mc₁ = 0 ∧ mc₂ = 0 := by omega
        exact ih lbc main la hw₂

theorem derLB_star_right (a : α) (l base : Lang α) : ∀ (lbcount : Nat) (la : List α),
    star_help l base (.left lbcount (a, []) [] la) ↔ star_help (derLB a l) (derLB a base) (.right lbcount.succ 0 0 la) := by
  intro lbcount la
  constructor
  · suffices key : ∀ w, star_help l base w →
        ∀ lbcount la, w = .left lbcount (a, []) [] la →
          star_help (derLB a l) (derLB a base) (.right lbcount.succ 0 0 la) by
      intro h; exact key _ h lbcount la rfl
    intro _ h
    induction h with
    | inUnit w hunit => intro _ _ hw; subst hw; exact star_help.inUnit _ hunit
    | inConcat w₁ w₂ w hl _ hwc ih =>
      intro lbc la hw; subst hw
      obtain ⟨pref, suff, hmain, h₁, h₂⟩ := hwc; subst h₁ h₂
      obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp hmain.symm
      exact star_help.inConcat (.right lbc.succ 0 0 la) (.right lbc.succ 0 0 la) _ hl (ih lbc la rfl) ⟨0, 0, rfl, rfl, rfl⟩
  · suffices key : ∀ w, star_help (derLB a l) (derLB a base) w →
        ∀ lbcount la, w = .right lbcount.succ 0 0 la →
          star_help l base (.left lbcount (a, []) [] la) by
      intro h; exact key _ h lbcount la rfl
    intro _ h
    induction h with
    | inUnit w hunit => intro _ _ hw; subst hw; exact star_help.inUnit _ hunit
    | inConcat w₁ w₂ w hl _ hwc ih =>
      intro lbc la hw; subst hw
      obtain ⟨mc₁, mc₂, hmcount, h₁, h₂⟩ := hwc
      obtain ⟨rfl, rfl⟩ : mc₁ = 0 ∧ mc₂ = 0 := by omega
      subst h₁
      exact star_help.inConcat (.left lbc (a, []) [] la) (.left lbc (a, []) [] la) _ hl (ih lbc la h₂) ⟨[], [], rfl, rfl, rfl⟩


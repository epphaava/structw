import Thesis.Semantics.«1_StructuredWords»
import Thesis.Semantics.«2_Operators»
import Thesis.Semantics.«3_Derivatives»

namespace derLALawsHelpers

open StructuredWords
open Operators



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

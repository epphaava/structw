import Thesis.Semantics.Lang.«1_StructuredWords»
import Thesis.Semantics.Lang.«2_Operators»
import Thesis.Semantics.Lang.«3_Derivatives»

namespace derLALawsHelpers

open StructuredWords
open Operators
open Derivatives


theorem derLA_star_right (a : α) (l base : Lang α) : ∀ (mc lac : Nat) (la : List α),
    star_help l base (.right mc lac (a :: la)) ↔ star_help (derLA a l) (derLA a base) (.right mc (lac + 1) la) := by
  intro mc lac la
  constructor
  · suffices key : ∀ w, star_help l base w → ∀ mc lac la, w = .right mc lac (a :: la) →
        star_help (derLA a l) (derLA a base) (.right mc (lac + 1) la) from fun h => key _ h mc lac la rfl
    intro _ h
    induction h with
    | inUnit w hu => intro _ _ _ hw; subst hw; exact star_help.inUnit _ hu
    | inConcat w₁ w₂ w hl _ hwc ih =>
      intro mc lac la rfl; obtain ⟨mc₁, mc₂, rfl, rfl, rfl⟩ := hwc;
      exact star_help.inConcat (.right mc₁ (mc₂ + (lac + 1)) la) (.right mc₂ (lac + 1) la) _
        hl (ih mc₂ lac la rfl) ⟨mc₁, mc₂, rfl, rfl, rfl⟩
  · suffices key : ∀ w, star_help (derLA a l) (derLA a base) w → ∀ mc lac la, w = .right mc (lac + 1) la →
        star_help l base (.right mc lac (a :: la)) from fun h => key _ h mc lac la rfl
    intro _ h
    induction h with
    | inUnit w hu => intro _ _ _ hw; subst hw; exact star_help.inUnit _ hu
    | inConcat w₁ w₂ w hl _ hwc ih =>
      intro mc lac la rfl; obtain ⟨mc₁, mc₂, rfl, rfl, rfl⟩ := hwc;
      exact star_help.inConcat (.right mc₁ (mc₂ + lac) (a :: la)) (.right mc₂ lac (a :: la)) _
        hl (ih mc₂ lac la rfl) ⟨mc₁, mc₂, rfl, rfl, rfl⟩

end derLALawsHelpers

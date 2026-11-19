import Thesis.Semantics.«1_StructuredWords»
import Thesis.Semantics.«2_Operators»
import Thesis.Semantics.«3_Derivatives»
import Thesis.Semantics.«8_AlgebraicLaws»
import Thesis.Semantics.«6_LookaheadDerivativeLaws»
import Thesis.Semantics.«5_LookbehindDerivativeLaws»


namespace DerLawsHelpers

open StructuredWords
open Operators
open derLBLaws
open derLALaws



theorem der_mono (a : α) {k l : Lang α} (h : ∀ w, k w → l w) : ∀ w, der a k w → der a l w := by
  intro w hw
  match w with
  | .left _ _ _ _ => simp [der] at hw
  | .middle _ mcount _ _ => cases mcount <;> first | exact h _ hw | simp [der] at hw
  | .right _ mcount lacount _ => cases mcount <;> cases lacount <;> first | exact h _ hw | simp [der] at hw

theorem derLA_mono (a : α) {k l : Lang α} (h : ∀ w, k w → l w) : ∀ w, derLA a k w → derLA a l w := by
  intro w hw
  match w with
  | .left _ _ _ _ => simp [derLA] at hw
  | .middle _ _ _ _ => simp [derLA] at hw
  | .right _ _ lacount _ => cases lacount <;> first | exact h _ hw | simp [derLA] at hw

theorem derLB_mono (a : α) {k l : Lang α} (h : ∀ w, k w → l w) : ∀ w, derLB a k w → derLB a l w := by
  intro w hw
  match w with
  | .left lbc _ _ _ => cases lbc <;> first | exact h _ hw | simp [derLB] at hw
  | .middle lbc mcount _ _ => cases lbc <;> cases mcount <;> first | exact h _ hw | simp [derLB] at hw
  | .right lbc mcount lacount _ => cases lbc <;> cases mcount <;> cases lacount <;> first | exact h _ hw | simp [derLB] at hw

theorem der_helper (a : α) (k : Lang α) : ∀ w, der a k w → ∃ w', k w' ∧ ∀ l : Lang α, l w' → der a l w := by
  intro w hw
  match w with
  | .left _ _ _ _ => simp [der] at hw
  | .middle _ mcount _ _ => cases mcount <;> first | exact ⟨_, hw, fun _ h => h⟩ | simp [der] at hw
  | .right _ mcount lacount _ => cases mcount <;> cases lacount <;> first | exact ⟨_, hw, fun _ h => h⟩ | simp [der] at hw

theorem concat_mono {k k' l l' : Lang α} (hk : ∀ v, k v → k' v) (hl : ∀ v, l v → l' v) : ∀ w, (k • l) w → (k' • l') w := by
  intro _ ⟨x, y, hx, hy, hxy⟩; exact ⟨x, y, hk x hx, hl y hy, hxy⟩

theorem star_unit_concat (base l : Lang α) : star l base ≐ star l I • base := by
  intro w
  constructor
  · intro h
    induction h with
    | inUnit w hb => exact concat_mono (fun v hv => star_help.inUnit v hv) (fun _ h => h) w ((AlgebraicLaws.concat_left_identity base w).mpr hb)
    | inConcat u v w hu _ huv ih =>
      have h1 : (l • (star l I • base)) w := ⟨u, v, hu, ih, huv⟩
      exact concat_mono (fun x ⟨p, q, hp, hq, hpq⟩ => star_help.inConcat p q x hp hq hpq) (fun _ h => h) w ((AlgebraicLaws.concat_assoc l (star l I) base w).mp h1)
  · intro ⟨u, v, hu, hv, huv⟩
    suffices key : ∀ u, star l I u → ∀ w, ((· = u) • base) w → star l base w from
      key u hu w ⟨u, v, rfl, hv, huv⟩
    intro u hu
    induction hu with
    | inUnit u hI =>
      intro w hw
      exact star_help.inUnit w ((AlgebraicLaws.concat_left_identity base w).mp (concat_mono (fun x hx => hx ▸ hI) (fun _ h => h) w hw))
    | inConcat u₁ u₂ u hu₁ _ hwc ih =>
      intro w hw
      have h1 : (((· = u₁) • (· = u₂)) • base) w := concat_mono (fun x hx => hx ▸ ⟨u₁, u₂, rfl, rfl, hwc⟩) (fun _ h => h) w hw
      obtain ⟨p, q, rfl, hq, hpq⟩ := (AlgebraicLaws.concat_assoc _ _ _ w).mpr h1
      exact star_help.inConcat p q w hu₁ (ih q hq) hpq

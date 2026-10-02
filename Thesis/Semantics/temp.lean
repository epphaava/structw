import Thesis.Semantics.StructuredWords
import Thesis.Semantics.Operators
import Thesis.Semantics.Derivatives


open StructuredWords
open Operators

theorem derLA_star (a : α) (l : Lang α) : derLA a (l*) ≐ ▹ₗ (derLA a l)* := by
  intro w
  match w with
  | .left lb main la =>
    simp [derLA, LAStep];
  | .middle mcount main la =>
    simp [derLA, LAStep]
  | .right mcount lacount la =>
    cases lacount with
    | zero => simp [derLA, LAStep]
    | succ lacount =>
      constructor
      · intro h
        simp only [derLA] at h
        cases h with
        | inUnit _ hu => left; cases mcount <;> simp [unit] at hu ⊢
        | inConcat w₁ w₂ w hl hs hwc =>
          obtain ⟨mc₁, mc₂, hmcount, rfl, rfl⟩ := hwc;
          simp [LAStep, star]
          have := star_help.inConcat (.right mc₁ (mc₂ + lacount) (a :: la)) (.right mc₂ lacount (a :: la)) (.right mcount lacount la) hl hs
          have g :  wc (Word.right mc₁ (mc₂ + lacount) (a :: la)) (Word.right mc₂ lacount (a :: la)) (Word.right mcount lacount la) := by
            refine ⟨mc₁, mc₂, hmcount, ?_, ?_⟩

          --right
          --exact ⟨.right mc₁ (mc₂ + (lacount + 1)) la, .right mc₂ (lacount + 1) la, hl, hs, mc₁, mc₂, rfl, rfl, rfl⟩
      · rintro (hu | ⟨x, y, hx, hy, mc₁, mc₂, rfl, rfl, rfl⟩)
        · exact star_help.inUnit _ (by cases mcount <;> simp [LAStep, unit] at hu ⊢)
        · exact star_help.inConcat (.right mc₁ (mc₂ + lacount) (a :: la)) (.right mc₂ lacount (a :: la)) _ hx hy ⟨mc₁, mc₂, rfl, rfl, rfl⟩

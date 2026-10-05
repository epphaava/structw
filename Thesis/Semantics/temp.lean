import Thesis.Semantics.StructuredWords
import Thesis.Semantics.Operators
import Thesis.Semantics.Derivatives


open StructuredWords
open Operators


theorem derLA_star (a : α) (l : Lang α) : derLA a (l*) ≐ ▹ₗ I  := by
  intro w
  match w with
  | .left lb main la => simp [derLA, LAStep];
  | .middle mcount main la =>
    simp [derLA, LAStep]
  | .right mcount lacount la =>
    cases lacount with
    | zero => simp [derLA, LAStep]
    | succ lacount =>
      cases mcount with
      | zero =>
        simp [derLA, LAStep, unit]
        exact star_help.inUnit (l := l) (.right 0 lacount (a :: la)) (by simp [unit])
      | succ mcount =>
        constructor
        · intro h
          cases h with
          | inUnit _ hu => simp [unit] at hu
          | inConcat w₁ w₂ _ hl hs hwc =>
            obtain ⟨mc₁, mc₂, hmcount, _, _⟩ := hwc;
            simp [LAStep, unit]
        · simp [derLA, LAStep, top]
          have := star_help.inConcat (l := l) (.right mcount lacount (a :: la)) (.right mcount lacount la) (.right (mcount + 1) lacount (a :: la))

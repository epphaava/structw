import Thesis.Syntax.«1_Expressions»
import Thesis.Syntax.«2_Derivatives»
import Thesis.Syntax.Helpers.«3_DerivativeCorrectness»
import Thesis.Syntax.«4_Nullability»
import Thesis.Syntax.«3_DerivativeCorrectness»


namespace AlgorithmHelpers

open SRegex
open StructuredWords
open kStructuredWords
open kOperators
open kNullabilityLaws
open DerCorrectHelpers
open SRegexDerivatives
open Nullability
open NullabilityHelpers
open DerCorrect


theorem regexToSRegex_wf (r : Regex α) : WF (regexToSRegex r) 0 := by
  induction r with
  | empty => trivial
  | unit | top | symbol _ => simp [regexToSRegex, WF, Steps.stepsSum, Steps.zeroSteps]
  | plus _ _ ih₁ ih₂ | intersection _ _ ih₁ ih₂ | complement _ _ ih₁ ih₂
  | mult _ _ ih₁ ih₂ | star _ _ ih₁ ih₂ => exact ⟨ih₁, ih₂⟩
  | lb _ ih | la _ ih => exact ih

theorem wf_findAllMatches [DecidableEq α] (r : Regex α) (w : List α) : WF (xD w (regexToSRegex r)) w.length := by
  have := wf_xD w _ 0 (regexToSRegex_wf r)
  rwa [Nat.zero_add] at this

def wordToSWord (w : List α) (s : Steps) : Word α :=
  let k := w.length - (s.m + s.la)
  mk_word (w.take k) ((w.drop k).take s.m) (w.drop (k + s.m))

end AlgorithmHelpers

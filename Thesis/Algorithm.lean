import Thesis.Syntax.«1_Expressions»
import Thesis.Syntax.«2_Derivatives»
import Thesis.Syntax.Helpers.«3_DerivativeCorrectness»
import Thesis.Syntax.«4_Nullability»
import Thesis.Syntax.«3_DerivativeCorrectness»
import Thesis.AlgorithmHelpers


namespace Algorithm

open SRegex
open StructuredWords
open kStructuredWords
open kOperators
open NullabilityLaws
open DerCorrectHelpers
open SRegexDerivatives
open Nullability
open NullabilityHelpers
open DerCorrect
open AlgorithmHelpers

-- Definition 5.1.2 (Matching algorithm).
def findAllMatches [DecidableEq α] (r : Regex α) (w : List α) : List Steps :=
  N (xD w (regexToSRegex r))


theorem algorithm_correctness [DecidableEq α] (r : Regex α) (w : List α) (s : Steps) :
    s ∈ findAllMatches r w ↔ nullable (xder w (sem (regexToSRegex r) 0)) s.m s.la := by
  have hwf := wf_findAllMatches r w
  have hx : ∀ u, xder w (sem (regexToSRegex r) 0) u ↔ sem (xD w (regexToSRegex r)) w.length u := by
    intro u; exact (xder_correct w (regexToSRegex r) 0 u).trans (by rw [Nat.zero_add])
  constructor
  · intro h
    have hs := N_sum _ _ hwf s h
    exact (hx _).mpr ((N_correct _ _ hwf s hs).mpr h)
  · intro hn
    have hb := (xder w (sem (regexToSRegex r) 0)).2 _ hn
    have hs : s.stepsSum ≤ w.length := by simp [word_steps, Steps.stepsSum] at hb ⊢; omega
    exact (N_correct _ _ hwf s hs).mp ((hx _).mp hn)

end Algorithm

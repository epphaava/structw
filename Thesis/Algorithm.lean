import Thesis.Syntax.«1_Expressions»
import Thesis.Syntax.«2_Derivatives»
import Thesis.Syntax.Helpers.«3_DerivativeCorrectness»
import Thesis.Syntax.«4_Nullability»
import Thesis.Syntax.«3_DerivativeCorrectness»
import Thesis.AlgorithmHelpers
import Thesis.Semantics.kLang.«4_DerivativeAcceptance»


namespace Algorithm

open SRegex
open StructuredWords
open kStructuredWords
open kOperators
open kNullabilityLaws
open kDerivatives
open DerCorrectHelpers
open SRegexDerivatives
open Nullability
open NullabilityHelpers
open DerCorrect
open AlgorithmHelpers
open kDerAccept
open Steps

-- Definition 5.1.2 (Matching algorithm).
def findAllMatches [DecidableEq α] (r : Regex α) (w : List α) : List Steps :=
  N (xD w (regexToSRegex r))


theorem algorithm_correctness [DecidableEq α] (r : Regex α) (w : List α) (s : Steps) :
    s ∈ findAllMatches r w ↔ nullable (xder w (sem (regexToSRegex r) 0)) s.m s.la := by
  have hwf := wf_findAllMatches r w
  have hx : ∀ u, xder w (sem (regexToSRegex r) 0) u ↔ sem (xD w (regexToSRegex r)) w.length u := by
    intro u; exact (xder_correct w (regexToSRegex r) 0 u).trans (by rw [Nat.zero_add])
  constructor
  · intro h; exact (hx _).mpr ((N_correct _ _ hwf s).mpr h)
  · intro hn; exact (N_correct _ _ hwf s).mp ((hx _).mp hn)

theorem algorithm_correctness' [DecidableEq α] (r : Regex α) (w : List α) (s : Steps) :
    s ∈ findAllMatches r w ↔ s.stepsSum ≤ w.length ∧ (sem (regexToSRegex r) 0) (wordToSWord w s) := by
  refine (algorithm_correctness r w s).trans ?_
  refine (xder_nullable_iff (sem (regexToSRegex r) 0) w s.m s.la).trans ?_
  have hmk : ∀ a b c : List α, word_to_list (mk_word a b c) = a ++ b ++ c ∧ final_counts (mk_word a b c) = (b.length, c.length) := by
    intro a b c; rcases a with _ | ⟨x, xs⟩ <;> rcases b with _ | ⟨y, ys⟩ <;> simp [mk_word, mk_mcount_word, word_to_list, Word.final_counts, toList]
  obtain ⟨m, la⟩ := s
  constructor
  · intro ⟨u, ⟨hw, hc⟩, hu⟩
    have hst := (sem (regexToSRegex r) 0).2 u hu
    obtain ⟨a, b, c, rfl⟩ : ∃ a b c, u = mk_word a b c := by
      rcases u with ⟨⟨x, xs⟩, main, la'⟩ | ⟨_ | mc, ⟨y, ys⟩, la'⟩ | ⟨_ | mc, _ | lac, la'⟩ <;>
        simp [word_steps] at hst
      · exact ⟨x :: xs, main, la', rfl⟩
      · exact ⟨[], y :: ys, la', rfl⟩
      · exact ⟨[], [], la', rfl⟩
    obtain ⟨h1, h2⟩ := hmk a b c
    rw [h1] at hw; rw [h2] at hc; simp at hc
    obtain ⟨rfl, rfl⟩ := hc; subst hw
    exact ⟨by simp [stepsSum], by simp [wordToSWord]; exact hu⟩
  · intro ⟨hb, h⟩
    refine ⟨_, ?_, h⟩
    simp [stepsSum] at hb
    simp [wordToSWord]
    generalize hk : HSub.hSub w.length (HAdd.hAdd m la) = k
    obtain ⟨h1, h2⟩ := hmk (w.take k) ((w.drop k).take m) (w.drop (HAdd.hAdd k m))
    exact ⟨by rw [h1]; simp [← List.drop_drop], by rw [h2]; simp; omega⟩


end Algorithm

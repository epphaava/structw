import Thesis.Syntax.«1_Expressions»
import Thesis.Syntax.«2_Derivatives»
import Thesis.Syntax.«4_DerivativeCorrectHelpers»
import Thesis.Syntax.«5_Nullability»
import Thesis.Syntax.«3_DerivativeCorrectness»

namespace Algorithm

open SRegex
open StructuredWords
open Operators
open NullabilityLaws
open DerCorrectHelp
open SRegexDerivatives
open SRegexDerivatives
open Nullability
open DerCorrect
open SRegexDerivatives

-- Definition 5.1.2 (Matching algorithm).
def findAllMatches [DecidableEq α] (r : Regex α) (w : List α) : List Steps := N (xD w (regexToSRegex r))



theorem ssEqLen_map {ss : List Steps} {n : Nat} (f : Steps → Steps)
    (hf : ∀ s, Steps.stepsSum s = n → Steps.stepsSum (f s) = n + 1)
    (h : ∀ s ∈ ss, Steps.stepsSum s = n) : ∀ s ∈ ss.map f, Steps.stepsSum s = n + 1 := by
  intro s hs
  obtain ⟨s', hs', rfl⟩ := List.mem_map.mp hs
  exact hf s' (h s' hs')

theorem ssEqLen_filter {ss : List Steps} {n : Nat} (p : Steps → Bool) (h : ∀ s ∈ ss, Steps.stepsSum s = n) : ∀ s ∈ ss.filter p, Steps.stepsSum s = n := by
  intro s hs
  exact h s (List.mem_filter.mp hs).1

theorem lb_succ (s : Steps) (n : Nat) (h : Steps.stepsSum s = n) :
    Steps.stepsSum (Steps.lbStepHelp s) = n + 1 := by
  simp [Steps.stepsSum, Steps.lbStepHelp] at *; omega
theorem m_succ (s : Steps) (n : Nat) (h : Steps.stepsSum s = n) :
    Steps.stepsSum (Steps.mStepHelp s) = n + 1 := by
  simp [Steps.stepsSum, Steps.mStepHelp] at *; omega
theorem la_succ (s : Steps) (n : Nat) (h : Steps.stepsSum s = n) :
    Steps.stepsSum (Steps.laStepHelp s) = n + 1 := by
  simp [Steps.stepsSum, Steps.laStepHelp] at *; omega

theorem ssEqLen_lbStep {ss : List Steps} {n} (h : ∀ s ∈ ss, Steps.stepsSum s = n) : ∀ s ∈ Steps.lbStep ss, Steps.stepsSum s = n + 1 := ssEqLen_map _ (lb_succ · n) h

theorem ssEqLen_mStep {ss : List Steps} {n} (h : ∀ s ∈ ss, Steps.stepsSum s = n) : ∀ s ∈ Steps.mStep ss, Steps.stepsSum s = n + 1 := ssEqLen_map _ (m_succ · n) h

theorem ssEqLen_laStep {ss : List Steps} {n} (h : ∀ s ∈ ss, Steps.stepsSum s = n) : ∀ s ∈ Steps.laStep ss, Steps.stepsSum s = n + 1 := ssEqLen_map _ (la_succ · n) h


mutual
theorem ssEqLen_D [DecidableEq α] (a : α) : (r : SRegex α) → (n : Nat) → ssEqLen r n → ssEqLen (D a r) (n + 1)
  | .empty, _, _ | .unit _, _, _ | .lb _, _, _ | .la _, _, _ => trivial
  | .top _, _, h => ⟨ssEqLen_mStep (ssEqLen_filter _ h), ssEqLen_laStep (ssEqLen_filter _ h)⟩
  | .symbol _ _, _, h => by
    simp [D]; split
    · exact ⟨ssEqLen_mStep (ssEqLen_filter _ h), ssEqLen_laStep (ssEqLen_filter _ h)⟩
    · trivial
  | .plus r₁ r₂, n, h | .intersection r₁ r₂, n, h | .complement r₁ r₂, n, h => ⟨ssEqLen_D a r₁ n h.1, ssEqLen_D a r₂ n h.2⟩
  | .mult r₁ r₂, n, h => ⟨⟨ssEqLen_D a r₁ n h.1, ssEqLen_DLB a r₂ n h.2⟩, ⟨ssEqLen_DLA a r₁ n h.1, ssEqLen_D a r₂ n h.2⟩⟩
  | .star r b, n, h => ⟨ssEqLen_DLA a r n h.1, ssEqLen_D a b n h.2, ssEqLen_D a r n h.1, ssEqLen_DLB a r n h.1, ssEqLen_DLB a b n h.2⟩

theorem ssEqLen_DLB [DecidableEq α] (a : α) : (r : SRegex α) → (n : Nat) → ssEqLen r n → ssEqLen (DLB a r) (n + 1)
  | .empty, _, _ => trivial
  | .unit _, _, h => ⟨ssEqLen_lbStep (ssEqLen_filter _ h), ssEqLen_laStep (ssEqLen_filter _ h)⟩
  | .top _, _, h => ⟨ssEqLen_lbStep (ssEqLen_filter _ h), ssEqLen_mStep (ssEqLen_filter _ h), ssEqLen_laStep (ssEqLen_filter _ h)⟩
  | .symbol _ _, _, h => ⟨ssEqLen_lbStep (ssEqLen_filter _ h), ssEqLen_mStep (ssEqLen_filter _ h), ssEqLen_laStep (ssEqLen_filter _ h)⟩
  | .plus r₁ r₂, n, h | .intersection r₁ r₂, n, h | .complement r₁ r₂, n, h
  | .mult r₁ r₂, n, h | .star r₁ r₂, n, h => ⟨ssEqLen_DLB a r₁ n h.1, ssEqLen_DLB a r₂ n h.2⟩
  | .lb r, n, h => ssEqLen_D a r n h
  | .la r, n, h => ssEqLen_DLB a r n h

theorem ssEqLen_DLA [DecidableEq α] (a : α) : (r : SRegex α) → (n : Nat) → ssEqLen r n → ssEqLen (DLA a r) (n + 1)
  | .empty, _, _ | .symbol _ _, _, _ => trivial
  | .unit _, _, h | .top _, _, h => ssEqLen_laStep h
  | .plus r₁ r₂, n, h | .intersection r₁ r₂, n, h | .complement r₁ r₂, n, h
  | .mult r₁ r₂, n, h | .star r₁ r₂, n, h =>
    ⟨ssEqLen_DLA a r₁ n h.1, ssEqLen_DLA a r₂ n h.2⟩
  | .lb r, n, h => ssEqLen_DLA a r n h
  | .la r, n, h => ssEqLen_D a r n h
end

theorem ssEqLen_xD [DecidableEq α] (w : List α) (r : SRegex α) (n : Nat) (h : ssEqLen r n) :
    ssEqLen (xD w r) (n + w.length) := by
  induction w generalizing r n with
  | nil => exact h
  | cons a w ih =>
    have := ih (.plus (.plus (DLB a r) (D a r)) (DLA a r)) (n + 1) ⟨⟨ssEqLen_DLB a r n h, ssEqLen_D a r n h⟩, ssEqLen_DLA a r n h⟩
    rw [Nat.add_right_comm] at this
    exact this

theorem ssEqLen_regexToSRegex : (r : Regex α) → ssEqLen (regexToSRegex r) 0
  | .empty => trivial
  | .unit | .top | .symbol _ => by simp [regexToSRegex, ssEqLen, Steps.stepsSum, Steps.zeroSteps]
  | .plus r₁ r₂ | .intersection r₁ r₂ | .complement r₁ r₂ | .mult r₁ r₂ | .star r₁ r₂ => ⟨ssEqLen_regexToSRegex r₁, ssEqLen_regexToSRegex r₂⟩
  | .lb r | .la r => ssEqLen_regexToSRegex r

theorem ssEqLen_findAllMatches [DecidableEq α] (r : Regex α) (w : List α) :
    ssEqLen (SRegexDerivatives.xD w (regexToSRegex r)) w.length := by
  have := ssEqLen_xD w _ 0 (ssEqLen_regexToSRegex r)
  simp [Nat.zero_add] at this; exact this

theorem algorithm_correctness [DecidableEq α] (r : Regex α) (w : List α) (s : Steps) :
  s ∈ findAllMatches r w ↔ s.stepsSum = w.length ∧ nullable (xder w (sem (regexToSRegex r))) s.lb s.m s.la  := by
  constructor
  · intro h
    have hs := N_sum _ _ (ssEqLen_findAllMatches r w) s h
    exact ⟨hs, (xder_correct w _ _).mpr ((N_correct _ _ (ssEqLen_findAllMatches r w) s hs).mpr h)⟩
  · rintro ⟨hs, hn⟩
    exact (N_correct _ _ (ssEqLen_findAllMatches r w) s hs).mp ((xder_correct w _ _).mp hn)

end Algorithm

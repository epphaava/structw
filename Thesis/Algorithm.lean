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
open Nullability
open DerCorrect

-- Definition 5.1.2 (Matching algorithm).

def findAllMatches [DecidableEq α] (r : Regex α) (w : List α) : List Steps :=
  N (xD w (regexToSRegex r)) w.length


theorem ssLe_filter {ss : List Steps} {n : Nat} (p : Steps → Bool) (h : ∀ s ∈ ss, s.stepsSum ≤ n) :
    ∀ s ∈ ss.filter p, s.stepsSum ≤ n :=
  fun s hs => h s (List.mem_filter.mp hs).1

theorem ssLe_succ {ss : List Steps} {n : Nat} (h : ∀ s ∈ ss, s.stepsSum ≤ n) :
    ∀ s ∈ ss, s.stepsSum ≤ n + 1 :=
  fun s hs => Nat.le_succ_of_le (h s hs)

theorem ssLe_mStep {ss : List Steps} {n : Nat} (h : ∀ s ∈ ss, s.stepsSum ≤ n) :
    ∀ s ∈ Steps.mStep ss, s.stepsSum ≤ n + 1 := by
  intro s hs
  obtain ⟨s', hs', rfl⟩ := List.mem_map.mp hs
  have := h s' hs'
  simp only [Steps.mStepHelp, Steps.stepsSum, Nat.add_eq] at *; omega

theorem ssLe_laStep {ss : List Steps} {n : Nat} (h : ∀ s ∈ ss, s.stepsSum ≤ n) :
    ∀ s ∈ Steps.laStep ss, s.stepsSum ≤ n + 1 := by
  intro s hs
  obtain ⟨s', hs', rfl⟩ := List.mem_map.mp hs
  have := h s' hs'
  simp only [Steps.laStepHelp, Steps.stepsSum, Nat.add_eq] at *; omega

mutual
theorem ssLe_D [DecidableEq α] (a : α) : (r : SRegex α) → (n : Nat) → ssLe r n → ssLe (D a r) (n + 1)
  | .empty, _, _ | .unit _, _, _ | .lb _, _, _ | .la _, _, _ => trivial
  | .top _, _, h => ⟨ssLe_mStep (ssLe_filter _ h), ssLe_laStep (ssLe_filter _ h)⟩
  | .symbol _ _, _, h => by
    simp only [D]; split
    · exact ⟨ssLe_mStep (ssLe_filter _ h), ssLe_laStep (ssLe_filter _ h)⟩
    · trivial
  | .plus r₁ r₂, n, h | .intersection r₁ r₂, n, h | .complement r₁ r₂, n, h =>
    ⟨ssLe_D a r₁ n h.1, ssLe_D a r₂ n h.2⟩
  | .mult r₁ r₂, n, h => ⟨⟨ssLe_D a r₁ n h.1, ssLe_DLB a r₂ n h.2⟩, ⟨ssLe_DLA a r₁ n h.1, ssLe_D a r₂ n h.2⟩⟩
  | .star r b, n, h =>
    ⟨ssLe_DLA a r n h.1, ssLe_D a b n h.2, ssLe_D a r n h.1, ssLe_DLB a r n h.1, ssLe_DLB a b n h.2⟩

theorem ssLe_DLB [DecidableEq α] (a : α) : (r : SRegex α) → (n : Nat) → ssLe r n → ssLe (DLB a r) (n + 1)
  | .empty, _, _ => trivial
  | .unit _, _, h => ⟨ssLe_succ (ssLe_filter _ h), ssLe_laStep (ssLe_filter _ h)⟩
  | .top _, _, h | .symbol _ _, _, h =>
    ⟨ssLe_succ (ssLe_filter _ h), ssLe_mStep (ssLe_filter _ h), ssLe_laStep (ssLe_filter _ h)⟩
  | .plus r₁ r₂, n, h | .intersection r₁ r₂, n, h | .complement r₁ r₂, n, h
  | .mult r₁ r₂, n, h | .star r₁ r₂, n, h => ⟨ssLe_DLB a r₁ n h.1, ssLe_DLB a r₂ n h.2⟩
  | .lb r, n, h => ssLe_D a r n h
  | .la r, n, h => ssLe_DLB a r n h

theorem ssLe_DLA [DecidableEq α] (a : α) : (r : SRegex α) → (n : Nat) → ssLe r n → ssLe (DLA a r) (n + 1)
  | .empty, _, _ | .symbol _ _, _, _ => trivial
  | .unit _, _, h | .top _, _, h => ssLe_laStep h
  | .plus r₁ r₂, n, h | .intersection r₁ r₂, n, h | .complement r₁ r₂, n, h
  | .mult r₁ r₂, n, h | .star r₁ r₂, n, h => ⟨ssLe_DLA a r₁ n h.1, ssLe_DLA a r₂ n h.2⟩
  | .lb r, n, h => ssLe_DLA a r n h
  | .la r, n, h => ssLe_D a r n h
end

theorem ssLe_xD [DecidableEq α] (w : List α) (r : SRegex α) (n : Nat) (h : ssLe r n) :
    ssLe (xD w r) (n + w.length) := by
  induction w generalizing r n with
  | nil => exact h
  | cons a w ih =>
    have := ih (.plus (.plus (DLB a r) (D a r)) (DLA a r)) (n + 1) ⟨⟨ssLe_DLB a r n h, ssLe_D a r n h⟩, ssLe_DLA a r n h⟩
    rw [Nat.add_right_comm] at this
    exact this

theorem ssLe_regexToSRegex : (r : Regex α) → ssLe (regexToSRegex r) 0
  | .empty => trivial
  | .unit | .top | .symbol _ => by simp [regexToSRegex, ssLe, Steps.stepsSum, Steps.zeroSteps]
  | .plus r₁ r₂ | .intersection r₁ r₂ | .complement r₁ r₂ | .mult r₁ r₂ | .star r₁ r₂ =>
    ⟨ssLe_regexToSRegex r₁, ssLe_regexToSRegex r₂⟩
  | .lb r | .la r => ssLe_regexToSRegex r

theorem ssLe_findAllMatches [DecidableEq α] (r : Regex α) (w : List α) :
    ssLe (xD w (regexToSRegex r)) w.length := by
  have := ssLe_xD w _ 0 (ssLe_regexToSRegex r)
  rwa [Nat.zero_add] at this


/-- Theorem 5.1.1 (Algorithm correctness): `findAllMatches` returns exactly the nullable
`(match, lookahead)` pairs of `r` on `w` whose lookbehind `w.length - (m + la)` is not negative. -/
theorem algorithm_correctness [DecidableEq α] (r : Regex α) (w : List α) (s : Steps) :
    s ∈ findAllMatches r w ↔
      s.stepsSum ≤ w.length ∧
        nullable (xder w (sem (regexToSRegex r) 0)) (w.length - s.stepsSum) s.m s.la := by
  have hwf := ssLe_findAllMatches r w
  have hx : ∀ u, xder w (sem (regexToSRegex r) 0) u ↔ sem (xD w (regexToSRegex r)) w.length u := by
    intro u; have := xder_correct w (regexToSRegex r) 0 u; rwa [Nat.zero_add] at this
  constructor
  · intro h
    have hs := N_sum _ _ hwf s h
    exact ⟨hs, (hx _).mpr ((N_correct _ _ hwf s hs).mpr h)⟩
  · rintro ⟨hs, hn⟩
    exact (N_correct _ _ hwf s hs).mp ((hx _).mp hn)

end Algorithm

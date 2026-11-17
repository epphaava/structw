import Thesis.Syntax.«1_Expressions»
import Thesis.Syntax.«2_Derivatives»
import Thesis.Syntax.Helpers.«4_DerivativeCorrectness»
import Thesis.Syntax.«5_Nullability»
import Thesis.Syntax.«3_DerivativeCorrectness»


namespace AlgorithmHelpers

open SRegex
open StructuredWords
open Operators
open NullabilityLaws
open DerCorrectHelpers
open SRegexDerivatives
open Nullability
open NullabilityHelpers
open DerCorrect




theorem all_filter {ss : List Steps} {P : Steps → Prop} (p : Steps → Bool) (h : ∀ s ∈ ss, P s) :
    ∀ s ∈ ss.filter p, P s :=
  fun s hs => h s (List.mem_filter.mp hs).1

theorem le_succ_all {ss : List Steps} {n : Nat} (h : ∀ s ∈ ss, s.stepsSum ≤ n) :
    ∀ s ∈ ss, s.stepsSum ≤ n + 1 :=
  fun s hs => Nat.le_succ_of_le (h s hs)

theorem le_mStep {ss : List Steps} {n : Nat} (h : ∀ s ∈ ss, s.stepsSum ≤ n) :
    ∀ s ∈ Steps.mStep ss, s.stepsSum ≤ n + 1 := by
  intro s hs
  obtain ⟨s', hs', rfl⟩ := List.mem_map.mp hs
  have := h s' hs'
  simp only [Steps.mStepHelp, Steps.stepsSum, Nat.add_eq] at *; omega

theorem le_laStep {ss : List Steps} {n : Nat} (h : ∀ s ∈ ss, s.stepsSum ≤ n) :
    ∀ s ∈ Steps.laStep ss, s.stepsSum ≤ n + 1 := by
  intro s hs
  obtain ⟨s', hs', rfl⟩ := List.mem_map.mp hs
  have := h s' hs'
  simp only [Steps.laStepHelp, Steps.stepsSum, Nat.add_eq] at *; omega

theorem eq_mStep {ss : List Steps} {n : Nat} (h : ∀ s ∈ ss, s.stepsSum = n) :
    ∀ s ∈ Steps.mStep ss, s.stepsSum = n + 1 := by
  intro s hs
  obtain ⟨s', hs', rfl⟩ := List.mem_map.mp hs
  have := h s' hs'
  simp only [Steps.mStepHelp, Steps.stepsSum, Nat.add_eq] at *; omega

theorem eq_laStep {ss : List Steps} {n : Nat} (h : ∀ s ∈ ss, s.stepsSum = n) :
    ∀ s ∈ Steps.laStep ss, s.stepsSum = n + 1 := by
  intro s hs
  obtain ⟨s', hs', rfl⟩ := List.mem_map.mp hs
  have := h s' hs'
  simp only [Steps.laStepHelp, Steps.stepsSum, Nat.add_eq] at *; omega

theorem laOnly_laStep {ss : List Steps} {n : Nat} (h : ∀ s ∈ ss, s.m = 0 ∧ s.la = n) :
    ∀ s ∈ Steps.laStep ss, s.m = 0 ∧ s.la = n + 1 := by
  intro s hs
  obtain ⟨s', hs', rfl⟩ := List.mem_map.mp hs
  have := h s' hs'
  simp only [Steps.laStepHelp]; omega



mutual
theorem full_D [DecidableEq α] (a : α) (r : SRegex α) (n : Nat) (h: Full r n) : Full (D a r) (n + 1) := by
  match r, n, h  with
  | .empty, _, _ | .unit _, _, _ | .lb _, _, _ | .la _, _, _ => trivial
  | .top _, _, h => exact ⟨eq_mStep (all_filter _ h), eq_laStep (all_filter _ h)⟩
  | .symbol _ _, _, h =>
    simp only [D]; split
    · exact ⟨eq_mStep (all_filter _ h), eq_laStep (all_filter _ h)⟩
    · trivial
  | .plus r₁ r₂, n, h | .intersection r₁ r₂, n, h | .complement r₁ r₂, n, h => exact ⟨full_D a r₁ n h.1, full_D a r₂ n h.2⟩
  | .mult r₁ _, n, h => exact ⟨full_D a r₁ n h, full_DLA a r₁ n h⟩
  | .star r b, n, h => exact ⟨full_DLA a r n h.1, full_D a b n h.2, full_D a r n h.1⟩

theorem full_DLA [DecidableEq α] (a : α) (r : SRegex α) (n : Nat) (h: Full r n) : Full (DLA a r) (n + 1) := by
  match r, n, h with
  | .empty, _, _ | .symbol _ _, _, _ => trivial
  | .unit _, _, h | .top _, _, h => exact eq_laStep h
  | .plus r₁ r₂, n, h | .intersection r₁ r₂, n, h | .complement r₁ r₂, n, h | .star r₁ r₂, n, h => exact ⟨full_DLA a r₁ n h.1, full_DLA a r₂ n h.2⟩
  | .mult r₁ _, n, h => exact full_DLA a r₁ n h
  | .lb r, n, h => exact laOnly_DLA a r n h
  | .la r, n, h => exact full_D a r n h

theorem laOnly_DLA [DecidableEq α] (a : α) (r : SRegex α) (n : Nat) (h: LAOnly r n) : LAOnly (DLA a r) (n + 1) := by
  match r, n, h with
  | .empty, _, _ | .symbol _ _, _, _ => trivial
  | .unit _, _, h | .top _, _, h => exact laOnly_laStep h
  | .plus r₁ r₂, n, h | .intersection r₁ r₂, n, h | .complement r₁ r₂, n, h
  | .mult r₁ r₂, n, h | .star r₁ r₂, n, h => exact ⟨laOnly_DLA a r₁ n h.1, laOnly_DLA a r₂ n h.2⟩
  | .lb r, n, h => exact laOnly_DLA a r n h
  | .la r, n, h => exact full_D a r n h
end

mutual
theorem wf_D [DecidableEq α] (a : α) (r : SRegex α) (n : Nat) (h: WF r n) : WF (D a r) (n + 1) := by
  match r, n, h with
  | .empty, _, _ | .unit _, _, _ | .lb _, _, _ | .la _, _, _ => trivial
  | .top _, _, h => exact ⟨le_mStep (all_filter _ h), le_laStep (all_filter _ h)⟩
  | .symbol _ _, _, h =>
    simp only [D]; split
    · exact ⟨le_mStep (all_filter _ h), le_laStep (all_filter _ h)⟩
    · trivial
  | .plus r₁ r₂, n, h | .intersection r₁ r₂, n, h | .complement r₁ r₂, n, h => exact ⟨wf_D a r₁ n h.1, wf_D a r₂ n h.2⟩
  | .mult r₁ r₂, n, h => exact ⟨⟨wf_D a r₁ n h.1, wf_DLB a r₂ n h.2⟩, ⟨wf_DLA a r₁ n h.1, wf_D a r₂ n h.2⟩⟩
  | .star r b, n, h => exact ⟨wf_DLA a r n h.1, wf_D a b n h.2, wf_D a r n h.1, wf_DLB a r n h.1, wf_DLB a b n h.2⟩

theorem wf_DLB [DecidableEq α] (a : α) (r : SRegex α) (n : Nat) (h: WF r n) : WF (DLB a r) (n + 1) := by
  match r, n, h with
  | .empty, _, _ => trivial
  | .unit _, _, h => exact ⟨le_succ_all (all_filter _ h), le_laStep (all_filter _ h)⟩
  | .top _, _, h | .symbol _ _, _, h => exact ⟨le_succ_all (all_filter _ h), le_mStep (all_filter _ h), le_laStep (all_filter _ h)⟩
  | .plus r₁ r₂, n, h | .intersection r₁ r₂, n, h | .complement r₁ r₂, n, h
  | .mult r₁ r₂, n, h | .star r₁ r₂, n, h => exact ⟨wf_DLB a r₁ n h.1, wf_DLB a r₂ n h.2⟩
  | .lb r, n, h => exact ⟨wf_D a r n h.1, full_D a r n h.2⟩
  | .la r, n, h => exact wf_DLB a r n h

theorem wf_DLA [DecidableEq α] (a : α) (r : SRegex α) (n : Nat) (h: WF r n) : WF (DLA a r) (n + 1) := by
  match r, n, h with
  | .empty, _, _ | .symbol _ _, _, _ => trivial
  | .unit _, _, h | .top _, _, h => exact le_laStep h
  | .plus r₁ r₂, n, h | .intersection r₁ r₂, n, h | .complement r₁ r₂, n, h
  | .mult r₁ r₂, n, h | .star r₁ r₂, n, h => exact ⟨wf_DLA a r₁ n h.1, wf_DLA a r₂ n h.2⟩
  | .lb r, n, h => exact ⟨wf_DLA a r n h.1, full_DLA a r n h.2⟩
  | .la r, n, h => exact wf_D a r n h
end

theorem wf_xD [DecidableEq α] (w : List α) (r : SRegex α) (n : Nat) (h : WF r n) : WF (xD w r) (n + w.length) := by
  induction w generalizing r n with
  | nil => exact h
  | cons a w ih =>
    have := ih (.plus (.plus (DLB a r) (D a r)) (DLA a r)) (n + 1) ⟨⟨wf_DLB a r n h, wf_D a r n h⟩, wf_DLA a r n h⟩
    rw [Nat.add_right_comm] at this
    exact this

theorem regexToSRegex_wf (r : Regex α) : WF (regexToSRegex r) 0 ∧ Full (regexToSRegex r) 0 ∧ LAOnly (regexToSRegex r) 0 := by
  match r with
  | .empty => exact ⟨trivial, trivial, trivial⟩
  | .unit | .top | .symbol _ =>
    simp [regexToSRegex, WF, Full, LAOnly, Steps.stepsSum, Steps.zeroSteps]
  | .plus r₁ r₂ | .intersection r₁ r₂ | .complement r₁ r₂ | .star r₁ r₂ =>
    have h₁ := regexToSRegex_wf r₁; have h₂ := regexToSRegex_wf r₂
    exact ⟨⟨h₁.1, h₂.1⟩, ⟨h₁.2.1, h₂.2.1⟩, ⟨h₁.2.2, h₂.2.2⟩⟩
  | .mult r₁ r₂ =>
    have h₁ := regexToSRegex_wf r₁; have h₂ := regexToSRegex_wf r₂
    exact ⟨⟨h₁.1, h₂.1⟩, h₁.2.1, ⟨h₁.2.2, h₂.2.2⟩⟩
  | .lb r =>
    have h := regexToSRegex_wf r
    exact ⟨⟨h.1, h.2.1⟩, h.2.2, h.2.2⟩
  | .la r =>
    have h := regexToSRegex_wf r
    exact ⟨h.1, h.2.1, h.2.1⟩

theorem wf_findAllMatches [DecidableEq α] (r : Regex α) (w : List α) : WF (xD w (regexToSRegex r)) w.length := by
  have := wf_xD w _ 0 (regexToSRegex_wf r).1
  rwa [Nat.zero_add] at this


end AlgorithmHelpers

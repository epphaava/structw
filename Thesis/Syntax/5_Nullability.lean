import Thesis.Syntax.«1_Expressions»
import Thesis.Syntax.«2_Derivatives»
import Thesis.Syntax.«4_DerivativeCorrectHelpers»
import Thesis.Semantics.«9_NullabilityLaws»


namespace Nullability

open SRegex
open StructuredWords
open Operators
open NullabilityLaws
open DerCorrectHelp
open SRegexDerivatives


def compose (s₁ s₂ : Steps) : Option Steps :=
  if s₁.la = s₂.m + s₂.la then some ⟨s₁.m + s₂.m, s₂.la⟩ else none

def concatN (n₁ n₂ : List Steps) : List Steps :=
  n₁.flatMap fun s₁ => n₂.filterMap (compose s₁)

def starStep (nr acc : List Steps) : List Steps := (acc ++ concatN nr acc).eraseDups

def starN (nr : List Steps) : Nat → List Steps → List Steps
  | 0, acc => acc
  | k + 1, acc => starN nr k (starStep nr acc)


def N {α} (r : SRegex α) : List Steps :=
  match r with
  | .empty => []
  | .unit ss => ss
  | .top ss => ss
  | .symbol _ _ => []
  | .plus r₁ r₂ => N r₁ ++ N r₂
  | .intersection r₁ r₂ => (N r₁).filter fun s => (N r₂).contains s
  | .complement r₁ r₂ => (N r₁).filter fun s => !(N r₂).contains s
  | .mult r₁ r₂ => concatN (N r₁) (N r₂)
  | .star r b => starN (N r) (Steps.maxSum (N b) + 1) (N b)
  | .lb r => (N r).map fun s => ⟨0, s.la⟩
  | .la r => (N r).filterMap fun s => if s.la = 0 then some ⟨0, s.m⟩ else none

/- def ssEqLen {α} : SRegex α → Nat → Prop
  | .empty, _ => True
  | .unit ss, n | .top ss, n | .symbol _ ss, n => ∀ s ∈ ss, (Steps.stepsSum s) = n
  | .plus r₁ r₂, n | .intersection r₁ r₂, n | .complement r₁ r₂, n
  | .mult r₁ r₂, n | .star r₁ r₂, n => ssEqLen r₁ n ∧ ssEqLen r₂ n
  | .lb r, n | .la r, n => ssEqLen r n
 -/


theorem compose_eq {s₁ s₂ t : Steps} :
    compose s₁ s₂ = some t ↔ s₁.la = s₂.m + s₂.la ∧ t = ⟨s₁.m + s₂.m, s₂.la⟩ := by
  simp [compose, eq_comm]

theorem mem_concatN {n₁ n₂ : List Steps} {t : Steps} : t ∈ concatN n₁ n₂ ↔ ∃ s₁ ∈ n₁, ∃ s₂ ∈ n₂, compose s₁ s₂ = some t := by
  simp [concatN]

theorem compose_sum {s₁ s₂ t : Steps} (h : compose s₁ s₂ = some t) :
    s₁.stepsSum = t.stepsSum ∧ s₁.m + s₂.stepsSum = t.stepsSum := by
  obtain ⟨h1, rfl⟩ := compose_eq.mp h
  simp [Steps.stepsSum]; omega

theorem compose_m_zero {s₁ s₂ t : Steps} (h : compose s₁ s₂ = some t) (hm : s₁.m = 0) : t = s₂ := by
  obtain ⟨_, rfl⟩ := compose_eq.mp h
  simp [hm]

theorem mem_starStep {nr acc : List Steps} {t : Steps} : t ∈ starStep nr acc ↔ t ∈ acc ∨ t ∈ concatN nr acc := by
  simp [starStep, List.mem_eraseDups]

theorem subset_starN (nr : List Steps) (k : Nat) (acc : List Steps) {t : Steps} : t ∈ acc → t ∈ starN nr k acc := by
  induction k generalizing acc with
  | zero => exact id
  | succ k ih => intro h; exact ih _ (mem_starStep.mpr (.inl h))

theorem starN_succ_mono (nr : List Steps) (k : Nat) (acc : List Steps) {t : Steps} : t ∈ starN nr k acc → t ∈ starN nr (k + 1) acc := by
  induction k generalizing acc with
  | zero => exact subset_starN nr 1 acc
  | succ k ih => exact ih _

theorem starN_mono (nr : List Steps) {k k' : Nat} (hk : k ≤ k') (acc : List Steps) {t : Steps} : t ∈ starN nr k acc → t ∈ starN nr k' acc := by
  induction hk with
  | refl => exact id
  | step _ ih => exact fun h => starN_succ_mono nr _ acc (ih h)

theorem starN_compose (nr : List Steps) (k : Nat) (acc : List Steps) {s₁ s₂ t : Steps}
    (h₁ : s₁ ∈ nr) (h₂ : s₂ ∈ starN nr k acc) (h : compose s₁ s₂ = some t) : t ∈ starN nr (k + 1) acc := by
  induction k generalizing acc with
  | zero => exact subset_starN nr 0 _ (mem_starStep.mpr (.inr (mem_concatN.mpr ⟨s₁, h₁, s₂, h₂, h⟩)))
  | succ k ih => exact ih _ h₂

theorem starN_induct (nr : List Steps) (P : Steps → Prop)
    (hc : ∀ s₁ s₂ t, s₁ ∈ nr → P s₂ → compose s₁ s₂ = some t → P t) (k : Nat) (acc : List Steps)
    (h : ∀ t ∈ acc, P t) : ∀ t ∈ starN nr k acc, P t := by
  induction k generalizing acc with
  | zero => exact h
  | succ k ih =>
    apply ih
    intro t ht
    rcases mem_starStep.mp ht with ht | ht
    · exact h t ht
    · obtain ⟨s₁, h₁, s₂, h₂, hc'⟩ := mem_concatN.mp ht
      exact hc s₁ s₂ t h₁ (h s₂ h₂) hc'

theorem le_maxSum {ss : List Steps} {s : Steps} (h : s ∈ ss) : s.stepsSum ≤ Steps.maxSum ss := by
  induction ss with
  | nil => simp at h
  | cons x xs ih =>
    simp only [Steps.maxSum]
    rcases List.mem_cons.mp h with rfl | h
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih h) (Nat.le_max_right _ _)


-- show that for any regex, regextoSRegex nullablity has always the same ampunt of steps (inluding lookbehind)

variable {α : Type} [DecidableEq α]

--

theorem N_correct (r : SRegex α) (n : Nat) (t : Steps):
    nullable (sem r) t.m t.la ↔ t ∈ N r := by
  induction r generalizing n t with
  | empty => simp [nullable, sem, N, empty]
  | unit ss =>
    sorry
  | _ =>
    sorry



end Nullability

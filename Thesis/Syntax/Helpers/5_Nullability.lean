import Thesis.Syntax.«1_Expressions»
import Thesis.Syntax.«2_Derivatives»
import Thesis.Syntax.Helpers.«4_DerivativeCorrectness»
import Thesis.Semantics.«9_NullabilityLaws»


namespace NullabilityHelpers

open SRegex
open StructuredWords
open Operators
open NullabilityLaws
open DerCorrectHelpers
open SRegexDerivatives
open Steps

def compose (s₁ s₂ : Steps) : Option Steps :=
  if s₁.la = s₂.m + s₂.la then some ⟨s₁.m + s₂.m, s₂.la⟩ else none

def concatN (n₁ n₂ : List Steps) : List Steps :=
  n₁.flatMap fun s₁ => n₂.filterMap (compose s₁)

def starStep (nr acc : List Steps) : List Steps := (acc ++ concatN nr acc).eraseDups

def starN (nr : List Steps) : Nat → List Steps → List Steps
  | 0, acc => acc
  | k + 1, acc => starN nr k (starStep nr acc)


mutual
def Full {α} : SRegex α → Nat → Prop
  | .empty, _ => True
  | .unit ss, n | .top ss, n | .symbol _ ss, n => ∀ s ∈ ss, s.stepsSum = n
  | .plus r₁ r₂, n | .intersection r₁ r₂, n | .complement r₁ r₂, n => Full r₁ n ∧ Full r₂ n
  | .mult r₁ _, n => Full r₁ n
  | .star r b, n => Full r n ∧ Full b n
  | .lb r, n => LAOnly r n
  | .la r, n => Full r n

def LAOnly {α} : SRegex α → Nat → Prop
  | .empty, _ => True
  | .unit ss, n | .top ss, n | .symbol _ ss, n => ∀ s ∈ ss, s.m = 0 ∧ s.la = n
  | .plus r₁ r₂, n | .intersection r₁ r₂, n | .complement r₁ r₂, n
  | .mult r₁ r₂, n | .star r₁ r₂, n => LAOnly r₁ n ∧ LAOnly r₂ n
  | .lb r, n => LAOnly r n
  | .la r, n => Full r n
end

def WF {α} : SRegex α → Nat → Prop
  | .empty, _ => True
  | .unit ss, n | .top ss, n | .symbol _ ss, n => ∀ s ∈ ss, s.stepsSum ≤ n
  | .plus r₁ r₂, n | .intersection r₁ r₂, n | .complement r₁ r₂, n
  | .mult r₁ r₂, n | .star r₁ r₂, n => WF r₁ n ∧ WF r₂ n
  | .lb r, n => WF r n ∧ Full r n
  | .la r, n => WF r n


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

theorem starN_sum_le (nr nb : List Steps) (k : Nat) : ∀ t ∈ starN nr k nb, t.stepsSum ≤ max (Steps.maxSum nr) (Steps.maxSum nb) := by
  apply starN_induct
  · intro s₁ s₂ t h₁ _ hc
    have := le_maxSum h₁
    rw [← (compose_sum hc).1]; omega
  · intro t ht; have := le_maxSum ht; omega


def lbOf (n : Nat) (t : Steps) : Nat := n - t.stepsSum

theorem star_N {α : Type} (l base : Lang α) (nr nb : List Steps) (n : Nat)
    (hr : ∀ t : Steps, t.stepsSum ≤ n → (nullable l (lbOf n t) t.m t.la ↔ t ∈ nr))
    (hb : ∀ t : Steps, t.stepsSum ≤ n → (nullable base (lbOf n t) t.m t.la ↔ t ∈ nb))
    (hnr : ∀ t ∈ nr, t.stepsSum ≤ n) (t : Steps) (ht : t.stepsSum ≤ n) :
    nullable (star l base) (lbOf n t) t.m t.la ↔
      t ∈ starN nr (max (Steps.maxSum nr) (Steps.maxSum nb) + 1) nb := by
  constructor
  · intro h
    suffices key : ∀ w, star_help l base w → ∀ t : Steps, w = .right (lbOf n t) t.m t.la [] →
        t.stepsSum ≤ n → t ∈ starN nr t.m nb by
      have hm := key _ h t rfl ht
      have := starN_sum_le nr nb t.m t hm
      exact starN_mono nr (Nat.le_succ_of_le (Nat.le_trans (Nat.le_add_right t.m t.la) this)) nb hm
    intro w hw
    induction hw with
    | inUnit w hbase =>
      intro t hwt ht; subst hwt
      exact subset_starN nr _ nb ((hb t ht).mp hbase)
    | inConcat w₁ w₂ w h₁ _ hwc ih =>
      intro t hwt ht
      subst hwt
      obtain ⟨mc₁, mc₂, hmc, rfl, rfl⟩ := hwc
      simp only [lbOf, Steps.stepsSum, Nat.add_eq] at ht h₁ ih
      let s₁ : Steps := ⟨mc₁, mc₂ + t.la⟩
      let s₂ : Steps := ⟨mc₂, t.la⟩
      have hc : compose s₁ s₂ = some t := by
        rw [compose_eq]; obtain ⟨_, _⟩ := t; simp_all [s₁, s₂]
      have h₂ : s₂ ∈ starN nr s₂.m nb :=
        ih s₂ (by simp [s₂]; omega) (by simp [s₂]; omega)
      have hs₁ : s₁ ∈ nr := by
        refine (hr s₁ (by simp [s₁, Steps.stepsSum]; omega)).mp ?_
        have e : (n - (t.m + t.la)) = (n - (s₁.m + s₁.la)) := by simp [s₁]; omega
        simp [nullable, lbOf, Steps.stepsSum, ←e]; exact h₁
      by_cases hz : mc₁ = 0
      · rw [compose_m_zero hc hz]; exact starN_mono nr (by simp [s₂]) nb h₂
      · exact starN_mono nr (by simp [s₂]; omega) nb (starN_compose nr _ nb hs₁ h₂ hc)
  · intro hmem
    refine starN_induct nr (fun t => t.stepsSum ≤ n → nullable (star l base) (lbOf n t) t.m t.la) ?_ _ nb ?_ t hmem ht
    · intro s₁ s₂ t h₁ h₂ hc ht
      have hs₁ := hnr s₁ h₁
      obtain ⟨e1, rfl⟩ := compose_eq.mp hc
      simp [Steps.stepsSum] at ht hs₁
      refine (nullable_star l base).mpr (.inr ⟨s₁.m, s₂.m, rfl, ?_, ?_⟩)
      · have := (hr s₁ (by simp [Steps.stepsSum]; omega)).mpr h₁
        have e : lbOf n s₁ = (n - ((s₁.m + s₂.m) + s₂.la)) := by
          simp [lbOf, Steps.stepsSum]; omega
        simp [lbOf, Steps.stepsSum] at this e ⊢
        rw [e, e1] at this; exact this
      · have := h₂ (by simp [Steps.stepsSum]; omega)
        have e : lbOf n s₂ = ((n - ((s₁.m + s₂.m) + s₂.la)) + s₁.m) := by
          simp [lbOf, Steps.stepsSum]; omega
        simp [lbOf, Steps.stepsSum] at this e ⊢
        rw [e] at this; exact this
    · intro t ht hn; exact (nullable_star l base).mpr (.inl ((hb t hn).mpr ht))


end NullabilityHelpers

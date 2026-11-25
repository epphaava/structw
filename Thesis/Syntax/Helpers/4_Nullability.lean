import Thesis.Syntax.«1_Expressions»
import Thesis.Syntax.«2_Derivatives»
import Thesis.Syntax.Helpers.«3_DerivativeCorrectness»
import Thesis.Semantics.kLang.«9_NullabilityLaws»


namespace NullabilityHelpers

open SRegex
open StructuredWords
open kStructuredWords
open kOperators
open Operators
open kDerivatives
open kNullabilityLaws
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

theorem starN_induct (nr : List Steps) (p : Steps → Prop)
    (hc : ∀ s₁ s₂ t, s₁ ∈ nr → p s₂ → compose s₁ s₂ = some t → p t) (k : Nat) (acc : List Steps)
    (h : ∀ t ∈ acc, p t) : ∀ t ∈ starN nr k acc, p t := by
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


theorem star_N {α : Type} (l base : kLang α n) (nr nb : List Steps)
    (hr : ∀ t : Steps, t.stepsSum ≤ n → (nullable l t.m t.la ↔ t ∈ nr))
    (hb : ∀ t : Steps, t.stepsSum ≤ n → (nullable base t.m t.la ↔ t ∈ nb))
    (hnr : ∀ t ∈ nr, t.stepsSum ≤ n) (t : Steps) (ht : t.stepsSum ≤ n) :
    nullable (star l base) t.m t.la ↔
      t ∈ starN nr (max (Steps.maxSum nr) (Steps.maxSum nb) + 1) nb := by
  constructor
  · intro h
    suffices key : ∀ w, star_help l.1 base.1 w → ∀ t : Steps, w = .right t.m t.la [] →
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
      simp only [Steps.stepsSum, Nat.add_eq] at ht
      let s₁ : Steps := ⟨mc₁, mc₂ + t.la⟩
      let s₂ : Steps := ⟨mc₂, t.la⟩
      have hc : compose s₁ s₂ = some t := by
        rw [compose_eq]; obtain ⟨_, _⟩ := t; simp_all [s₁, s₂]
      have h₂ : s₂ ∈ starN nr s₂.m nb :=
        ih s₂ rfl (by simp [s₂, Steps.stepsSum]; omega)
      have hs₁ : s₁ ∈ nr := (hr s₁ (by simp [s₁, Steps.stepsSum]; omega)).mp h₁
      by_cases hz : mc₁ = 0
      · rw [compose_m_zero hc hz]; exact starN_mono nr (by simp [s₂]) nb h₂
      · exact starN_mono nr (by simp [s₂]; omega) nb (starN_compose nr _ nb hs₁ h₂ hc)
  · intro hmem
    refine starN_induct nr (fun t => t.stepsSum ≤ n → nullable (star l base) t.m t.la) ?_ _ nb ?_ t hmem ht
    · intro s₁ s₂ t h₁ h₂ hc ht
      have hs₁ := hnr s₁ h₁
      obtain ⟨e1, rfl⟩ := compose_eq.mp hc
      simp [Steps.stepsSum] at ht hs₁
      refine (nullable_star l base).mpr (.inr ⟨s₁.m, s₂.m, rfl, ?_, ?_⟩)
      · have := (hr s₁ (by simp [Steps.stepsSum]; omega)).mpr h₁
        rw [e1] at this; exact this
      · exact h₂ (by simp [Steps.stepsSum]; omega)
    · intro t ht hn; exact (nullable_star l base).mpr (.inl ((hb t hn).mpr ht))

def WF {α} : SRegex α → Nat → Prop
  | .empty, _ => True
  | .unit ss, n | .top ss, n | .symbol _ ss, n => ∀ s ∈ ss, s.stepsSum ≤ n
  | .plus r₁ r₂, n | .intersection r₁ r₂, n | .complement r₁ r₂, n
  | .mult r₁ r₂, n => WF r₁ n ∧ WF r₂ n
  | .star r b, n => WF r n ∧ WF b n
  | .lb r, n | .la r, n => WF r n


theorem wf_lbStep {ss : List Steps} {n : Nat} (h : ∀ s ∈ ss, s.stepsSum ≤ n) :
    ∀ s ∈ ↑₁ss, s.stepsSum ≤ n + 1 :=
  λ s hs => Nat.le_succ_of_le (h s (List.mem_filter.mp hs).1)

theorem wf_mStep {ss : List Steps} {n : Nat} (h : ∀ s ∈ ss, s.stepsSum ≤ n) :
    ∀ s ∈ ↑₂ss, s.stepsSum ≤ n + 1 := by
  intro s hs
  obtain ⟨s', hs', rfl⟩ := List.mem_map.mp hs
  have := h s' (List.mem_filter.mp hs').1
  simp [mStepSingle, stepsSum] at *; omega

theorem wf_laStep {ss : List Steps} {n : Nat} (h : ∀ s ∈ ss, s.stepsSum ≤ n) :
    ∀ s ∈ ↑₃ss, s.stepsSum ≤ n + 1 := by
  intro s hs
  obtain ⟨s', hs', rfl⟩ := List.mem_map.mp hs
  have := h s' hs'
  simp [laStepSingle, stepsSum] at *; omega

mutual
theorem wf_D [DecidableEq α] (a : α) (r : SRegex α) (n : Nat) (h : WF r n) : WF (D a r) (n.succ) := by
  match r, n, h with
  | .empty, _, _ | .unit _, _, _ | .lb _, _, _ | .la _, _, _ => trivial
  | .top _, _, h => exact wf_mStep h
  | .symbol _ _, _, h =>
    simp only [D]; split
    · exact wf_mStep h
    · trivial
  | .plus r₁ r₂, n, h | .intersection r₁ r₂, n, h | .complement r₁ r₂, n, h => exact ⟨wf_D a r₁ n h.1, wf_D a r₂ n h.2⟩
  | .mult r₁ r₂, n, h => exact ⟨⟨wf_D a r₁ n h.1, wf_DLB a r₂ n h.2⟩, ⟨wf_DLA a r₁ n h.1, wf_D a r₂ n h.2⟩⟩
  | .star r b, n, h => exact ⟨wf_DLA a r n h.1, wf_D a b n h.2, wf_D a r n h.1, wf_DLB a r n h.1, wf_DLB a b n h.2⟩

theorem wf_DLB [DecidableEq α] (a : α) (r : SRegex α) (n : Nat) (h : WF r n) : WF (DLB a r) (n.succ) := by
  match r, n, h with
  | .empty, _, _ => trivial
  | .unit _, _, h | .top _, _, h | .symbol _ _, _, h => exact wf_lbStep h
  | .plus r₁ r₂, n, h | .intersection r₁ r₂, n, h | .complement r₁ r₂, n, h
  | .mult r₁ r₂, n, h | .star r₁ r₂, n, h => exact ⟨wf_DLB a r₁ n h.1, wf_DLB a r₂ n h.2⟩
  | .lb r, n, h => exact wf_D a r n h
  | .la r, n, h => exact wf_DLB a r n h

theorem wf_DLA [DecidableEq α] (a : α) (r : SRegex α) (n : Nat) (h : WF r n) : WF (DLA a r) (n.succ) := by
  match r, n, h with
  | .empty, _, _ | .symbol _ _, _, _ => trivial
  | .unit _, _, h | .top _, _, h => exact wf_laStep h
  | .plus r₁ r₂, n, h | .intersection r₁ r₂, n, h | .complement r₁ r₂, n, h
  | .mult r₁ r₂, n, h | .star r₁ r₂, n, h => exact ⟨wf_DLA a r₁ n h.1, wf_DLA a r₂ n h.2⟩
  | .lb r, n, h => exact wf_DLA a r n h
  | .la r, n, h => exact wf_D a r n h
end

theorem wf_xD [DecidableEq α] (w : List α) (r : SRegex α) (n : Nat) (h : WF r n) : WF (xD w r) (n + w.length) := by
  induction w generalizing r n with
  | nil => exact h
  | cons a w ih =>
    have := ih (((DLB a r) + (D a r)) + (DLA a r)) (n.succ) ⟨⟨wf_DLB a r n h, wf_D a r n h⟩, wf_DLA a r n h⟩
    rw [Nat.succ_add] at this
    exact this



end NullabilityHelpers

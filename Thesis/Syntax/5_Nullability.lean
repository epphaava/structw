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
  if s₂.lb = s₁.lb + s₁.m ∧ s₁.la = s₂.m + s₂.la then some ⟨s₁.lb, s₁.m + s₂.m, s₂.la⟩ else none

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
  | .lb r => (N r).filterMap fun s => if s.lb = 0 then some ⟨s.m, 0, s.la⟩ else none
  | .la r => (N r).filterMap fun s => if s.la = 0 then some ⟨s.lb, 0, s.m⟩ else none

def ssEqLen {α} : SRegex α → Nat → Prop
  | .empty, _ => True
  | .unit ss, n | .top ss, n | .symbol _ ss, n => ∀ s ∈ ss, (Steps.stepsSum s) = n
  | .plus r₁ r₂, n | .intersection r₁ r₂, n | .complement r₁ r₂, n
  | .mult r₁ r₂, n | .star r₁ r₂, n => ssEqLen r₁ n ∧ ssEqLen r₂ n
  | .lb r, n | .la r, n => ssEqLen r n



theorem compose_eq {s₁ s₂ t : Steps} :
    compose s₁ s₂ = some t ↔ s₂.lb = s₁.lb + s₁.m ∧ s₁.la = s₂.m + s₂.la ∧ t = ⟨s₁.lb, s₁.m + s₂.m, s₂.la⟩ := by
  simp [compose, eq_comm, and_assoc]

theorem mem_concatN {n₁ n₂ : List Steps} {t : Steps} : t ∈ concatN n₁ n₂ ↔ ∃ s₁ ∈ n₁, ∃ s₂ ∈ n₂, compose s₁ s₂ = some t := by
  simp [concatN]

theorem compose_sum {s₁ s₂ t : Steps} (h : compose s₁ s₂ = some t) : s₁.stepsSum = t.stepsSum ∧ s₂.stepsSum = t.stepsSum := by
  obtain ⟨h1, h2, rfl⟩ := compose_eq.mp h
  simp only [Steps.stepsSum, Nat.add_eq]; omega

theorem compose_m_zero {s₁ s₂ t : Steps} (h : compose s₁ s₂ = some t) (hm : s₁.m = 0) : t = s₂ := by
  obtain ⟨h1, h2, rfl⟩ := compose_eq.mp h
  obtain ⟨lb, m, la⟩ := s₂
  simp_all

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

theorem steps_right_eq {s t : Steps} (hs : s.stepsSum = t.stepsSum) (h1 : s.lb ≤ t.lb) (h2 : s.m ≤ t.m)
    (h3 : s.la ≤ t.la) : s = t := by
  obtain ⟨_, _, _⟩ := s; obtain ⟨_, _, _⟩ := t
  simp only [Steps.stepsSum, Nat.add_eq] at *; simp only [Steps.mk.injEq]; omega

theorem N_sum {α} (r : SRegex α) (n : Nat) (hwf : ssEqLen r n) : ∀ t ∈ N r, t.stepsSum = n := by
  induction r generalizing n with
  | empty => simp [N]
  | unit ss | top ss => exact hwf
  | symbol _ _ => simp [N]
  | plus r₁ r₂ ih₁ ih₂ =>
    intro t ht
    rcases List.mem_append.mp ht with ht | ht
    · exact ih₁ n hwf.1 t ht
    · exact ih₂ n hwf.2 t ht
  | intersection r₁ r₂ ih₁ _ | complement r₁ r₂ ih₁ _ =>
    intro t ht; exact ih₁ n hwf.1 t (List.mem_filter.mp ht).1
  | mult r₁ r₂ ih₁ _ =>
    intro t ht
    obtain ⟨s₁, h₁, s₂, _, hc⟩ := mem_concatN.mp ht
    exact (compose_sum hc).1 ▸ ih₁ n hwf.1 s₁ h₁
  | star r b _ ihb =>
    apply starN_induct _ (fun t => t.stepsSum = n)
    · intro s₁ s₂ t _ h hc; exact (compose_sum hc).2 ▸ h
    · exact ihb n hwf.2
  | lb r ih =>
    intro t ht
    simp only [N, List.mem_filterMap] at ht
    obtain ⟨s, hs, h⟩ := ht
    split at h <;> simp at h
    have := ih n hwf s hs; subst h; simp only [Steps.stepsSum, Nat.add_eq] at *; omega
  | la r ih =>
    intro t ht
    simp only [N, List.mem_filterMap] at ht
    obtain ⟨s, hs, h⟩ := ht
    split at h <;> simp at h
    have := ih n hwf s hs; subst h; simp only [Steps.stepsSum, Nat.add_eq] at *; omega


theorem star_N {α : Type} (l base : Lang α) (nr nb : List Steps) (n : Nat)
    (hr : ∀ t : Steps, t.stepsSum = n → (nullable l t.lb t.m t.la ↔ t ∈ nr))
    (hb : ∀ t : Steps, t.stepsSum = n → (nullable base t.lb t.m t.la ↔ t ∈ nb))
    (hnb : ∀ t ∈ nb, t.stepsSum = n) (t : Steps) (ht : t.stepsSum = n) :
    nullable (star l base) t.lb t.m t.la ↔ t ∈ starN nr (Steps.maxSum nb + 1) nb := by
  constructor
  · intro h
    suffices key : ∀ w, star_help l base w → ∀ t : Steps, w = .right t.lb t.m t.la [] →
        t.stepsSum = n → t ∈ starN nr t.m nb by
      have hm := key _ h t rfl ht
      have hne : ∃ s, s ∈ nb := by
        cases nb with
        | nil =>
          have hc : concatN nr [] = [] := by simp [concatN]
          have : ∀ k, starN nr k [] = [] := by
            intro k; induction k with
            | zero => rfl
            | succ k ih => rw [starN, starStep, hc]; exact ih
          simp [this] at hm
        | cons s _ => exact ⟨s, List.mem_cons_self⟩
      obtain ⟨s, hs⟩ := hne
      have := le_maxSum hs
      have := hnb s hs
      exact starN_mono nr (by simp only [Steps.stepsSum, Nat.add_eq] at *; omega) nb hm
    intro w hw
    induction hw with
    | inUnit w hbase =>
      intro t hwt ht
      subst hwt
      exact subset_starN nr _ nb ((hb t ht).mp hbase)
    | inConcat w₁ w₂ w h₁ _ hwc ih =>
      intro t hwt ht
      subst hwt
      obtain ⟨mc₁, mc₂, hmc, rfl, rfl⟩ := hwc
      let s₁ : Steps := ⟨t.lb, mc₁, mc₂ + t.la⟩
      let s₂ : Steps := ⟨t.lb + mc₁, mc₂, t.la⟩
      have hc : compose s₁ s₂ = some t := by
        rw [compose_eq]; obtain ⟨_, _, _⟩ := t; simp_all [s₁, s₂]
      have h₂ := ih s₂ rfl (by simp only [Steps.stepsSum, Nat.add_eq, s₂] at *; omega)
      have hs₁ := (hr s₁ (by simp only [Steps.stepsSum, Nat.add_eq, s₁] at *; omega)).mp h₁
      by_cases hz : mc₁ = 0
      · rw [compose_m_zero hc hz]
        exact starN_mono nr (by simp only [s₂]; omega) nb h₂
      · exact starN_mono nr (by simp only [s₂]; omega) nb (starN_compose nr _ nb hs₁ h₂ hc)
  · intro hmem
    refine starN_induct nr (fun t => t.stepsSum = n → nullable (star l base) t.lb t.m t.la) ?_ _ nb ?_ t hmem ht
    · intro s₁ s₂ t h₁ h₂ hc ht
      obtain ⟨hs₁, hs₂⟩ := compose_sum hc
      obtain ⟨e1, e2, rfl⟩ := compose_eq.mp hc
      refine (nullable_star l base).mpr (.inr ⟨s₁.m, s₂.m, rfl, ?_, ?_⟩)
      · have := (hr s₁ (hs₁.trans ht)).mpr h₁
        rw [e2] at this; exact this
      · have := h₂ (hs₂.trans ht)
        rw [e1] at this; exact this
    · intro t ht hn
      exact (nullable_star l base).mpr (.inl ((hb t hn).mpr ht))

variable {α : Type} [DecidableEq α]

theorem N_correct (r : SRegex α) (n : Nat) (hwf : ssEqLen r n) (t : Steps) (ht : t.stepsSum = n) :
    nullable (sem r) t.lb t.m t.la ↔ t ∈ N r := by
  induction r generalizing n t with
  | empty => simp [nullable, sem, N, empty]
  | unit ss =>
    simp [nullable, sem, N, atom_iff]
    constructor
    · rintro ⟨s, hs, h⟩; rw [← steps_right_eq ((hwf s hs).trans ht.symm) h.1 h.2.1 h.2.2.1]; exact hs
    · intro h; exact ⟨t, h, by simp [sem.steps, unit]⟩
  | top ss =>
    simp [nullable, sem, N, atom_iff]
    constructor
    · rintro ⟨s, hs, h⟩; simp [sem.steps, top] at h
      rw [← steps_right_eq ((hwf s hs).trans ht.symm) h.1 h.2.1 h.2.2]; exact hs
    · intro h; exact ⟨t, h, by simp [sem.steps, top]⟩
  | symbol b ss => simp [nullable, sem, N, atom_iff, sem.steps]
  | plus r₁ r₂ ih₁ ih₂ => simp [N, List.mem_append]; exact (nullable_union).trans (or_congr (ih₁ n hwf.1 t ht) (ih₂ n hwf.2 t ht))
  | intersection r₁ r₂ ih₁ ih₂ => simp [N, List.mem_filter]; exact (nullable_intersection).trans (and_congr (ih₁ n hwf.1 t ht) (ih₂ n hwf.2 t ht))
  | complement r₁ r₂ ih₁ ih₂ => simp [N, List.mem_filter, ← Bool.not_eq_true]; exact (nullable_diff).trans (and_congr (ih₁ n hwf.1 t ht) (not_congr (ih₂ n hwf.2 t ht)))
  | mult r₁ r₂ ih₁ ih₂ =>
    simp [N, sem, nullable_concat, mem_concatN]
    constructor
    · rintro ⟨mc₁, mc₂, hmc, h₁, h₂⟩
      let s₁ : Steps := ⟨t.lb, mc₁, mc₂ + t.la⟩
      let s₂ : Steps := ⟨t.lb + mc₁, mc₂, t.la⟩
      have ih₁ := (ih₁ n hwf.1 s₁ (by simp [Steps.stepsSum, s₁] at *; omega)).mp h₁
      have ih₂ := (ih₂ n hwf.2 s₂ (by simp [Steps.stepsSum, s₂] at *; omega)).mp h₂
      obtain ⟨_, _, _⟩ := t;
      refine ⟨s₁, ih₁, s₂, ih₂, ?_⟩
      simp [compose, s₁, s₂] at *; omega
    · rintro ⟨s₁, h₁, s₂, h₂, hc⟩
      obtain ⟨hs₁, hs₂⟩ := compose_sum hc
      obtain ⟨e1, e2, rfl⟩ := compose_eq.mp hc
      refine ⟨s₁.m, s₂.m, rfl, ?_, ?_⟩
      · have := (ih₁ n hwf.1 s₁ (hs₁.trans ht)).mpr h₁
        rw [e2] at this; exact this
      · have := (ih₂ n hwf.2 s₂ (hs₂.trans ht)).mpr h₂
        rw [e1] at this; exact this
  | star r b ihr ihb =>
    simp only [N, sem]
    exact star_N _ _ _ _ n (fun t ht => ihr n hwf.1 t ht) (fun t ht => ihb n hwf.2 t ht) (N_sum b n hwf.2) t ht
  | lb r ih =>
    simp [N, sem, List.mem_filterMap, nullable_lookbehind]
    constructor
    · rintro ⟨hm, h⟩
      refine ⟨⟨0, t.lb, t.la⟩, (ih n hwf ⟨0, t.lb, t.la⟩ (by simp [Steps.stepsSum] at *; omega)).mp h, ?_⟩
      obtain ⟨_, _, _⟩ := t; simp_all
    · rintro ⟨s, hs, ⟨_, h⟩⟩
      subst h
      refine ⟨rfl, ?_⟩
      have := (ih n hwf s (by simp [Steps.stepsSum] at *; omega)).mpr hs
      obtain ⟨_, _, _⟩ := s; simp_all [nullable]
  | la r ih =>
    simp [N, sem, List.mem_filterMap, nullable_lookahead]
    constructor
    · rintro ⟨hm, h⟩
      refine ⟨⟨t.lb, t.la, 0⟩, (ih n hwf ⟨t.lb, t.la, 0⟩ (by simp [Steps.stepsSum] at *; omega)).mp h, ?_⟩
      obtain ⟨_, _, _⟩ := t; simp_all
    · rintro ⟨s, hs, ⟨_, h⟩ ⟩
      subst h
      refine ⟨rfl, ?_⟩
      have := (ih n hwf s (by simp [Steps.stepsSum] at *; omega)).mpr hs
      obtain ⟨_, _, _⟩ := s; simp_all [nullable]




end Nullability

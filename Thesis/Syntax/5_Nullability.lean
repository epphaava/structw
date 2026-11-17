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
open Steps

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
  | .star r b => starN (N r) (max (Steps.maxSum (N r)) (Steps.maxSum (N b)) + 1) (N b)
  | .lb r => (N r).map fun s => ⟨0, s.la⟩
  | .la r => (N r).filterMap fun s => if s.la = 0 then some ⟨0, s.m⟩ else none


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

theorem N_sum {α} (r : SRegex α) (n : Nat) (hwf : WF r n) : ∀ t ∈ N r, t.stepsSum ≤ n := by
  induction r with
  | empty => simp [N]
  | unit ss | top ss => exact hwf
  | symbol _ _ => simp [N]
  | plus r₁ r₂ ih₁ ih₂ =>
    intro t ht
    rcases List.mem_append.mp ht with ht | ht
    · exact ih₁ hwf.1 t ht
    · exact ih₂ hwf.2 t ht
  | intersection r₁ r₂ ih₁ _ | complement r₁ r₂ ih₁ _ => intro t ht; exact ih₁ hwf.1 t (List.mem_filter.mp ht).1
  | mult r₁ r₂ ih₁ _ =>
    intro t ht
    obtain ⟨s₁, h₁, s₂, _, hc⟩ := mem_concatN.mp ht
    have hsum := (compose_sum hc).1
    have hn := ih₁ hwf.1 s₁ h₁
    exact hsum ▸ hn
  | star r b ihr ihb =>
    apply starN_induct _ (fun t => t.stepsSum ≤ n)
    · intro s₁ s₂ t h₁ _ hc; exact (compose_sum hc).1 ▸ ihr hwf.1 s₁ h₁
    · exact ihb hwf.2
  | lb r ih =>
    intro t ht
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
    have := ih hwf.1 s hs; simp [Steps.stepsSum, Nat.add_eq] at *; omega
  | la r ih =>
    intro t ht
    simp only [N, List.mem_filterMap] at ht
    obtain ⟨s, hs, h⟩ := ht
    split at h <;> simp at h
    have := ih hwf s hs; subst h; simp [Steps.stepsSum, Nat.add_eq] at *; omega

mutual
theorem N_full {α} (r : SRegex α) (n : Nat) (h : Full r n) : ∀ t ∈ N r, t.stepsSum = n := by
  match r, n, h with
  | .empty, _, _ => simp [N]
  | .unit _, _, h | .top _, _, h => exact h
  | .symbol _ _, _, _ => simp [N]
  | .plus r₁ r₂, n, h =>
    intro t ht
    rcases List.mem_append.mp ht with ht | ht
    · exact N_full r₁ n h.1 t ht
    · exact N_full r₂ n h.2 t ht
  | .intersection r₁ _, n, h | .complement r₁ _, n, h => intro t ht; exact N_full r₁ n h.1 t (List.mem_filter.mp ht).1
  | .mult r₁ _, n, h =>
    intro t ht
    obtain ⟨s₁, h₁, s₂, _, hc⟩ := mem_concatN.mp ht
    exact (compose_sum hc).1 ▸ N_full r₁ n h s₁ h₁
  | .star r b, n, h =>
    apply starN_induct _ (fun t => t.stepsSum = n)
    · intro s₁ s₂ t h₁ _ hc; exact (compose_sum hc).1 ▸ N_full r n h.1 s₁ h₁
    · exact N_full b n h.2
  | .lb r, n, h =>
    intro t ht
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
    have := (N_laOnly r n h s hs).2
    simp [Steps.stepsSum, Nat.add_eq]; exact this
  | .la r, n, h =>
    intro t ht
    simp only [N, List.mem_filterMap] at ht
    obtain ⟨s, hs, hst⟩ := ht
    split at hst <;> simp at hst
    have := N_full r n h s hs; subst hst; simp [Steps.stepsSum, Nat.add_eq] at *; omega

theorem N_laOnly {α} (r : SRegex α) (n : Nat) (h : LAOnly r n) : ∀ t ∈ N r, t.m = 0 ∧ t.la = n := by
  match r, n, h with
  | .empty, _, _ => simp [N]
  | .unit _, _, h | .top _, _, h => exact h
  | .symbol _ _, _, _ => simp [N]
  | .plus r₁ r₂, n, h =>
    intro t ht
    rcases List.mem_append.mp ht with ht | ht
    · exact N_laOnly r₁ n h.1 t ht
    · exact N_laOnly r₂ n h.2 t ht
  | .intersection r₁ _, n, h | .complement r₁ _, n, h => intro t ht; exact N_laOnly r₁ n h.1 t (List.mem_filter.mp ht).1
  | .mult r₁ r₂, n, h =>
    intro t ht
    obtain ⟨s₁, h₁, s₂, h₂, hc⟩ := mem_concatN.mp ht
    obtain ⟨e, rfl⟩ := compose_eq.mp hc
    have := N_laOnly r₁ n h.1 s₁ h₁; have := N_laOnly r₂ n h.2 s₂ h₂
    simp; omega
  | .star r b, n, h =>
    apply starN_induct _ (fun t => t.m = 0 ∧ t.la = n)
    · intro s₁ s₂ t h₁ h₂ hc
      obtain ⟨e, rfl⟩ := compose_eq.mp hc
      have := N_laOnly r n h.1 s₁ h₁
      simp only; omega
    · exact N_laOnly b n h.2
  | .lb r, n, h =>
    intro t ht
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
    exact ⟨rfl, (N_laOnly r n h s hs).2⟩
  | .la r, n, h =>
    intro t ht
    simp only [N, List.mem_filterMap] at ht
    obtain ⟨s, hs, hst⟩ := ht
    split at hst <;> simp at hst
    have := N_full r n h s hs; subst hst
    refine ⟨rfl, ?_⟩
    simp [Steps.stepsSum, Nat.add_eq] at this ⊢; omega
end


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

variable {α : Type} [DecidableEq α]


theorem N_correct (r : SRegex α) (n : Nat) (hwf : WF r n) (t : Steps) (ht : t.stepsSum ≤ n) :
    nullable (sem r n) (lbOf n t) t.m t.la ↔ t ∈ N r := by
  induction r generalizing t with
  | empty => simp [nullable, sem, N, empty]
  | unit ss =>
    simp [nullable, sem, atom_iff]
    constructor
    . intro ⟨s, hs, h⟩
      have := hwf s hs
      simp [sem.steps, unit, lbOf, stepsSum] at h ht this
      obtain ⟨s_m, s_la⟩ := s; obtain ⟨t_m, t_la⟩ := t; simp at *
      obtain rfl : t_m = s_m := by omega
      obtain rfl : t_la = s_la := by omega
      exact hs
    . intro h; exact ⟨t, h, by simp [sem.steps, unit, lbOf, stepsSum]⟩
  | top ss =>
    simp [nullable, sem, atom_iff]
    constructor
    . intro ⟨s, hs, h⟩
      have := hwf s hs
      simp [sem.steps, top, lbOf, stepsSum] at h ht this
      obtain ⟨s_m, s_la⟩ := s; obtain ⟨t_m, t_la⟩ := t; simp at *
      obtain rfl : t_m = s_m := by omega
      obtain rfl : t_la = s_la := by omega
      exact hs
    . intro h; exact ⟨t, h, by simp [sem.steps, top, lbOf, stepsSum]⟩
  | symbol b ss => simp [nullable, sem, atom_iff, sem.steps, N]
  | plus r₁ r₂ ih₁ ih₂ => simp [sem, N]; exact nullable_union.trans (or_congr (ih₁ hwf.1 t ht) (ih₂ hwf.2 t ht))
  | intersection r₁ r₂ ih₁ ih₂ => simp [sem, N]; exact nullable_intersection.trans (and_congr (ih₁ hwf.1 t ht) (ih₂ hwf.2 t ht))
  | complement r₁ r₂ ih₁ ih₂ => simp [sem, N]; exact nullable_diff.trans (and_congr (ih₁ hwf.1 t ht) (not_congr (ih₂ hwf.2 t ht)))
  | mult r₁ r₂ ih₁ ih₂ =>
    simp [sem, N, nullable_concat, mem_concatN]
    simp [stepsSum] at ht
    constructor
    . intro ⟨mc₁, mc₂, hmc, h₁, h₂⟩
      let s₁ : Steps := ⟨mc₁, mc₂ + t.la⟩
      let s₂ : Steps := ⟨mc₂, t.la⟩
      have hs₁ : s₁.stepsSum ≤ n := by simp [s₁, stepsSum]; omega
      have hs₂ : s₂.stepsSum ≤ n := by simp [s₂, stepsSum]; omega
      have hlb₁ : (n - (t.m + t.la)) = lbOf n s₁ := by simp [lbOf, s₁, stepsSum]; omega;
      simp [lbOf, stepsSum, hlb₁] at h₁
      have hlb₂ : ((n - (t.m + t.la)) + mc₁) = lbOf n s₂ := by simp [lbOf, s₂, stepsSum]; omega
      simp [lbOf, stepsSum, hlb₂] at h₂
      obtain ⟨_, _⟩ := t
      exact ⟨s₁, (ih₁ hwf.1 s₁ hs₁).mp h₁, s₂, (ih₂ hwf.2 s₂ hs₂).mp h₂, by simp [compose, s₁, s₂] at ⊢ hmc; exact hmc.symm⟩
    . intro ⟨s₁, h₁, s₂, h₂, hc⟩
      obtain ⟨hs₁, hs₂⟩ := compose_sum hc
      obtain ⟨hsla₁, rfl⟩ := compose_eq.mp hc
      simp [Steps.stepsSum, Nat.add_eq] at hs₁ hs₂ ht
      refine ⟨s₁.m, s₂.m, rfl, ?_, ?_⟩
      . have ih₁ := (ih₁ hwf.1 s₁ (by simp [Steps.stepsSum]; omega)).mpr h₁
        have : lbOf n s₁ = (n - ((s₁.m + s₂.m) + s₂.la)) := by simp [lbOf, stepsSum]; omega
        rw [this, hsla₁] at ih₁; exact ih₁
      . have ih₂ := (ih₂ hwf.2 s₂ (by simp [Steps.stepsSum]; omega)).mpr h₂
        have : lbOf n s₂ = ((n - ((s₁.m + s₂.m) + s₂.la)) + s₁.m) := by simp [lbOf, stepsSum]; omega
        rw [this] at ih₂; exact ih₂
  | star r b ihr ihb => simp [N, sem]; exact star_N _ _ _ _ n (fun t ht => ihr hwf.1 t ht) (fun t ht => ihb hwf.2 t ht) (N_sum r n hwf.1) t ht
  | lb r ih =>
    simp [sem, N, nullable_lookbehind]
    constructor
    . intro ⟨hm, h⟩
      let s : Steps := ⟨lbOf n t, t.la⟩
      have : lbOf n s = 0 := by simp [s, lbOf, Steps.stepsSum] at ht ⊢; omega
      obtain ⟨_, _⟩ := t
      exact ⟨s, (ih hwf.1 s (by simp [s, lbOf, stepsSum] at ⊢ ht; omega)).mp (by simp [nullable, this]; exact h), by simp at hm; subst hm; rfl⟩
    . rintro ⟨s, hs, rfl⟩
      have hsum := N_full r n hwf.2 s hs
      have hs' := (ih hwf.1 s (by omega)).mpr hs
      have e₁ : lbOf n s = 0 := by simp only [lbOf]; omega
      have e₂ : lbOf n ⟨0, s.la⟩ = s.m := by simp only [lbOf, Steps.stepsSum, Nat.add_eq] at hsum ⊢; omega
      simp [nullable, e₁] at hs'
      rw [e₂]; simp; exact hs'
  | la r ih =>
    simp [sem, N, nullable_lookahead]
    constructor
    . intro ⟨hm, h⟩; let s : Steps := ⟨t.la, 0⟩;
      exact ⟨s, (ih hwf s (by simp [s, stepsSum] at ht ⊢; omega)).mp (by simp [nullable, s, lbOf, stepsSum, hm] at ⊢ h; exact h), by obtain ⟨_, _⟩ := t; simp at hm; simp [hm, s]⟩
    . rintro ⟨⟨sm, sla⟩, hs, ⟨hla, rfl⟩⟩; simp at hla ⊢; subst hla
      have := (ih hwf ⟨sm, 0⟩ (N_sum r n hwf ⟨sm, 0⟩ hs)).mpr hs
      simp [nullable, lbOf, stepsSum] at ⊢ this; exact this

end Nullability

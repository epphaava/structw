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


def N {α} (r : SRegex α) (n : Nat) : List Steps :=
  match r with
  | .empty => []
  | .unit ss => ss
  | .top ss => ss
  | .symbol _ _ => []
  | .plus r₁ r₂ => N r₁ n ++ N r₂ n
  | .intersection r₁ r₂ => (N r₁ n).filter fun s => (N r₂ n).contains s
  | .complement r₁ r₂ => (N r₁ n).filter fun s => !(N r₂ n).contains s
  | .mult r₁ r₂ => concatN (N r₁ n) (N r₂ n)
  | .star r b => starN (N r n) (n + 1) (N b n)
  | .lb r => (N r n).filterMap fun s => if s.stepsSum = n then some ⟨0, s.la⟩ else none
  | .la r => (N r n).filterMap fun s => if s.la = 0 then some ⟨0, s.m⟩ else none

/-- Every step in `r` fits in the `n` characters read so far. -/
def ssLe {α} : SRegex α → Nat → Prop
  | .empty, _ => True
  | .unit ss, n | .top ss, n | .symbol _ ss, n => ∀ s ∈ ss, s.stepsSum ≤ n
  | .plus r₁ r₂, n | .intersection r₁ r₂, n | .complement r₁ r₂, n
  | .mult r₁ r₂, n | .star r₁ r₂, n => ssLe r₁ n ∧ ssLe r₂ n
  | .lb r, n | .la r, n => ssLe r n


theorem compose_eq {s₁ s₂ t : Steps} : compose s₁ s₂ = some t ↔ s₁.la = s₂.m + s₂.la ∧ t = ⟨s₁.m + s₂.m, s₂.la⟩ := by
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

theorem N_sum {α} (r : SRegex α) (n : Nat) (hwf : ssLe r n) : ∀ t ∈ N r n, t.stepsSum ≤ n := by
  induction r with
  | empty => simp [N]
  | unit ss | top ss => exact hwf
  | symbol _ _ => simp [N]
  | plus r₁ r₂ ih₁ ih₂ =>
    intro t ht
    rcases List.mem_append.mp ht with ht | ht
    · exact ih₁ hwf.1 t ht
    · exact ih₂ hwf.2 t ht
  | intersection r₁ r₂ ih₁ _ | complement r₁ r₂ ih₁ _ =>
    intro t ht; exact ih₁ hwf.1 t (List.mem_filter.mp ht).1
  | mult r₁ r₂ ih₁ _ =>
    intro t ht
    obtain ⟨s₁, h₁, s₂, _, hc⟩ := mem_concatN.mp ht
    exact (compose_sum hc).1 ▸ ih₁ hwf.1 s₁ h₁
  | star r b ihr ihb =>
    apply starN_induct _ (fun t => t.stepsSum ≤ n)
    · intro s₁ s₂ t h₁ _ hc; exact (compose_sum hc).1 ▸ ihr hwf.1 s₁ h₁
    · exact ihb hwf.2
  | lb r ih =>
    intro t ht
    simp only [N, List.mem_filterMap] at ht
    obtain ⟨s, hs, h⟩ := ht
    split at h <;> simp at h
    have := ih hwf s hs; subst h; simp only [Steps.stepsSum, Nat.add_eq] at *; omega
  | la r ih =>
    intro t ht
    simp only [N, List.mem_filterMap] at ht
    obtain ⟨s, hs, h⟩ := ht
    split at h <;> simp at h
    have := ih hwf s hs; subst h; simp only [Steps.stepsSum, Nat.add_eq] at *; omega


/-- The lookbehind count of a pair is whatever the match and lookahead leave of `n`. -/
abbrev lbOf (n : Nat) (t : Steps) : Nat := n - t.stepsSum

theorem star_N {α : Type} (l base : Lang α) (nr nb : List Steps) (n : Nat)
    (hr : ∀ t : Steps, t.stepsSum ≤ n → (nullable l (lbOf n t) t.m t.la ↔ t ∈ nr))
    (hb : ∀ t : Steps, t.stepsSum ≤ n → (nullable base (lbOf n t) t.m t.la ↔ t ∈ nb))
    (hnr : ∀ t ∈ nr, t.stepsSum ≤ n) (t : Steps) (ht : t.stepsSum ≤ n) :
    nullable (star l base) (lbOf n t) t.m t.la ↔ t ∈ starN nr (n + 1) nb := by
  constructor
  · intro h
    suffices key : ∀ w, star_help l base w → ∀ t : Steps, w = .right (lbOf n t) t.m t.la [] →
        t.stepsSum ≤ n → t ∈ starN nr t.m nb by
      exact starN_mono nr (by simp only [Steps.stepsSum, Nat.add_eq] at ht; omega) nb (key _ h t rfl ht)
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
      simp only [lbOf, Steps.stepsSum, Nat.add_eq] at ht h₁ ih
      let s₁ : Steps := ⟨mc₁, mc₂ + t.la⟩
      let s₂ : Steps := ⟨mc₂, t.la⟩
      have hc : compose s₁ s₂ = some t := by
        rw [compose_eq]; obtain ⟨_, _⟩ := t; simp_all [s₁, s₂]
      have h₂ : s₂ ∈ starN nr s₂.m nb :=
        ih s₂ (by simp only [s₂, Word.right.injEq, and_true]; omega) (by simp only [s₂]; omega)
      have hs₁ : s₁ ∈ nr := by
        refine (hr s₁ (by simp only [s₁, Steps.stepsSum, Nat.add_eq]; omega)).mp ?_
        have e : (n - (t.m + t.la)) = (n - (s₁.m + s₁.la)) := by simp only [s₁]; omega
        simp only [nullable, lbOf, Steps.stepsSum, Nat.add_eq]; rw [← e]; exact h₁
      by_cases hz : mc₁ = 0
      · rw [compose_m_zero hc hz]
        exact starN_mono nr (by simp only [s₂]; omega) nb h₂
      · exact starN_mono nr (by simp only [s₂]; omega) nb (starN_compose nr _ nb hs₁ h₂ hc)
  · intro hmem
    refine starN_induct nr (fun t => t.stepsSum ≤ n → nullable (star l base) (lbOf n t) t.m t.la) ?_ _ nb ?_ t hmem ht
    · intro s₁ s₂ t h₁ h₂ hc ht
      have hs₁ := hnr s₁ h₁
      obtain ⟨e1, rfl⟩ := compose_eq.mp hc
      simp only [Steps.stepsSum, Nat.add_eq] at ht hs₁
      refine (nullable_star l base).mpr (.inr ⟨s₁.m, s₂.m, rfl, ?_, ?_⟩)
      · have := (hr s₁ (by simp only [Steps.stepsSum, Nat.add_eq]; omega)).mpr h₁
        have e : lbOf n s₁ = (n - ((s₁.m + s₂.m) + s₂.la)) := by
          simp only [lbOf, Steps.stepsSum, Nat.add_eq]; omega
        simp only [lbOf, Steps.stepsSum, Nat.add_eq] at this e ⊢
        rw [e, e1] at this; exact this
      · have := h₂ (by simp only [Steps.stepsSum, Nat.add_eq]; omega)
        have e : lbOf n s₂ = ((n - ((s₁.m + s₂.m) + s₂.la)) + s₁.m) := by
          simp only [lbOf, Steps.stepsSum, Nat.add_eq]; omega
        simp only [lbOf, Steps.stepsSum, Nat.add_eq] at this e ⊢
        rw [e] at this; exact this
    · intro t ht hn
      exact (nullable_star l base).mpr (.inl ((hb t hn).mpr ht))

variable {α : Type} [DecidableEq α]

/-- Nullability is computed exactly by `N`, for steps that fit in the `n` characters read. -/
theorem N_correct (r : SRegex α) (n : Nat) (hwf : ssLe r n) (t : Steps) (ht : t.stepsSum ≤ n) :
    nullable (sem r n) (lbOf n t) t.m t.la ↔ t ∈ N r n := by
  induction r generalizing t with
  | empty => simp [nullable, sem, N, empty]
  | unit ss =>
    simp only [nullable, sem, N, atom_iff]
    constructor
    · rintro ⟨s, hs, h⟩
      have hs' := hwf s hs
      simp only [sem.steps, unit, lbOf, Steps.stepsSum, Nat.add_eq, Nat.sub_eq] at h hs' ht
      obtain ⟨s_m, s_la⟩ := s; obtain ⟨t_m, t_la⟩ := t
      simp only at *
      obtain rfl : t_m = s_m := by omega
      obtain rfl : t_la = s_la := by omega
      exact hs
    · intro h
      exact ⟨t, h, by simp [sem.steps, unit, lbOf, Steps.stepsSum]⟩
  | top ss =>
    simp only [nullable, sem, N, atom_iff]
    constructor
    · rintro ⟨s, hs, h⟩
      have hs' := hwf s hs
      simp only [sem.steps, top, lbOf, Steps.stepsSum, Nat.add_eq, Nat.sub_eq, and_true] at h hs' ht
      obtain ⟨s_m, s_la⟩ := s; obtain ⟨t_m, t_la⟩ := t
      simp only at *
      obtain rfl : t_m = s_m := by omega
      obtain rfl : t_la = s_la := by omega
      exact hs
    · intro h
      exact ⟨t, h, by simp [sem.steps, top, lbOf, Steps.stepsSum]⟩
  | symbol b ss => simp [nullable, sem, N, atom_iff, sem.steps]
  | plus r₁ r₂ ih₁ ih₂ =>
    simp only [sem, N, List.mem_append]
    exact (nullable_union).trans (or_congr (ih₁ hwf.1 t ht) (ih₂ hwf.2 t ht))
  | intersection r₁ r₂ ih₁ ih₂ =>
    simp only [sem, N, List.mem_filter, List.contains_iff_mem]
    exact (nullable_intersection).trans (and_congr (ih₁ hwf.1 t ht) (ih₂ hwf.2 t ht))
  | complement r₁ r₂ ih₁ ih₂ =>
    simp [sem, N, List.mem_filter, ← Bool.not_eq_true]
    exact (nullable_diff).trans (and_congr (ih₁ hwf.1 t ht) (not_congr (ih₂ hwf.2 t ht)))
  | mult r₁ r₂ ih₁ ih₂ =>
    simp only [sem, N, nullable_concat, mem_concatN]
    simp only [lbOf, Steps.stepsSum, Nat.add_eq] at ht ⊢
    constructor
    · rintro ⟨mc₁, mc₂, hmc, h₁, h₂⟩
      let s₁ : Steps := ⟨mc₁, mc₂ + t.la⟩
      let s₂ : Steps := ⟨mc₂, t.la⟩
      have hs₁ : s₁.stepsSum ≤ n := by simp only [s₁, Steps.stepsSum, Nat.add_eq]; omega
      have hs₂ : s₂.stepsSum ≤ n := by simp only [s₂, Steps.stepsSum, Nat.add_eq]; omega
      have e₁ : (n - (t.m + t.la)) = lbOf n s₁ := by simp only [lbOf, s₁, Steps.stepsSum, Nat.add_eq]; omega
      have e₂ : ((n - (t.m + t.la)) + mc₁) = lbOf n s₂ := by simp only [lbOf, s₂, Steps.stepsSum, Nat.add_eq]; omega
      rw [e₁] at h₁; rw [e₂] at h₂
      refine ⟨s₁, (ih₁ hwf.1 s₁ hs₁).mp h₁, s₂, (ih₂ hwf.2 s₂ hs₂).mp h₂, ?_⟩
      rw [compose_eq]; obtain ⟨_, _⟩ := t; simp_all [s₁, s₂]
    · rintro ⟨s₁, h₁, s₂, h₂, hc⟩
      obtain ⟨hs₁, hs₂⟩ := compose_sum hc
      obtain ⟨e1, rfl⟩ := compose_eq.mp hc
      simp only [Steps.stepsSum, Nat.add_eq] at hs₁ hs₂ ht
      refine ⟨s₁.m, s₂.m, rfl, ?_, ?_⟩
      · have := (ih₁ hwf.1 s₁ (by simp only [Steps.stepsSum, Nat.add_eq]; omega)).mpr h₁
        have e : lbOf n s₁ = (n - ((s₁.m + s₂.m) + s₂.la)) := by simp only [lbOf, Steps.stepsSum, Nat.add_eq]; omega
        rw [e, e1] at this; exact this
      · have := (ih₂ hwf.2 s₂ (by simp only [Steps.stepsSum, Nat.add_eq]; omega)).mpr h₂
        have e : lbOf n s₂ = ((n - ((s₁.m + s₂.m) + s₂.la)) + s₁.m) := by simp only [lbOf, Steps.stepsSum, Nat.add_eq]; omega
        rw [e] at this; exact this
  | star r b ihr ihb =>
    simp only [N, sem]
    exact star_N _ _ _ _ n (fun t ht => ihr hwf.1 t ht) (fun t ht => ihb hwf.2 t ht) (N_sum r n hwf.1) t ht
  | lb r ih =>
    simp only [sem, N, List.mem_filterMap, nullable_lookbehind]
    constructor
    · rintro ⟨hm, h⟩
      -- the content's match is the whole lookbehind: the pair `(n - la, la)`
      let s : Steps := ⟨lbOf n t, t.la⟩
      have hs : s.stepsSum ≤ n := by simp only [s, lbOf, Steps.stepsSum, Nat.add_eq] at ht ⊢; omega
      have e : lbOf n s = 0 := by simp only [s, lbOf, Steps.stepsSum, Nat.add_eq] at ht ⊢; omega
      refine ⟨s, (ih hwf s hs).mp (by simp only [nullable, e]; exact h), ?_⟩
      have hsum : s.stepsSum = n := by
        simp only [s, lbOf, Steps.stepsSum, Nat.add_eq] at ht ⊢; omega
      rw [if_pos hsum]
      obtain ⟨t_m, t_la⟩ := t; simp only at hm; subst hm; rfl
    · rintro ⟨s, hs, h⟩
      split at h <;> simp at h
      rename_i hsum
      subst h
      have hs' := (ih hwf s (by omega)).mpr hs
      refine ⟨rfl, ?_⟩
      have e₁ : lbOf n s = 0 := by simp only [lbOf]; omega
      have e₂ : lbOf n ⟨0, s.la⟩ = s.m := by simp only [lbOf, Steps.stepsSum, Nat.add_eq] at hsum ⊢; omega
      simp only [nullable, e₁] at hs'
      rw [e₂]; exact hs'
  | la r ih =>
    simp only [sem, N, List.mem_filterMap, nullable_lookahead]
    constructor
    · rintro ⟨hm, h⟩
      -- the content's match is the outer lookahead: the pair `(la, 0)`
      let s : Steps := ⟨t.la, 0⟩
      have hs : s.stepsSum ≤ n := by simp only [s, Steps.stepsSum, Nat.add_eq] at ht ⊢; omega
      have e : lbOf n s = lbOf n t := by simp only [s, lbOf, Steps.stepsSum, Nat.add_eq]; omega
      refine ⟨s, (ih hwf s hs).mp (by simp only [nullable, e]; exact h), ?_⟩
      obtain ⟨t_m, t_la⟩ := t; simp only at hm; subst hm; simp [s]
    · rintro ⟨s, hs, h⟩
      split at h <;> simp at h
      rename_i hla
      subst h
      have hs' := (ih hwf s (N_sum r n hwf s hs)).mpr hs
      refine ⟨rfl, ?_⟩
      have e : lbOf n s = lbOf n ⟨0, s.m⟩ := by simp only [lbOf, Steps.stepsSum, Nat.add_eq, hla]; omega
      simp only [nullable] at hs'
      obtain ⟨s_m, s_la⟩ := s; simp only at hla e hs' ⊢; subst hla
      rw [← e]; exact hs'

end Nullability

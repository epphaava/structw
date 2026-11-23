import Thesis.Syntax.«1_Expressions»
import Thesis.Syntax.«2_Derivatives»
import Thesis.Syntax.Helpers.«3_DerivativeCorrectness»
import Thesis.Semantics.kLang.«9_NullabilityLaws»
import Thesis.Syntax.Helpers.«4_Nullability»


namespace Nullability

open SRegex
open StructuredWords
open kStructuredWords
open kOperators
open NullabilityLaws
open DerCorrectHelpers
open SRegexDerivatives
open Steps
open NullabilityHelpers




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


variable {α : Type} [DecidableEq α]


theorem N_correct (r : SRegex α) (n : Nat) (hwf : WF r n) (t : Steps) (ht : t.stepsSum ≤ n) :
    nullable (sem r n) t.m t.la ↔ t ∈ N r := by
  induction r generalizing t with
  | empty => simp [nullable, sem, N, kOperators.empty, Operators.empty]
  | unit ss =>
    obtain ⟨tm, tla⟩ := t
    simp only [nullable, sem, atom_iff, N]
    constructor
    . rintro ⟨_, ⟨sm, sla⟩, hs, h⟩
      simp [sem.steps, Operators.unit, Word.word_steps] at h
      obtain rfl : tm = sm := by omega
      obtain rfl : tla = sla := by omega
      exact hs
    . intro h; exact ⟨ht, _, h, by simp [sem.steps, Operators.unit, Word.word_steps]⟩
  | top ss =>
    obtain ⟨tm, tla⟩ := t
    simp only [nullable, sem, atom_iff, N]
    constructor
    . rintro ⟨_, ⟨sm, sla⟩, hs, h⟩
      simp [sem.steps, Operators.top, Word.word_steps] at h
      obtain rfl : tm = sm := by omega
      obtain rfl : tla = sla := by omega
      exact hs
    . intro h; exact ⟨ht, _, h, by simp [sem.steps, Operators.top, Word.word_steps]⟩
  | symbol b ss => simp [nullable, sem, atom_iff, sem.steps, N, Operators.symb]
  | plus r₁ r₂ ih₁ ih₂ =>
    simp only [sem, N, List.mem_append]
    exact (nullable_union _ _).trans (or_congr (ih₁ hwf.1 t ht) (ih₂ hwf.2 t ht))
  | intersection r₁ r₂ ih₁ ih₂ =>
    simp only [sem, N, List.mem_filter, List.contains_iff_mem]
    exact (nullable_intersection _ _).trans (and_congr (ih₁ hwf.1 t ht) (ih₂ hwf.2 t ht))
  | complement r₁ r₂ ih₁ ih₂ =>
    simp [sem, N]
    exact (nullable_diff _ _).trans (and_congr (ih₁ hwf.1 t ht) (not_congr (ih₂ hwf.2 t ht)))
  | mult r₁ r₂ ih₁ ih₂ =>
    simp only [sem, N, nullable_concat, mem_concatN]
    simp only [stepsSum, Nat.add_eq] at ht
    constructor
    . intro ⟨mc₁, mc₂, hmc, h₁, h₂⟩
      let s₁ : Steps := ⟨mc₁, mc₂ + t.la⟩
      let s₂ : Steps := ⟨mc₂, t.la⟩
      have hs₁ : s₁.stepsSum ≤ n := by simp [s₁, stepsSum]; omega
      have hs₂ : s₂.stepsSum ≤ n := by simp [s₂, stepsSum]; omega
      obtain ⟨_, _⟩ := t
      exact ⟨s₁, (ih₁ hwf.1 s₁ hs₁).mp h₁, s₂, (ih₂ hwf.2 s₂ hs₂).mp h₂, by simp [compose, s₁, s₂] at ⊢ hmc; exact hmc.symm⟩
    . intro ⟨s₁, h₁, s₂, h₂, hc⟩
      obtain ⟨hs₁, hs₂⟩ := compose_sum hc
      obtain ⟨hsla₁, rfl⟩ := compose_eq.mp hc
      simp [Steps.stepsSum] at hs₁ hs₂ ht
      refine ⟨s₁.m, s₂.m, rfl, ?_, (ih₂ hwf.2 s₂ (by simp [Steps.stepsSum]; omega)).mpr h₂⟩
      have ih₁ := (ih₁ hwf.1 s₁ (by simp [Steps.stepsSum]; omega)).mpr h₁
      rw [hsla₁] at ih₁; exact ih₁
  | star r b ihr ihb =>
    simp only [N, sem]
    exact star_N _ _ _ _ (fun t ht => ihr hwf.1 t ht) (fun t ht => ihb hwf.2 t ht) (N_sum r n hwf.1) t ht
  | lb r ih =>
    simp only [sem, N, nullable_lookbehind, List.mem_map]
    constructor
    . intro ⟨hm, lbc, _, h⟩
      have hb := (sem r n).2 _ h
      exact ⟨⟨lbc, t.la⟩, (ih hwf.1 ⟨lbc, t.la⟩ hb).mp h, by obtain ⟨_, _⟩ := t; simp at hm; simp [hm]⟩
    . rintro ⟨s, hs, rfl⟩
      have hsum := N_sum r n hwf.1 s hs
      simp only [Steps.stepsSum, Nat.add_eq] at hsum
      exact ⟨rfl, s.m, by omega, (ih hwf.1 s (N_sum r n hwf.1 s hs)).mpr hs⟩
  | la r ih =>
    simp only [sem, N, nullable_lookahead, List.mem_filterMap]
    constructor
    . intro ⟨hm, h⟩
      let s : Steps := ⟨t.la, 0⟩
      have hs : s.stepsSum ≤ n := by simp [s, stepsSum] at ht ⊢; omega
      exact ⟨s, (ih hwf s hs).mp h, by obtain ⟨_, _⟩ := t; simp at hm; simp [hm, s]⟩
    . rintro ⟨⟨sm, sla⟩, hs, h⟩
      split at h <;> simp at h
      rename_i hla; simp at hla; subst hla h
      exact ⟨rfl, (ih hwf ⟨sm, 0⟩ (N_sum r n hwf ⟨sm, 0⟩ hs)).mpr hs⟩

end Nullability

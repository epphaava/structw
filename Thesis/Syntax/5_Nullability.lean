import Thesis.Syntax.«1_Expressions»
import Thesis.Syntax.«2_Derivatives»
import Thesis.Syntax.Helpers.«4_DerivativeCorrectness»
import Thesis.Semantics.«9_NullabilityLaws»
import Thesis.Syntax.Helpers.«5_Nullability»


namespace Nullability

open SRegex
open StructuredWords
open Operators
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

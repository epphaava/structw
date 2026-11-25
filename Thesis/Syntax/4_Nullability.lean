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
open kDerivatives
open kNullabilityLaws
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
  | .lb r => (N r).map λ s => ⟨0, s.la⟩
  | .la r => (N r).filterMap λ s => if s.la = 0 then some ⟨0, s.m⟩ else none


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
    exact (compose_sum hc).1 ▸ ih₁ hwf.1 s₁ h₁
  | star r b ihr ihb =>
    apply starN_induct _ (λ t => t.stepsSum ≤ n)
    · intro s₁ s₂ t h₁ _ hc; exact (compose_sum hc).1 ▸ ihr hwf.1 s₁ h₁
    · exact ihb hwf.2
  | lb r ih =>
    intro t ht
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
    have := ih hwf s hs; simp [stepsSum] at *; omega
  | la r ih =>
    intro t ht
    simp only [N, List.mem_filterMap] at ht
    obtain ⟨s, hs, h⟩ := ht
    split at h <;> simp at h
    have := ih hwf s hs; subst h; simp [Steps.stepsSum, Nat.add_eq] at *; omega





theorem N_correct [DecidableEq α] (r : SRegex α) (n : Nat) (hwf : WF r n) (ss : Steps) : nullable (sem r n) ss.m ss.la ↔ ss ∈ N r := by
  suffices key : ∀ t : Steps, t.stepsSum ≤ n → (nullable (sem r n) t.m t.la ↔ t ∈ N r) by
    constructor
    · intro h; exact (key ss ((sem r n).2 _ h)).mp h
    · intro h; exact (key ss (N_sum r n hwf ss h)).mpr h
  induction r with
  | empty => simp [nullable, sem, N, empty, Operators.empty]
  | unit ss =>
    intro ⟨ssm, ssla⟩ hss
    constructor
    . intro ⟨_, ⟨tm, tla⟩, ht, h⟩
      simp [sem.steps, Operators.unit, word_steps] at h
      obtain rfl : ssm = tm := by omega
      obtain rfl : ssla = tla := by omega
      exact ht
    . intro h; exact ⟨hss, _, h, by simp [sem.steps, Operators.unit, word_steps]⟩
  | top ss =>
    intro ⟨ssm, ssla⟩ hss
    constructor
    . intro ⟨_, ⟨tm, tla⟩, ht, h⟩
      simp [sem.steps, Operators.top, word_steps] at h
      obtain rfl : ssm = tm := by omega
      obtain rfl : ssla = tla := by omega
      exact ht
    . intro h; exact ⟨hss, _, h, by simp [sem.steps, Operators.top, word_steps]⟩
  | symbol b ss => intro _ _; simp [nullable, sem, atom_iff, sem.steps, N, Operators.symb]
  | plus r₁ r₂ ih₁ ih₂ =>
    intro ss hss
    simp [sem, N]
    exact (nullable_union _ _).trans (or_congr (ih₁ hwf.1 ss hss) (ih₂ hwf.2 ss hss))
  | intersection r₁ r₂ ih₁ ih₂ =>
    intro ss hss
    simp [sem, N]
    exact (nullable_intersection _ _).trans (and_congr (ih₁ hwf.1 ss hss) (ih₂ hwf.2 ss hss))
  | complement r₁ r₂ ih₁ ih₂ =>
    intro ss hss
    simp [sem, N]
    exact (nullable_diff _ _).trans (and_congr (ih₁ hwf.1 ss hss) (not_congr (ih₂ hwf.2 ss hss)))
  | mult r₁ r₂ ih₁ ih₂ =>
    intro ss hss
    simp [sem, N, nullable_concat, mem_concatN]
    simp [stepsSum] at hss
    constructor
    . intro ⟨mc₁, mc₂, hmc, h₁, h₂⟩
      let s₁ : Steps := ⟨mc₁, mc₂ + ss.la⟩
      let s₂ : Steps := ⟨mc₂, ss.la⟩
      have hs₁ : s₁.stepsSum ≤ n := by simp [s₁, stepsSum]; omega
      have hs₂ : s₂.stepsSum ≤ n := by simp [s₂, stepsSum]; omega
      obtain ⟨_, _⟩ := ss
      exact ⟨s₁, (ih₁ hwf.1 s₁ hs₁).mp h₁, s₂, (ih₂ hwf.2 s₂ hs₂).mp h₂, by simp [compose, s₁, s₂] at ⊢ hmc; exact hmc.symm⟩
    . intro ⟨s₁, h₁, s₂, h₂, hc⟩
      obtain ⟨hs₁, hs₂⟩ := compose_sum hc
      obtain ⟨hsla₁, rfl⟩ := compose_eq.mp hc
      simp [stepsSum] at hs₁ hs₂ hss
      refine ⟨s₁.m, s₂.m, rfl, ?_, (ih₂ hwf.2 s₂ (by simp [stepsSum]; omega)).mpr h₂⟩
      have ih₁ := (ih₁ hwf.1 s₁ (by simp [Steps.stepsSum]; omega)).mpr h₁
      rw [hsla₁] at ih₁; exact ih₁
  | star r b ihr ihb =>
    intro ss hss
    simp [N, sem]
    exact star_N _ _ _ _ (fun ss hss => ihr hwf.1 ss hss) (fun ss hss => ihb hwf.2 ss hss) (N_sum r n hwf.1) ss hss
  | lb r ih =>
    intro ss hss
    simp [sem, N, nullable_lookbehind]
    constructor
    . intro ⟨hm, lbc, _, h⟩
      have hb := (sem r n).2 _ h
      exact ⟨⟨lbc, ss.la⟩, (ih hwf ⟨lbc, ss.la⟩ hb).mp h, by obtain ⟨_, _⟩ := ss; simp at hm; simp [hm]⟩
    . rintro ⟨s, hs, rfl⟩
      have hsum := N_sum r n hwf s hs
      exact ⟨rfl, s.m, by simp [stepsSum] at hsum; omega, (ih hwf s (N_sum r n hwf s hs)).mpr hs⟩
  | la r ih =>
    intro ss hss
    simp [sem, N, nullable_lookahead, List.mem_filterMap]
    constructor
    . intro ⟨hm, h⟩
      let t : Steps := ⟨ss.la, 0⟩
      have ht : t.stepsSum ≤ n := by simp [t, stepsSum] at hss ⊢; omega
      exact ⟨t, (ih hwf t ht).mp h, by obtain ⟨_, _⟩ := ss; simp at hm; simp [hm, t]⟩
    . rintro ⟨⟨sm, sla⟩, hs, ⟨hla, hm⟩⟩
      simp at hla hm
      subst hla hm
      exact ⟨rfl, (ih hwf ⟨sm, 0⟩ (N_sum r n hwf ⟨sm, 0⟩ hs)).mpr hs⟩

end Nullability

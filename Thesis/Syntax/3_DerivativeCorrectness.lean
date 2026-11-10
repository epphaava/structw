import Thesis.Syntax.«1_Expressions»
import Thesis.Syntax.«2_Derivatives»
import Thesis.Syntax.«4_DerivativeCorrectHelpers»
import Thesis.Semantics.«3_Derivatives»
import Thesis.Semantics.«5_LookbehindDerivativeLaws»
import Thesis.Semantics.«6_LookaheadDerivativeLaws»
import Thesis.Semantics.«7_DerivativeLaws»

namespace DerCorrect

open SRegex
open SRegexDerivatives

open DerCorrect
open DerLaws
open derLBLaws
open derLALaws
open StructuredWords
open Operators

open DerCorrectHelp

mutual

theorem der_correct {α} [DecidableEq α] (a : α) (r : SRegex α) : der a (sem r) ≐ sem (D a r) := by
  intro w
  match r with
  | .empty => rw [D, sem, der_empty a]
  | .unit ss =>
    simp [D, sem]
    induction ss with
    | nil => exact der_empty a w
    | cons s ss ih =>
      refine (der_union a _ _ w).trans ?_
      simp [union, empty, ih] at ih ⊢
      rcases w with ⟨⟩ | ⟨_ | _, _, _⟩ | ⟨_ | _, _ | _, _⟩ <;> simp [der, sem.steps, unit]
  | .top ss =>
    simp only [D, sem, Steps.mStep, Steps.laStep, complement, atom_map_iff]
    rcases w with ⟨⟩ | ⟨_ | mc, main, la⟩ | ⟨_ | mc, _ | lac, la⟩ <;> simp [der, atom_iff, filterD, sem.steps, Steps.mStepHelp, Steps.laStepHelp, top]
    · exact ⟨fun ⟨s, hs⟩ => ⟨s, by simp_all⟩, fun ⟨s, hs⟩ => ⟨s, by simp_all⟩⟩
    · exact ⟨fun ⟨s, hs⟩ => ⟨s, by simp_all⟩, fun ⟨s, hs⟩ => ⟨s, by simp_all⟩⟩
    · intro s hs h1 h2 _; exact ⟨s, hs, h1, by omega, by omega⟩
  | .symbol b ss =>
    by_cases h : a = b
    · subst h
      simp [D, sem, Steps.mStep, Steps.laStep, complement, atom_map_iff]
      rcases w with ⟨⟩ | ⟨_ | mc, main, la⟩ | ⟨_ | mc, _ | lac, la⟩ <;> simp [der, atom_iff, filterD, sem.steps, Steps.mStepHelp, Steps.laStepHelp, top, unit, toList]
      · exact ⟨fun ⟨s, hs⟩ => ⟨s, by simp_all⟩, fun ⟨s, hs⟩ => ⟨s, by simp_all⟩⟩
      · intro s hs h1 h2 _ _; exact ⟨s, hs, h1, by omega, by omega⟩
    · simp [D, h, sem]; rcases w with ⟨⟩ | ⟨_ | mc, main, la⟩ | ⟨_ | mc, _ | lac, la⟩ <;> simp [der, atom_iff, sem.steps, empty, Ne.symm h]
  | .plus r₁ r₂ => rw [D, SRegex.sem, SRegex.sem, der_union a (SRegex.sem r₁) (SRegex.sem r₂), union, union, der_correct a r₁, der_correct a r₂]
  | .intersection r₁ r₂ => rw [D, SRegex.sem, SRegex.sem, der_intersection a (SRegex.sem r₁) (SRegex.sem r₂), intersection, intersection, der_correct a r₁, der_correct a r₂]
  | .complement r₁ r₂ => rw [D, SRegex.sem, SRegex.sem, der_complement a (SRegex.sem r₁) (SRegex.sem r₂), complement, complement, der_correct a r₁, der_correct a r₂]
  | .mult r₁ r₂ =>
    rw [sem, der_concat a (sem r₁) (sem r₂), D, sem, sem, sem]
    constructor
    · rintro (⟨x, y, hx, hy, hc⟩ | ⟨x, y, hx, hy, hc⟩)
      · exact Or.inl ⟨x, y, (der_correct a r₁ x).mp hx, (derLB_correct a r₂ y).mp hy, hc⟩
      · exact Or.inr ⟨x, y, (derLA_correct a r₁ x).mp hx, (der_correct a r₂ y).mp hy, hc⟩
    · rintro (⟨x, y, hx, hy, hc⟩ | ⟨x, y, hx, hy, hc⟩)
      · exact Or.inl ⟨x, y, (der_correct a r₁ x).mpr hx, (derLB_correct a r₂ y).mpr hy, hc⟩
      · exact Or.inr ⟨x, y, (derLA_correct a r₁ x).mpr hx, (der_correct a r₂ y).mpr hy, hc⟩
  | .star r b =>
    refine (der_star_base a (sem r) (sem b) w).trans ?_
    exact star_congr (derLA_correct a r) (fun y => or_congr (der_correct a b y) (concat_congr (der_correct a r) (star_congr (derLB_correct a r) (derLB_correct a b)) y)) w
  | .lb r => exact der_lb a (sem r) w
  | .la r => exact der_la a (sem r) w


theorem derLB_correct {α} [DecidableEq α] (a : α) (r : SRegex α) : derLB a (sem r) ≐ sem (DLB a r) := by
  intro w
  match r with
  | .empty => rw [DLB, sem, derLB_empty a]
  | .unit ss =>
    simp only [DLB, sem, Steps.laStep, complement, atom_map_iff]
    rcases w with ⟨lb, main, la⟩ | ⟨_ | mc, main, la⟩ | ⟨_ | mc, _ | lac, la⟩ <;> simp [derLB, atom_iff, filterDLB, sem.steps, Steps.laStepHelp, unit, toList]
    all_goals first
      | exact ⟨fun ⟨s, hs⟩ => ⟨s, by simp_all⟩, fun ⟨s, hs⟩ => ⟨s, by simp_all⟩⟩
      | (intro s hs; intros; refine ⟨s, hs, ?_⟩; omega)
      | (intros; omega)
  | .top ss =>
    simp only [DLB, sem, Steps.mStep, Steps.laStep, complement, union, atom_map_iff]
    rcases w with ⟨lb, main, la⟩ | ⟨_ | mc, main, la⟩ | ⟨_ | mc, _ | lac, la⟩ <;>
      simp [derLB, atom_iff, filterDLB, sem.steps, Steps.mStepHelp, Steps.laStepHelp, top]
    all_goals first
      | exact ⟨fun ⟨s, hs⟩ => ⟨s, by simp_all⟩, fun ⟨s, hs⟩ => ⟨s, by simp_all⟩⟩
      | intro s hs; intros; exact ⟨s, hs, by omega⟩
  | .symbol b ss =>
    simp only [DLB, sem, Steps.mStep, Steps.laStep, complement, union, atom_map_iff]
    rcases w with ⟨lb, main, la⟩ | ⟨_ | mc, ⟨y, l⟩, la⟩ | ⟨_ | mc, _ | lac, la⟩ <;>
      simp [derLB, atom_iff, filterDLB, sem.steps, Steps.mStepHelp, Steps.laStepHelp, toList]
    all_goals first
      | exact ⟨fun ⟨s, hs⟩ => ⟨s, by simp_all⟩, fun ⟨s, hs⟩ => ⟨s, by simp_all⟩⟩
      | intro s hs; intros; exact ⟨s, hs, by omega⟩
  | .plus r₁ r₂ => rw [DLB, SRegex.sem, SRegex.sem, derLB_union a (SRegex.sem r₁) (SRegex.sem r₂), union, union, derLB_correct a r₁, derLB_correct a r₂]
  | .intersection r₁ r₂ => rw [DLB, SRegex.sem, SRegex.sem, derLB_intersection a (SRegex.sem r₁) (SRegex.sem r₂), intersection, intersection, derLB_correct a r₁, derLB_correct a r₂]
  | .complement r₁ r₂ => rw [DLB, SRegex.sem, SRegex.sem, derLB_complement a (SRegex.sem r₁) (SRegex.sem r₂), complement, complement, derLB_correct a r₁, derLB_correct a r₂]
  | .mult r₁ r₂ =>
    rw [SRegex.sem, (derLB_concat a (SRegex.sem r₁) (SRegex.sem r₂))]
    constructor
    . intro ⟨x, y, hx, hy, hc⟩; exact ⟨x, y, ((derLB_correct a r₁) x).mp hx, ((derLB_correct a r₂) y).mp hy, hc⟩
    . intro ⟨x, y, hx, hy, hc⟩; exact ⟨x, y, ((derLB_correct a r₁) x).mpr hx, ((derLB_correct a r₂) y).mpr hy, hc⟩
  | .star r b => exact (derLB_star a (SRegex.sem r) (SRegex.sem b) w).trans (star_congr (derLB_correct a r) (derLB_correct a b) w)
  | .lb r =>
    refine (derLB_lb a (SRegex.sem r) w).trans ?_
    match w with
    | .left _ [] _ | .right 0 _ _ =>
      simp only [SRegex.sem, DLB, lookbehind]; exact exists_congr fun _ => der_correct a r _
    | .left _ (_ :: _) _ | .middle _ _ _ | .right (_ + 1) _ _ => simp [SRegex.sem, DLB, lookbehind]
  | .la r =>
    refine (derLB_la a (SRegex.sem r) w).trans ?_
    match w with
    | .left _ [] _ | .right 0 _ [] | .right 0 _ (_ :: _) => simp only [SRegex.sem, DLB, lookahead]; exact derLB_correct a r _
    | .left _ (_ :: _) _ | .middle _ _ _ | .right (_ + 1) _ _ => simp [SRegex.sem, DLB, lookahead]

theorem derLA_correct {α} [DecidableEq α] (a : α) (r : SRegex α) : derLA a (sem r) ≐ sem (DLA a r) := by
  intro w
  match r with
  | .empty => rw [DLA, sem, derLA_empty a]
  | .unit ss =>
    simp only [DLA, sem, Steps.laStep, atom_map_iff]
    rcases w with ⟨⟩ | ⟨⟩ | ⟨mc, _ | lac, la⟩ <;> simp [derLA, atom_iff, sem.steps, Steps.laStepHelp, unit]
  | .top ss =>
    simp only [DLA, sem, Steps.laStep, atom_map_iff]
    rcases w with ⟨⟩ | ⟨⟩ | ⟨mc, _ | lac, la⟩ <;> simp [derLA, atom_iff, sem.steps, Steps.laStepHelp, top]
  | .symbol b ss =>
    simp only [DLA, sem]
    rcases w with ⟨⟩ | ⟨⟩ | ⟨mc, _ | lac, la⟩ <;> simp [derLA, atom_iff, sem.steps, empty]
  | .plus r₁ r₂ => rw [DLA, SRegex.sem, SRegex.sem, derLA_union a (SRegex.sem r₁) (SRegex.sem r₂), union, union, derLA_correct a r₁, derLA_correct a r₂]
  | .intersection r₁ r₂ => rw [DLA, SRegex.sem, SRegex.sem, derLA_intersection a (SRegex.sem r₁) (SRegex.sem r₂), intersection, intersection, derLA_correct a r₁, derLA_correct a r₂]
  | .complement r₁ r₂ => rw [DLA, SRegex.sem, SRegex.sem, derLA_complement a (SRegex.sem r₁) (SRegex.sem r₂), complement, complement, derLA_correct a r₁, derLA_correct a r₂]
  | .mult r₁ r₂ =>
    rw [SRegex.sem, (derLA_concat a (SRegex.sem r₁) (SRegex.sem r₂))]
    constructor
    . intro ⟨x, y, hx, hy, hc⟩; exact ⟨x, y, ((derLA_correct a r₁) x).mp hx, ((derLA_correct a r₂) y).mp hy, hc⟩
    . intro ⟨x, y, hx, hy, hc⟩; exact ⟨x, y, ((derLA_correct a r₁) x).mpr hx, ((derLA_correct a r₂) y).mpr hy, hc⟩
  | .star r b => exact (derLA_star a (SRegex.sem r) (SRegex.sem b) w).trans (star_congr (derLA_correct a r) (derLA_correct a b) w)
  | .lb r =>
    rw [sem, DLA, sem]
    refine (derLA_lb a (sem r) w).trans ?_
    match w with
    | .left _ [] _ | .right 0 _ _ =>
      simp only [lookbehind]; exact exists_congr fun _ => derLA_correct a r _
    | .left _ (_ :: _) _ | .middle _ _ _ | .right (_ + 1) _ _ => simp [lookbehind]
  | .la r =>
    refine (derLA_la a (sem r) w).trans ?_
    match w with
    | .left _ [] _ | .right 0 _ [] | .right 0 _ (_ :: _) => simp only [DLA, sem, lookahead]; exact der_correct a r _
    | .left _ (_ :: _) _ | .middle _ _ _ | .right (_ + 1) _ _ => simp [DLA, sem, lookahead]

end


theorem der_word_correct {α} [DecidableEq α] (w : List α) (r : SRegex α) : (der_word w (sem r)) ≐ (sem (D_word w r)) := by
  induction w generalizing r with
  | nil => intro u; simp [der_word, D_word]
  | cons whd wtl ih =>
    intro u
    simp [der_word, D_word]
    have hder := der_correct whd r
    have der_word_congr :  ∀ (tl : List α) (l₁ l₂ : Lang α), l₁ ≐ l₂ → ∀ u : Word α, der_word tl l₁ u ↔ der_word tl l₂ u := by
      intro tl l₁ l₂ h
      induction tl generalizing l₁ l₂ with
      | nil => intro v; exact h v
      | cons y ys ih₂ =>
        intro u'; simp [der_word]
        have : der y l₁ ≐ der y l₂ := by
          intro v; simp only [der]; split <;> first | exact h _ | exact Iff.rfl
        exact ih₂ (der y l₁) (der y l₂) this u'
    exact Iff.trans (der_word_congr wtl (der whd (SRegex.sem r)) (SRegex.sem (D whd r)) hder u) (ih (D whd r) u)

theorem derLB_word_correct {α} [DecidableEq α] (w : List α) (r : SRegex α) : (derLB_word w (sem r)) ≐ (sem (DLB_word w r)) := by
  induction w generalizing r with
  | nil => intro u; simp [derLB_word, DLB_word]
  | cons whd wtl ih =>
    intro u
    simp only [derLB_word, DLB_word]
    have hderLB := derLB_correct whd r
    have der_word_congr :
        ∀ (tl : List α) (l₁ l₂ : Lang α), l₁ ≐ l₂ → ∀ u : Word α, derLB_word tl l₁ u ↔ derLB_word tl l₂ u := by
      intro tl l₁ l₂ h
      induction tl generalizing l₁ l₂ with
      | nil => intro v; exact h v
      | cons y ys ih₂ =>
        intro u'; simp [derLB_word]
        have : derLB y l₁ ≐ derLB y l₂ := by
          intro v; simp only [derLB]; split <;> first | exact h _ | exact Iff.rfl
        exact ih₂ (derLB y l₁) (derLB y l₂) this u'
    exact Iff.trans (der_word_congr wtl (derLB whd (SRegex.sem r)) (SRegex.sem (DLB whd r)) hderLB u) (ih (DLB whd r) u)

theorem derLA_word_correct {α} [DecidableEq α] (w : List α) (r : SRegex α) : (derLA_word w (sem r)) ≐ (sem (DLA_word w r)) := by
  induction w generalizing r with
  | nil => intro u; simp [derLA_word, DLA_word]
  | cons whd wtl ih =>
    intro u
    simp only [derLA_word, DLA_word]
    have hderLA := derLA_correct whd r
    have derLA_word_congr :
        ∀ (tl : List α) (l₁ l₂ : Lang α), l₁ ≐ l₂ → ∀ u : Word α, derLA_word tl l₁ u ↔ derLA_word tl l₂ u := by
      intro tl l₁ l₂ h
      induction tl generalizing l₁ l₂ with
      | nil => intro v; exact h v
      | cons y ys ih₂ =>
        intro u'
        simp [derLA_word]
        have : derLA y l₁ ≐ derLA y l₂ := by
          intro v; simp only [derLA]; split <;> first | exact h _ | exact Iff.rfl
        exact ih₂ (derLA y l₁) (derLA y l₂) this u'
    exact Iff.trans (derLA_word_congr wtl (derLA whd (SRegex.sem r)) (SRegex.sem (DLA whd r)) hderLA u) (ih (DLA whd r) u)

/-- Theorem 4.2.3 — correctness of the existential derivative: `⟦xD_w r⟧ = xder_w ⟦r⟧`. -/
theorem xder_correct {α} [DecidableEq α] (s : List α) (r : SRegex α) : (xder s (sem r)) ≐ (sem (xD s r) ) := by
  induction s generalizing r with
  | nil => intro w; simp [xder, xD]
  | cons a tl ih =>
    intro w
    have : (derLB a (sem r) ∪ der a (sem r) ∪ derLA a (sem r)) ≐ SRegex.sem (.plus (.plus (DLB a r) (D a r)) (DLA a r)) := by
      intro u; simp [SRegex.sem, union, derLB_correct a r u, der_correct a r u, derLA_correct a r u, or_assoc]
    exact (xder_congr tl _ _ this w).trans (ih (.plus (.plus (DLB a r) (D a r)) (DLA a r)) w)

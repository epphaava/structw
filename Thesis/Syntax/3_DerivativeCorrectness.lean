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

theorem der_correct {α} [DecidableEq α] (a : α) (r : SRegex α) (n : Nat) :
    der a (sem r n) ≐ sem (D a r) (n + 1) := by
  intro w
  match r with
  | .empty => exact der_empty a w
  | .unit ss =>
    simp [D, sem]
    induction ss with
    | nil => exact der_empty a w
    | cons s ss ih =>
      refine (der_union a _ _ w).trans ?_
      simp [union, empty, ih] at ih ⊢
      rcases w with ⟨⟩ | ⟨_, _ | _, _, _⟩ | ⟨_, _ | _, _ | _, _⟩ <;> simp [der, sem.steps, unit]
  | .top ss =>
    simp only [D, sem, Steps.mStep, Steps.laStep, complement, atom_map_iff]
    rcases w with ⟨⟩ | ⟨lbc, _ | mc, main, la⟩ | ⟨lbc, _ | mc, _ | lac, la⟩ <;>
      simp [der, atom_iff, filterD, sem.steps, Steps.mStepHelp, Steps.laStepHelp, top]
    all_goals first
      | exact ⟨fun ⟨s, hs⟩ => ⟨s, by simp_all; omega⟩, fun ⟨s, hs⟩ => ⟨s, by simp_all; omega⟩⟩
      | exact ⟨fun ⟨s, hs⟩ => ⟨s, by simp_all⟩, fun ⟨s, hs⟩ => ⟨s, by simp_all⟩⟩
      | (intro s hs; intros; refine ⟨s, hs, ?_⟩; omega)
  | .symbol b ss =>
    by_cases h : a = b
    · subst h
      simp [D, sem, Steps.mStep, Steps.laStep, complement, atom_map_iff]
      rcases w with ⟨⟩ | ⟨lbc, _ | mc, main, la⟩ | ⟨lbc, _ | mc, _ | lac, la⟩ <;>
        simp [der, atom_iff, filterD, sem.steps, Steps.mStepHelp, Steps.laStepHelp, top, unit, toList]
      all_goals first
        | exact ⟨fun ⟨s, hs⟩ => ⟨s, by simp_all; omega⟩, fun ⟨s, hs⟩ => ⟨s, by simp_all; omega⟩⟩
        | exact ⟨fun ⟨s, hs⟩ => ⟨s, by simp_all⟩, fun ⟨s, hs⟩ => ⟨s, by simp_all⟩⟩
        | (intro s hs; intros; refine ⟨s, hs, ?_⟩; omega)
    · simp [D, h, sem]
      rcases w with ⟨⟩ | ⟨lbc, _ | mc, main, la⟩ | ⟨lbc, _ | mc, _ | lac, la⟩ <;>
        simp [der, atom_iff, sem.steps, empty, Ne.symm h]
  | .plus r₁ r₂ => rw [D, SRegex.sem, SRegex.sem, der_union a (SRegex.sem r₁ n) (SRegex.sem r₂ n), union, union, der_correct a r₁ n, der_correct a r₂ n]
  | .intersection r₁ r₂ => rw [D, SRegex.sem, SRegex.sem, der_intersection a (SRegex.sem r₁ n) (SRegex.sem r₂ n), intersection, intersection, der_correct a r₁ n, der_correct a r₂ n]
  | .complement r₁ r₂ => rw [D, SRegex.sem, SRegex.sem, der_complement a (SRegex.sem r₁ n) (SRegex.sem r₂ n), complement, complement, der_correct a r₁ n, der_correct a r₂ n]
  | .mult r₁ r₂ =>
    rw [sem, der_concat a (sem r₁ n) (sem r₂ n), D, sem, sem, sem]
    constructor
    · rintro (⟨x, y, hx, hy, hc⟩ | ⟨x, y, hx, hy, hc⟩)
      · exact Or.inl ⟨x, y, (der_correct a r₁ n x).mp hx, (derLB_correct a r₂ n y).mp hy, hc⟩
      · exact Or.inr ⟨x, y, (derLA_correct a r₁ n x).mp hx, (der_correct a r₂ n y).mp hy, hc⟩
    · rintro (⟨x, y, hx, hy, hc⟩ | ⟨x, y, hx, hy, hc⟩)
      · exact Or.inl ⟨x, y, (der_correct a r₁ n x).mpr hx, (derLB_correct a r₂ n y).mpr hy, hc⟩
      · exact Or.inr ⟨x, y, (derLA_correct a r₁ n x).mpr hx, (der_correct a r₂ n y).mpr hy, hc⟩
  | .star r b =>
    refine (der_star_base a (sem r n) (sem b n) w).trans ?_
    exact star_congr (derLA_correct a r n)
      (fun y => or_congr (der_correct a b n y)
        (concat_congr (der_correct a r n) (star_congr (derLB_correct a r n) (derLB_correct a b n)) y)) w
  | .lb r => exact der_lb a (sem r n) w
  | .la r => exact der_la a (sem r n) w


theorem derLB_correct {α} [DecidableEq α] (a : α) (r : SRegex α) (n : Nat) :
    derLB a (sem r n) ≐ sem (DLB a r) (n + 1) := by
  intro w
  match r with
  | .empty => exact derLB_empty a w
  | .unit ss =>
    simp only [DLB, sem, Steps.laStep, complement, atom_map_iff]
    rcases w with ⟨_ | lbc, lb, main, la⟩ | ⟨_ | lbc, _ | mc, main, la⟩ | ⟨_ | lbc, _ | mc, _ | lac, la⟩ <;>
      simp [derLB, atom_iff, filterDLB, sem.steps, Steps.laStepHelp, unit, toList]
    all_goals first
      | exact ⟨fun ⟨s, hs⟩ => ⟨s, by simp_all; omega⟩, fun ⟨s, hs⟩ => ⟨s, by simp_all; omega⟩⟩
      | exact ⟨fun ⟨s, hs⟩ => ⟨s, by simp_all⟩, fun ⟨s, hs⟩ => ⟨s, by simp_all⟩⟩
      | (intro s hs; intros; refine ⟨s, hs, ?_⟩; omega)
      | (intros; omega)
  | .top ss =>
    simp only [DLB, sem, Steps.mStep, Steps.laStep, complement, union, atom_map_iff]
    rcases w with ⟨_ | lbc, lb, main, la⟩ | ⟨_ | lbc, _ | mc, main, la⟩ | ⟨_ | lbc, _ | mc, _ | lac, la⟩ <;>
      simp [derLB, atom_iff, filterDLB, sem.steps, Steps.mStepHelp, Steps.laStepHelp, top]
    all_goals first
      | exact ⟨fun ⟨s, hs⟩ => ⟨s, by simp_all; omega⟩, fun ⟨s, hs⟩ => ⟨s, by simp_all; omega⟩⟩
      | exact ⟨fun ⟨s, hs⟩ => ⟨s, by simp_all⟩, fun ⟨s, hs⟩ => ⟨s, by simp_all⟩⟩
      | (intro s hs; intros; refine ⟨s, hs, ?_⟩; omega)
      | (intros; omega)
  | .symbol b ss =>
    simp only [DLB, sem, Steps.mStep, Steps.laStep, complement, union, atom_map_iff]
    rcases w with ⟨_ | lbc, lb, main, la⟩ | ⟨_ | lbc, _ | mc, ⟨y, l⟩, la⟩ | ⟨_ | lbc, _ | mc, _ | lac, la⟩ <;>
      simp [derLB, atom_iff, filterDLB, sem.steps, Steps.mStepHelp, Steps.laStepHelp, toList]
    all_goals first
      | exact ⟨fun ⟨s, hs⟩ => ⟨s, by simp_all; omega⟩, fun ⟨s, hs⟩ => ⟨s, by simp_all; omega⟩⟩
      | exact ⟨fun ⟨s, hs⟩ => ⟨s, by simp_all⟩, fun ⟨s, hs⟩ => ⟨s, by simp_all⟩⟩
      | (intro s hs; intros; refine ⟨s, hs, ?_⟩; omega)
      | (intros; omega)
  | .plus r₁ r₂ => rw [DLB, SRegex.sem, SRegex.sem, derLB_union a (SRegex.sem r₁ n) (SRegex.sem r₂ n), union, union, derLB_correct a r₁ n, derLB_correct a r₂ n]
  | .intersection r₁ r₂ => rw [DLB, SRegex.sem, SRegex.sem, derLB_intersection a (SRegex.sem r₁ n) (SRegex.sem r₂ n), intersection, intersection, derLB_correct a r₁ n, derLB_correct a r₂ n]
  | .complement r₁ r₂ => rw [DLB, SRegex.sem, SRegex.sem, derLB_complement a (SRegex.sem r₁ n) (SRegex.sem r₂ n), complement, complement, derLB_correct a r₁ n, derLB_correct a r₂ n]
  | .mult r₁ r₂ =>
    rw [SRegex.sem, (derLB_concat a (SRegex.sem r₁ n) (SRegex.sem r₂ n))]
    constructor
    . intro ⟨x, y, hx, hy, hc⟩; exact ⟨x, y, ((derLB_correct a r₁ n) x).mp hx, ((derLB_correct a r₂ n) y).mp hy, hc⟩
    . intro ⟨x, y, hx, hy, hc⟩; exact ⟨x, y, ((derLB_correct a r₁ n) x).mpr hx, ((derLB_correct a r₂ n) y).mpr hy, hc⟩
  | .star r b => exact (derLB_star a (SRegex.sem r n) (SRegex.sem b n) w).trans (star_congr (derLB_correct a r n) (derLB_correct a b n) w)
  | .lb r =>
    refine (derLB_lb a (SRegex.sem r n) w).trans ?_
    match w with
    | .left _ _ [] _ | .right _ 0 _ _ => exact der_correct a r n _
    | .left _ _ (_ :: _) _ | .middle _ _ _ _ | .right _ (_ + 1) _ _ => simp [SRegex.sem, DLB, lookbehind]
  | .la r =>
    refine (derLB_la a (SRegex.sem r n) w).trans ?_
    match w with
    | .left _ _ [] _ | .right _ 0 _ [] | .right _ 0 _ (_ :: _) =>
      simp only [SRegex.sem, DLB, lookahead]; exact derLB_correct a r n _
    | .left _ _ (_ :: _) _ | .middle _ _ _ _ | .right _ (_ + 1) _ _ => simp [SRegex.sem, DLB, lookahead]

theorem derLA_correct {α} [DecidableEq α] (a : α) (r : SRegex α) (n : Nat) :
    derLA a (sem r n) ≐ sem (DLA a r) (n + 1) := by
  intro w
  match r with
  | .empty => exact derLA_empty a w
  | .unit ss =>
    simp only [DLA, sem, Steps.laStep, atom_map_iff]
    rcases w with ⟨⟩ | ⟨⟩ | ⟨lbc, mc, _ | lac, la⟩ <;> simp [derLA, atom_iff, sem.steps, Steps.laStepHelp, unit]
    all_goals first
      | exact ⟨fun ⟨s, hs⟩ => ⟨s, by simp_all; omega⟩, fun ⟨s, hs⟩ => ⟨s, by simp_all; omega⟩⟩
      | exact ⟨fun ⟨s, hs⟩ => ⟨s, by simp_all⟩, fun ⟨s, hs⟩ => ⟨s, by simp_all⟩⟩
  | .top ss =>
    simp only [DLA, sem, Steps.laStep, atom_map_iff]
    rcases w with ⟨⟩ | ⟨⟩ | ⟨lbc, mc, _ | lac, la⟩ <;> simp [derLA, atom_iff, sem.steps, Steps.laStepHelp, top]
    all_goals first
      | exact ⟨fun ⟨s, hs⟩ => ⟨s, by simp_all; omega⟩, fun ⟨s, hs⟩ => ⟨s, by simp_all; omega⟩⟩
      | exact ⟨fun ⟨s, hs⟩ => ⟨s, by simp_all⟩, fun ⟨s, hs⟩ => ⟨s, by simp_all⟩⟩
  | .symbol b ss =>
    simp only [DLA, sem]
    rcases w with ⟨⟩ | ⟨⟩ | ⟨lbc, mc, _ | lac, la⟩ <;> simp [derLA, atom_iff, sem.steps, empty]
  | .plus r₁ r₂ => rw [DLA, SRegex.sem, SRegex.sem, derLA_union a (SRegex.sem r₁ n) (SRegex.sem r₂ n), union, union, derLA_correct a r₁ n, derLA_correct a r₂ n]
  | .intersection r₁ r₂ => rw [DLA, SRegex.sem, SRegex.sem, derLA_intersection a (SRegex.sem r₁ n) (SRegex.sem r₂ n), intersection, intersection, derLA_correct a r₁ n, derLA_correct a r₂ n]
  | .complement r₁ r₂ => rw [DLA, SRegex.sem, SRegex.sem, derLA_complement a (SRegex.sem r₁ n) (SRegex.sem r₂ n), complement, complement, derLA_correct a r₁ n, derLA_correct a r₂ n]
  | .mult r₁ r₂ =>
    rw [SRegex.sem, (derLA_concat a (SRegex.sem r₁ n) (SRegex.sem r₂ n))]
    constructor
    . intro ⟨x, y, hx, hy, hc⟩; exact ⟨x, y, ((derLA_correct a r₁ n) x).mp hx, ((derLA_correct a r₂ n) y).mp hy, hc⟩
    . intro ⟨x, y, hx, hy, hc⟩; exact ⟨x, y, ((derLA_correct a r₁ n) x).mpr hx, ((derLA_correct a r₂ n) y).mpr hy, hc⟩
  | .star r b => exact (derLA_star a (SRegex.sem r n) (SRegex.sem b n) w).trans (star_congr (derLA_correct a r n) (derLA_correct a b n) w)
  | .lb r =>
    rw [sem, DLA, sem]
    refine (derLA_lb a (sem r n) w).trans ?_
    match w with
    | .left _ _ [] _ | .right _ 0 _ _ => simp only [lookbehind]; exact derLA_correct a r n _
    | .left _ _ (_ :: _) _ | .middle _ _ _ _ | .right _ (_ + 1) _ _ => simp [lookbehind]
  | .la r =>
    refine (derLA_la a (sem r n) w).trans ?_
    match w with
    | .left _ _ [] _ | .right _ 0 _ [] | .right _ 0 _ (_ :: _) =>
      simp only [DLA, sem, lookahead]; exact der_correct a r n _
    | .left _ _ (_ :: _) _ | .middle _ _ _ _ | .right _ (_ + 1) _ _ => simp [DLA, sem, lookahead]

end


/-- Each of `derLB`, `der`, `derLA` either looks `l` up at one word or is `False`,
so they all respect language equality. -/
theorem der_congr {α} (a : α) {l₁ l₂ : Lang α} (h : l₁ ≐ l₂) : der a l₁ ≐ der a l₂ := by
  intro v; simp only [der]; split <;> first | exact h _ | exact Iff.rfl

theorem derLB_congr {α} (a : α) {l₁ l₂ : Lang α} (h : l₁ ≐ l₂) : derLB a l₁ ≐ derLB a l₂ := by
  intro v; simp only [derLB]; split <;> first | exact h _ | exact Iff.rfl

theorem derLA_congr {α} (a : α) {l₁ l₂ : Lang α} (h : l₁ ≐ l₂) : derLA a l₁ ≐ derLA a l₂ := by
  intro v; simp only [derLA]; split <;> first | exact h _ | exact Iff.rfl

theorem der_word_congr {α} (tl : List α) {l₁ l₂ : Lang α} (h : l₁ ≐ l₂) : der_word tl l₁ ≐ der_word tl l₂ := by
  induction tl generalizing l₁ l₂ with
  | nil => exact h
  | cons y ys ih => exact ih (der_congr y h)

theorem derLB_word_congr {α} (tl : List α) {l₁ l₂ : Lang α} (h : l₁ ≐ l₂) : derLB_word tl l₁ ≐ derLB_word tl l₂ := by
  induction tl generalizing l₁ l₂ with
  | nil => exact h
  | cons y ys ih => exact ih (derLB_congr y h)

theorem derLA_word_congr {α} (tl : List α) {l₁ l₂ : Lang α} (h : l₁ ≐ l₂) : derLA_word tl l₁ ≐ derLA_word tl l₂ := by
  induction tl generalizing l₁ l₂ with
  | nil => exact h
  | cons y ys ih => exact ih (derLA_congr y h)

theorem der_word_correct {α} [DecidableEq α] (w : List α) (r : SRegex α) (n : Nat) :
    der_word w (sem r n) ≐ sem (D_word w r) (n + w.length) := by
  induction w generalizing r n with
  | nil => intro u; simp [der_word, D_word]
  | cons whd wtl ih =>
    intro u
    have h := (der_word_congr wtl (der_correct whd r n) u).trans (ih (D whd r) (n + 1) u)
    rw [List.length_cons, ← Nat.add_assoc, Nat.add_right_comm]
    exact h

theorem derLB_word_correct {α} [DecidableEq α] (w : List α) (r : SRegex α) (n : Nat) :
    derLB_word w (sem r n) ≐ sem (DLB_word w r) (n + w.length) := by
  induction w generalizing r n with
  | nil => intro u; simp [derLB_word, DLB_word]
  | cons whd wtl ih =>
    intro u
    have h := (derLB_word_congr wtl (derLB_correct whd r n) u).trans (ih (DLB whd r) (n + 1) u)
    rw [List.length_cons, ← Nat.add_assoc, Nat.add_right_comm]
    exact h

theorem derLA_word_correct {α} [DecidableEq α] (w : List α) (r : SRegex α) (n : Nat) :
    derLA_word w (sem r n) ≐ sem (DLA_word w r) (n + w.length) := by
  induction w generalizing r n with
  | nil => intro u; simp [derLA_word, DLA_word]
  | cons whd wtl ih =>
    intro u
    have h := (derLA_word_congr wtl (derLA_correct whd r n) u).trans (ih (DLA whd r) (n + 1) u)
    rw [List.length_cons, ← Nat.add_assoc, Nat.add_right_comm]
    exact h

/-- Theorem 4.2.3 — correctness of the existential derivative: `⟦xD_w r⟧ = xder_w ⟦r⟧`. -/
theorem xder_correct {α} [DecidableEq α] (s : List α) (r : SRegex α) (n : Nat) :
    xder s (sem r n) ≐ sem (xD s r) (n + s.length) := by
  induction s generalizing r n with
  | nil => intro w; simp [xder, xD]
  | cons a tl ih =>
    intro w
    have : (derLB a (sem r n) ∪ der a (sem r n) ∪ derLA a (sem r n)) ≐
        SRegex.sem (.plus (.plus (DLB a r) (D a r)) (DLA a r)) (n + 1) := by
      intro u; simp [SRegex.sem, union, derLB_correct a r n u, der_correct a r n u, derLA_correct a r n u, or_assoc]
    have h := (xder_congr tl _ _ this w).trans (ih (.plus (.plus (DLB a r) (D a r)) (DLA a r)) (n + 1) w)
    rw [List.length_cons, ← Nat.add_assoc, Nat.add_right_comm]
    exact h

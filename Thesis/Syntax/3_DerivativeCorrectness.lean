import Thesis.Syntax.«1_Expressions»
import Thesis.Syntax.«2_Derivatives»
import Thesis.Syntax.Helpers.«3_DerivativeCorrectness»
import Thesis.Semantics.kLang.«3_Derivatives»
import Thesis.Semantics.kLang.«5_LookbehindDerivativeLaws»
import Thesis.Semantics.kLang.«6_LookaheadDerivativeLaws»
import Thesis.Semantics.kLang.«7_DerivativeLaws»

namespace DerCorrect

open SRegex
open SRegexDerivatives

open derLaws
open derLBLaws
open derLALaws
open StructuredWords
open kStructuredWords
open kOperators
open DerCorrectHelpers
open kDerivatives
open Steps

mutual

theorem der_correct {α} [DecidableEq α] (a : α) (r : SRegex α) (n : Nat) : der a (sem r n) ≐ sem (D a r) (n + 1) := by
  intro w
  match r with
  | .empty => exact der_empty a w
  | .unit ss => rcases w with ⟨⟩ | ⟨_ | _, _, _⟩ | ⟨_ | _, _ | _, _⟩ <;> simp [D, sem, der, Derivatives.der, atom_iff, sem.steps, Operators.unit, kOperators.empty, Operators.empty,  word_steps]
  | .top ss =>
    simp [D, sem, Steps.mStep, atom_map_iff]
    rcases w with ⟨⟩ | ⟨_ | mc, main, la⟩ | ⟨_ | mc, _ | lac, la⟩ <;> simp [der, Derivatives.der, atom_iff, filterD, sem.steps,  mStepSingle, Operators.top, word_steps]
    . intro _; constructor
      . intro ⟨s, hs, _, hla, hm⟩; exact ⟨s, ⟨hs, hla⟩, by omega, hla, hm⟩
      . intro ⟨s, ⟨hs, hla⟩, _, _, hm⟩; exact ⟨s, hs, by omega, hla, hm⟩
    . intro _; constructor
      . intro ⟨s, hs, _, hla, hm⟩; exact ⟨s, ⟨hs, hla⟩, by omega, hm, hla⟩
      . intro ⟨s, ⟨hs, hla⟩, _, hm, _⟩; exact ⟨s, hs, by omega, hla, hm⟩
    . intros; omega
  | .symbol b ss =>
    by_cases h : a = b
    · subst h
      simp [D, sem, Steps.mStep, atom_map_iff]
      rcases w with ⟨⟩ | ⟨_ | mc, main, la⟩ | ⟨_ | mc, _ | lac, la⟩ <;> simp [der, Derivatives.der, atom_iff, filterD, sem.steps, mStepSingle, Operators.unit, toList, word_steps]
      . intro _; constructor
        . intro ⟨s, hs, _, hla, hm, hmc⟩; exact ⟨s, ⟨hs, hla⟩, by omega, hm, hla, hmc⟩
        . intro ⟨s, ⟨hs, hla⟩, _, hm, _, hmc⟩; exact ⟨s, hs, by omega, hla, hm, hmc⟩
      . intros; omega
    · rcases w with ⟨⟩ | ⟨_ | mc, main, la⟩ | ⟨_ | mc, _ | lac, la⟩ <;> simp [D, h, sem, der, Derivatives.der, atom_iff, sem.steps, empty, Operators.empty, Ne.symm h, word_steps]
  | .plus r₁ r₂ => exact (der_union a _ _ w).trans (or_congr (der_correct a r₁ n w) (der_correct a r₂ n w))
  | .intersection r₁ r₂ => exact (der_intersection a _ _ w).trans (and_congr (der_correct a r₁ n w) (der_correct a r₂ n w))
  | .complement r₁ r₂ => exact (der_complement a _ _ w).trans (and_congr (der_correct a r₁ n w) (not_congr (der_correct a r₂ n w)))
  | .mult r₁ r₂ =>
    refine (der_concat a (sem r₁ n).val (sem r₂ n).val w).trans ?_
    constructor
    · rintro (⟨x, y, hx, hy, hc⟩ | ⟨x, y, hx, hy, hc⟩)
      · exact Or.inl ⟨x, y, (der_correct a r₁ n x).mp hx, (derLB_correct a r₂ n y).mp hy, hc⟩
      · exact Or.inr ⟨x, y, (derLA_correct a r₁ n x).mp hx, (der_correct a r₂ n y).mp hy, hc⟩
    · rintro (⟨x, y, hx, hy, hc⟩ | ⟨x, y, hx, hy, hc⟩)
      · exact Or.inl ⟨x, y, (der_correct a r₁ n x).mpr hx, (derLB_correct a r₂ n y).mpr hy, hc⟩
      · exact Or.inr ⟨x, y, (derLA_correct a r₁ n x).mpr hx, (der_correct a r₂ n y).mpr hy, hc⟩
  | .star r b =>
    refine (der_star_base a (sem r n).val (sem b n).val w).trans ?_
    have hb : (der a (sem b n) ∪ (der a (sem r n) • star (derLB a (sem r n)) (derLB a (sem b n)))) ≐
        (sem (D a b) (n + 1) ∪ (sem (D a r) (n + 1) • star (sem (DLB a r) (n + 1)) (sem (DLB a b) (n + 1)))) :=
      λ y => or_congr (der_correct a b n y)
        (concat_congr (der_correct a r n) (star_congr (derLB_correct a r n) (derLB_correct a b n)) y)
    exact star_congr (derLA_correct a r n) hb w
  | .lb r => exact der_lb a (sem r n).val w
  | .la r => exact der_la a (sem r n).val w

theorem derLB_correct {α} [DecidableEq α] (a : α) (r : SRegex α) (n : Nat) : derLB a (sem r n) ≐ sem (DLB a r) (n + 1) := by
  intro w
  match r with
  | .empty => exact derLB_empty a w
  | .unit ss =>
    rcases w with ⟨lb, main, la⟩ | ⟨_ | mc, main, la⟩ | ⟨_ | mc, _ | lac, la⟩ <;> simp [DLB, sem, derLB, Derivatives.derLB, atom_iff, filterDLB, sem.steps, Operators.unit, toList, Word.word_steps]
    . constructor
      . intro ⟨s, hs, hm, hla, hmain⟩; exact ⟨s, ⟨hs, hm, hla⟩, hm, hla, hmain⟩
      . intro ⟨s, ⟨hs, hm, hla⟩, _, _, hmain⟩; exact ⟨s, hs, hm, hla, hmain⟩
    . intros; omega
    . intros; omega
    . intros; omega
  | .top ss =>
    rcases w with ⟨lb, main, la⟩ | ⟨_ | mc, main, la⟩ | ⟨_ | mc, _ | lac, la⟩ <;> simp [DLB, sem, derLB, Derivatives.derLB, atom_iff, filterDLB, sem.steps, Operators.top, Word.word_steps]
    . constructor
      . intro ⟨s, hs, hm, hla⟩; exact ⟨s, ⟨hs, hm, hla⟩, hla, hm⟩
      . intro ⟨s, ⟨hs, hm, hla⟩, _⟩; exact ⟨s, hs, hm, hla⟩
    . intros; omega
    . intros; omega
    . intros; omega
    . intros; omega
  | .symbol b ss =>
    rcases w with ⟨lb, main, la⟩ | ⟨_ | mc, ⟨y, l⟩, la⟩ | ⟨_ | mc, _ | lac, la⟩ <;> simp [DLB, sem, derLB, Derivatives.derLB, atom_iff, filterDLB, sem.steps, toList, Word.word_steps]
    . constructor
      . intro ⟨s, hs, hm, hla, hmain⟩; exact ⟨s, ⟨hs, hm, hla⟩, hm, hla, hmain⟩
      . intro ⟨s, ⟨hs, hm, hla⟩, _, _, hmain⟩; exact ⟨s, hs, hm, hla, hmain⟩
    . constructor
      . intro ⟨s, hs, hm, hla, hy, hl⟩; exact ⟨s, ⟨hs, hm, hla⟩, hla, hm, hl, hy.symm⟩
      . intro ⟨s, ⟨hs, hm, hla⟩, _, _, hl, hy⟩; exact ⟨s, hs, hm, hla, hy.symm, hl⟩
    . intros; omega
  | .plus r₁ r₂ => exact (derLB_union a _ _ w).trans (or_congr (derLB_correct a r₁ n w) (derLB_correct a r₂ n w))
  | .intersection r₁ r₂ => exact (derLB_intersection a _ _ w).trans (and_congr (derLB_correct a r₁ n w) (derLB_correct a r₂ n w))
  | .complement r₁ r₂ => exact (derLB_complement a _ _ w).trans (and_congr (derLB_correct a r₁ n w) (not_congr (derLB_correct a r₂ n w)))
  | .mult r₁ r₂ =>
    refine (derLB_concat a (sem r₁ n).val (sem r₂ n).val w).trans ?_
    constructor
    . intro ⟨x, y, hx, hy, hc⟩; exact ⟨x, y, ((derLB_correct a r₁ n) x).mp hx, ((derLB_correct a r₂ n) y).mp hy, hc⟩
    . intro ⟨x, y, hx, hy, hc⟩; exact ⟨x, y, ((derLB_correct a r₁ n) x).mpr hx, ((derLB_correct a r₂ n) y).mpr hy, hc⟩
  | .star r b => exact (derLB_star a (sem r n).val (sem b n).val w).trans (star_congr (derLB_correct a r n) (derLB_correct a b n) w)
  | .lb r =>
    refine (derLB_lb a (sem r n).val w).trans ?_
    match w with
    | .left _ [] _ | .right 0 _ _ => exact exists_congr λ _ => der_correct a r n _
    | .left _ (_ :: _) _ | .middle _ _ _ | .right (_ + 1) _ _ => simp [SRegex.sem, DLB, lookbehind, Operators.lookbehind]
  | .la r =>
    refine (derLB_la a (sem r n).val w).trans ?_
    match w with
    | .left lb [] la => exact derLB_correct a r n (.left lb la [])
    | .right 0 lac [] => exact derLB_correct a r n (.right lac 0 [])
    | .right 0 lac (z :: zs) => exact derLB_correct a r n (.middle lac (z, zs) [])
    | .left _ (_ :: _) _ | .middle _ _ _ | .right (_ + 1) _ _ => simp [SRegex.sem, DLB, lookahead, Operators.lookahead]


theorem derLA_correct {α} [DecidableEq α] (a : α) (r : SRegex α) (n : Nat) : derLA a (sem r n) ≐ sem (DLA a r) (n + 1) := by
  intro w
  match r with
  | .empty => exact derLA_empty a w
  | .unit ss =>
    simp [DLA, sem, Steps.laStep, atom_map_iff]
    rcases w with ⟨⟩ | ⟨⟩ | ⟨mc, _ | lac, la⟩ <;> simp [derLA, Derivatives.derLA, atom_iff, sem.steps, laStepSingle, Operators.unit,  word_steps]
    . constructor
      . intro ⟨_, s, hs, _, hm, hla, hmc⟩; exact ⟨by omega, s, hs, by omega, hm, hla, hmc⟩
      . intro ⟨_, s, hs, _, hm, hla, hmc⟩; exact ⟨by omega, s, hs, by omega, hm, hla, hmc⟩
  | .top ss =>
    simp [DLA, sem, Steps.laStep, atom_map_iff]
    rcases w with ⟨⟩ | ⟨⟩ | ⟨mc, _ | lac, la⟩ <;> simp [derLA, Derivatives.derLA, atom_iff, sem.steps, Steps.laStepSingle, Operators.top,  word_steps]
    . constructor
      . intro ⟨_, s, hs, _, hm, hla⟩; exact ⟨by omega, s, hs, by omega, hm, hla⟩
      . intro ⟨_, s, hs, _, hm, hla⟩; exact ⟨by omega, s, hs, by omega, hm, hla⟩
  | .symbol b ss => rcases w with ⟨⟩ | ⟨⟩ | ⟨mc, _ | lac, la⟩ <;> simp [DLA, sem, derLA, Derivatives.derLA, atom_iff, sem.steps,  empty, Operators.empty,  word_steps]
  | .plus r₁ r₂ => exact (derLA_union a _ _ w).trans (or_congr (derLA_correct a r₁ n w) (derLA_correct a r₂ n w))
  | .intersection r₁ r₂ => exact (derLA_intersection a _ _ w).trans (and_congr (derLA_correct a r₁ n w) (derLA_correct a r₂ n w))
  | .complement r₁ r₂ => exact (derLA_complement a _ _ w).trans (and_congr (derLA_correct a r₁ n w) (not_congr (derLA_correct a r₂ n w)))
  | .mult r₁ r₂ =>
    refine (derLA_concat a (sem r₁ n).val (sem r₂ n).val w).trans ?_
    constructor
    . intro ⟨x, y, hx, hy, hc⟩; exact ⟨x, y, ((derLA_correct a r₁ n) x).mp hx, ((derLA_correct a r₂ n) y).mp hy, hc⟩
    . intro ⟨x, y, hx, hy, hc⟩; exact ⟨x, y, ((derLA_correct a r₁ n) x).mpr hx, ((derLA_correct a r₂ n) y).mpr hy, hc⟩
  | .star r b => exact (derLA_star a (sem r n).val (sem b n).val w).trans (star_congr (derLA_correct a r n) (derLA_correct a b n) w)
  | .lb r =>
    refine (derLA_lb a (sem r n).val w).trans ?_
    match w with
    | .left lb [] la => exact exists_congr fun c => derLA_correct a r n (.middle c lb la)
    | .right 0 lac la => exact exists_congr fun c => derLA_correct a r n (.right c lac la)
    | .left _ (_ :: _) _ | .middle _ _ _ | .right (_ + 1) _ _ => simp [DLA, sem,  lookbehind, Operators.lookbehind]
  | .la r =>
    refine (derLA_la a (sem r n).val w).trans ?_
    match w with
    | .left lb [] la => exact der_correct a r n (.left lb la [])
    | .right 0 lac [] => exact der_correct a r n (.right lac 0 [])
    | .right 0 lac (z :: zs) => exact der_correct a r n (.middle lac (z, zs) [])
    | .left _ (_ :: _) _ | .middle _ _ _ | .right (_ + 1) _ _ => simp [DLA, sem,  lookahead, Operators.lookahead]

end


theorem der_congr {α} (a : α) {l₁ l₂ : kLang α n} (h : l₁ ≐ l₂) : der a l₁ ≐ der a l₂ := by
  intro v; simp only [der, Derivatives.der]; split <;> first | exact h _ | exact Iff.rfl

theorem derLB_congr {α} (a : α) {l₁ l₂ : kLang α n} (h : l₁ ≐ l₂) : derLB a l₁ ≐ derLB a l₂ := by
  intro v; simp only [derLB, Derivatives.derLB]; split <;> first | exact h _ | exact Iff.rfl

theorem derLA_congr {α} (a : α) {l₁ l₂ : kLang α n} (h : l₁ ≐ l₂) : derLA a l₁ ≐ derLA a l₂ := by
  intro v; simp only [derLA, Derivatives.derLA]; split <;> first | exact h _ | exact Iff.rfl

theorem der_word_congr {α} (tl : List α) {l₁ l₂ : kLang α n} (h : l₁ ≐ l₂) : der_word tl l₁ ≐ der_word tl l₂ := by
  induction tl generalizing n l₁ l₂ with
  | nil => exact h
  | cons y ys ih => exact ih (der_congr y h)

theorem derLB_word_congr {α} (tl : List α) {l₁ l₂ : kLang α n} (h : l₁ ≐ l₂) : derLB_word tl l₁ ≐ derLB_word tl l₂ := by
  induction tl generalizing n l₁ l₂ with
  | nil => exact h
  | cons y ys ih => exact ih (derLB_congr y h)

theorem derLA_word_congr {α} (tl : List α) {l₁ l₂ : kLang α n} (h : l₁ ≐ l₂) : derLA_word tl l₁ ≐ derLA_word tl l₂ := by
  induction tl generalizing n l₁ l₂ with
  | nil => exact h
  | cons y ys ih => exact ih (derLA_congr y h)

theorem der_word_correct {α} [DecidableEq α] (w : List α) (r : SRegex α) (n : Nat) :
    der_word w (sem r n) ≐ sem (D_word w r) (n + w.length) := by
  induction w generalizing r n with
  | nil => intro u; simp [der_word, D_word]
  | cons whd wtl ih =>
    intro u
    have h := (der_word_congr wtl (der_correct whd r n) u).trans (ih (D whd r) (n + 1) u)
    have e : HAdd.hAdd (HAdd.hAdd n 1) wtl.length = HAdd.hAdd n (HAdd.hAdd wtl.length 1) := by omega
    exact h.trans (by rw [e]; rfl)

theorem derLB_word_correct {α} [DecidableEq α] (w : List α) (r : SRegex α) (n : Nat) :
    derLB_word w (sem r n) ≐ sem (DLB_word w r) (n + w.length) := by
  induction w generalizing r n with
  | nil => intro u; simp [derLB_word, DLB_word]
  | cons whd wtl ih =>
    intro u
    have h := (derLB_word_congr wtl (derLB_correct whd r n) u).trans (ih (DLB whd r) (n + 1) u)
    have e : HAdd.hAdd (HAdd.hAdd n 1) wtl.length = HAdd.hAdd n (HAdd.hAdd wtl.length 1) := by omega
    exact h.trans (by rw [e]; rfl)

theorem derLA_word_correct {α} [DecidableEq α] (w : List α) (r : SRegex α) (n : Nat) :
    derLA_word w (sem r n) ≐ sem (DLA_word w r) (n + w.length) := by
  induction w generalizing r n with
  | nil => intro u; simp [derLA_word, DLA_word]
  | cons whd wtl ih =>
    intro u
    have h := (derLA_word_congr wtl (derLA_correct whd r n) u).trans (ih (DLA whd r) (n + 1) u)
    have e : HAdd.hAdd (HAdd.hAdd n 1) wtl.length = HAdd.hAdd n (HAdd.hAdd wtl.length 1) := by omega
    exact h.trans (by rw [e]; rfl)

/-- Theorem 4.2.3 — correctness of the existential derivative: `⟦xD_w r⟧ = xder_w ⟦r⟧`. -/
theorem xder_correct {α} [DecidableEq α] (s : List α) (r : SRegex α) (n : Nat) :
    xder s (sem r n) ≐ sem (xD s r) (n + s.length) := by
  induction s generalizing r n with
  | nil => intro w; simp [xder, xD]
  | cons a tl ih =>
    intro w
    have : (derLB a (sem r n) ∪ der a (sem r n) ∪ derLA a (sem r n)) ≐
        SRegex.sem (.plus (.plus (DLB a r) (D a r)) (DLA a r)) (n + 1) := by
      intro u; simp [SRegex.sem, kOperators.union, Operators.union, derLB_correct a r n u, der_correct a r n u, derLA_correct a r n u, or_assoc]
    have h := (xder_congr tl _ _ this w).trans (ih (.plus (.plus (DLB a r) (D a r)) (DLA a r)) (n + 1) w)
    have e : HAdd.hAdd (HAdd.hAdd n 1) tl.length = HAdd.hAdd n (HAdd.hAdd tl.length 1) := by omega
    exact h.trans (by rw [e]; rfl)

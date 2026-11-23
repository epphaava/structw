import Thesis.Semantics.kLang.«1_StructuredWords»
import Thesis.Semantics.kLang.«2_Operators»
import Thesis.Semantics.kLang.«3_Derivatives»
import Thesis.Semantics.kLang.«8_AlgebraicLaws»
import Thesis.Semantics.Lang.«7_DerivativeLaws»


namespace kderLaws

open StructuredWords
open kStructuredWords
open kOperators
open Operators
open kDerivatives
open derLaws
open helpers

-- Proposition 3.4.1 (Derivative laws for structured languages).

theorem der_empty (a : α) : der a (∅ : kLang α n) ≐ (∅ : kLang α (n.succ)) := by
  exact derLaws.der_empty a

theorem der_unit (a : α) : der a (I : kLang α n) ≐ (∅ : kLang α (n.succ)) := by
  intro w
  match w with
  | .left _ _ _ => simp [kDerivatives.der, Derivatives.der, kOperators.unit, Operators.empty, kOperators.empty]
  | .middle mcount _ _ => cases mcount <;> simp [kDerivatives.der, Derivatives.der, kOperators.unit, Operators.empty, kOperators.empty, Operators.unit]
  | .right mcount lacount _ => cases mcount <;> cases lacount <;> simp [kDerivatives.der, Derivatives.der, kOperators.unit, Operators.empty, kOperators.empty, Operators.unit]

theorem der_top (a : α): der a (T : kLang α n) ≐ (↑₂ (T : kLang α n) - ↑₃ (T : kLang α n)) := by
  intro w
  match w with
  | .left _ _ _ => simp [kDerivatives.der, Derivatives.der, kOperators.complement, Operators.complement, kOperators.matchStep, Operators.matchStep, kOperators.laStep, Operators.laStep]
  | .middle mcount _ _ => cases mcount <;> simp [kDerivatives.der, Derivatives.der, kOperators.complement, Operators.complement, kOperators.matchStep, Operators.matchStep, kOperators.laStep, Operators.laStep, kOperators.top, Word.word_steps, toList]
  | .right mcount lacount _ => cases mcount <;> cases lacount <;> simp [kDerivatives.der, Derivatives.der, kOperators.complement, Operators.complement, kOperators.matchStep, Operators.matchStep, kOperators.laStep, Operators.laStep, kOperators.top, Word.word_steps] <;> omega

theorem der_symb_match (a b : α) (h : a = b) : der b (#a : kLang α n) ≐ ((↑₂ I - ↑₃ T) : kLang α (n.succ)) := by
  intro w
  match w with
  | .left _ _ _ => simp [kDerivatives.der, Derivatives.der, kOperators.complement, Operators.complement, kOperators.matchStep, Operators.matchStep, kOperators.laStep, Operators.laStep]
  | .middle mcount _ _ => cases mcount <;> simp [kDerivatives.der, Derivatives.der, kOperators.complement, Operators.complement, kOperators.matchStep, Operators.matchStep, kOperators.laStep, Operators.laStep, kOperators.top, Word.word_steps, toList, kOperators.symb, Operators.symb, kOperators.unit, Operators.unit]
  | .right mcount lacount _ => rcases mcount with _ | _ | mcount <;> cases lacount <;> simp [kDerivatives.der, Derivatives.der, kOperators.complement, Operators.complement, kOperators.matchStep, Operators.matchStep, kOperators.laStep, Operators.laStep, kOperators.top, Word.word_steps, toList, kOperators.symb, Operators.symb, kOperators.unit, Operators.unit] <;> omega

theorem der_symb_no_match (a b : α) (h : a ≠ b) : der b (#a : kLang α n) ≐ (∅ : kLang α (n.succ)) := by
  exact derLaws.der_symb_no_match a b h

theorem der_union (a : α) (k l : kLang α n) : der a (k ∪ l) ≐ der a k ∪ der a l := by
  exact derLaws.der_union a k.1 l.1

theorem der_intersection (a : α) (k l : kLang α n): der a (k ∩ l) ≐ (der a k) ∩ (der a l) := by
  exact derLaws.der_intersection a k.1 l.1

theorem der_complement (a : α) (k l : kLang α n): der a (k - l) ≐ ((der a k) - (der a l)) := by
  exact derLaws.der_complement a k.1 l.1

theorem der_concat (a : α) (k l : kLang α n) : der a (k • l) ≐ ((der a k) • (derLB a l)) ∪ ((derLA a k) • (der a l)) := by
  exact derLaws.der_concat a k.1 l.1

theorem der_star (a : α) (l base : kLang α n) : der a (star l base) ≐ star (derLA a l) I • ((der a base) ∪ ((der a l) • star (derLB a l) (derLB a base))) := by
  have to_bounded : ∀ u, Operators.star (derLA a l).1 Operators.unit u → u.word_steps ≤ n.succ →
      Operators.star (derLA a l).1 (kOperators.unit : kLang α (n.succ)).1 u := by
    intro u hu
    induction hu with
    | inUnit u hb => exact λ hs => .inUnit _ ⟨hs, hb⟩
    | inConcat u₁ u₂ u hd _ hwc ih =>
      exact λ hs => .inConcat u₁ u₂ u hd (ih (Nat.le_trans (wc_steps_le hwc).2 hs)) hwc
  have from_bounded : ∀ u, Operators.star (derLA a l).1 (kOperators.unit : kLang α (n.succ)).1 u →
      Operators.star (derLA a l).1 Operators.unit u := by
    intro u hu
    induction hu with
    | inUnit u hb => exact .inUnit _ hb.2
    | inConcat u₁ u₂ u hd _ hwc ih => exact .inConcat u₁ u₂ u hd ih hwc
  intro w
  have hlang := derLaws.der_star a l.1 base.1 w
  constructor
  · intro h
    obtain ⟨u, v, hu, hv, hwc⟩ := hlang.1 h
    have hw := (der a (star l base)).2 w h
    exact ⟨u, v, to_bounded u hu (Nat.le_trans (wc_steps_le hwc).1 hw), hv, hwc⟩
  · intro ⟨u, v, hu, hv, hwc⟩
    exact hlang.2 ⟨u, v, from_bounded u hu, hv, hwc⟩

theorem der_lb (a : α) (l : kLang α n) : der a (◁ l) ≐ (∅ : kLang α n.succ) := by
  exact derLaws.der_lb a l.1

theorem der_la (a : α) (l : kLang α n) : der a (▷ l) ≐ (∅ : kLang α n.succ) := by
  exact derLaws.der_la a l.1

theorem der_matchStep (a : α) (l : kLang α n) : der a (↑₂ l) ≐ ↑₂ (der a l) := by
  exact derLaws.der_matchStep a l.1

theorem der_LAStep (a : α) (l : kLang α n) : der a (↑₃ l) ≐ (∅ : kLang α n.succ) := by
  exact derLaws.der_laStep a l.1

end kderLaws

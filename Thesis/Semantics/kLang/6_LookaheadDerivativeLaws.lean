import Thesis.Semantics.kLang.«1_StructuredWords»
import Thesis.Semantics.kLang.«2_Operators»
import Thesis.Semantics.kLang.«3_Derivatives»
import Thesis.Semantics.Lang.«3_Derivatives»
import Thesis.Semantics.Lang.«6_LookaheadDerivativeLaws»


namespace kderLALaws

open StructuredWords
open kStructuredWords
open kOperators
open kDerivatives
open Derivatives
open derLALaws


-- Proposition 3.4.1 (Derivative laws for structured languages).

theorem derLA_empty (a : α) : derLA a (∅ : kLang α n) ≐ (∅ : kLang α (n + 1)) := by
  exact derLALaws.derLA_empty a

theorem derLA_unit (a : α) : derLA a (I : kLang α n) ≐ ↑₃ (I : kLang α n) := by
  intro w
  match w with
  | .left _ _ _ => simp [kDerivatives.derLA, Derivatives.derLA, kOperators.laStep, kOperators.unit, Operators.laStep, Operators.unit, Word.word_steps]
  | .middle mcount _ _ => cases mcount <;> simp [kDerivatives.derLA, Derivatives.derLA, kOperators.laStep, kOperators.unit, Operators.laStep, Operators.unit, Word.word_steps]
  | .right mcount lacount _ => cases mcount <;> cases lacount <;> simp [kDerivatives.derLA, Derivatives.derLA, kOperators.laStep, kOperators.unit, Operators.laStep, Operators.unit, Word.word_steps]

theorem derLA_top (a : α) : derLA a (T : kLang α n) ≐ ↑₃ (T : kLang α n) := by
  intro w
  match w with
  | .left _ _ _ => simp [kDerivatives.derLA, Derivatives.derLA, kOperators.laStep, kOperators.laStep, kOperators.top, Operators.laStep, Word.word_steps]
  | .middle mcount _ _ => cases mcount <;> simp [kDerivatives.derLA, Derivatives.derLA, kOperators.laStep, kOperators.laStep, kOperators.top, Operators.laStep, Word.word_steps]
  | .right mcount lacount _ => cases mcount <;> cases lacount <;> simp [kDerivatives.derLA, Derivatives.derLA, kOperators.laStep, kOperators.laStep, kOperators.top, Operators.laStep, Word.word_steps] <;> omega

theorem derLA_symb (a b : α) : derLA b (#a : kLang α n) ≐ (∅ : kLang α (n.succ)) := by
  exact derLALaws.derLA_symb a b

theorem derLA_union (a : α) (k l : kLang α n) : derLA a (k ∪ l) ≐ derLA a k ∪ derLA a l := by
  exact derLALaws.derLA_union a k.1 l.1

theorem derLA_intersection (a : α) (k l : kLang α n): derLA a (k ∩ l) ≐ (derLA a k) ∩ (derLA a l) := by
  exact derLALaws.derLA_intersection a k.1 l.1

theorem derLA_complement (a : α) (k l : kLang α n): derLA a (k - l) ≐ ((derLA a k) - (derLA a l)) := by
  exact derLALaws.derLA_complement a k.1 l.1

theorem derLA_concat (a : α) (k l : kLang α n) : derLA a (k • l) ≐ derLA a k • derLA a l := by
  exact derLALaws.derLA_concat a k.1 l.1

theorem derLA_star (a : α) (l base : kLang α n) : derLA a (star l base) ≐ star (derLA a l) (derLA a base) := by
  exact derLALaws.derLA_star a l.1 base.1
  
theorem derLA_lb (a : α) (l : kLang α n) : derLA a (◁ l) ≐ ◁ (derLA a l) := by
  exact derLALaws.derLA_lb a l.1

theorem derLA_la (a : α) (l : kLang α n) : derLA a (▷ l) ≐ ▷ (der a l) := by
  exact derLALaws.derLA_la a l.1

theorem derLA_matchStep (a : α) (l : kLang α n) : derLA a (↑₂ l) ≐ ↑₂ (derLA a l) := by
  exact derLALaws.derLA_matchStep a l.1

theorem derLA_laStep (a : α) (l : kLang α n) : derLA a (↑₃ l) ≐ ↑₃ (derLA a l) := by
  exact derLALaws.derLA_laStep a l.1

end kderLALaws

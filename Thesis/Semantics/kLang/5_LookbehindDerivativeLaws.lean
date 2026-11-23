import Thesis.Semantics.kLang.«1_StructuredWords»
import Thesis.Semantics.kLang.«2_Operators»
import Thesis.Semantics.kLang.«3_Derivatives»
import Thesis.Semantics.Lang.«3_Derivatives»
import Thesis.Semantics.Lang.«5_LookbehindDerivativeLaws»


namespace kderLBLaws

open StructuredWords
open kStructuredWords
open kOperators
open kDerivatives
open Derivatives
open derLBLaws

-- Proposition 3.4.1 (Derivative laws for structured languages).

theorem derLB_empty (a : α) : derLB a (∅ : kLang α n) ≐ (∅ : kLang α (n.succ)) := by
  exact derLBLaws.derLB_empty a

theorem derLB_unit (a : α) : derLB a (I : kLang α n) ≐ (I - ↑₃ I : kLang α (n.succ)) := by
  intro w
  match w with
  | .left _ _ _ => simp [kOperators.complement, kDerivatives.derLB, Derivatives.derLB, kOperators.laStep, kOperators.unit, Operators.complement, Operators.laStep, Operators.unit, Word.word_steps]
  | .middle mcount _ _ => cases mcount <;> simp [kOperators.complement, kDerivatives.derLB, Derivatives.derLB, kOperators.laStep, kOperators.unit, toList, Operators.complement, Operators.laStep, Operators.unit, Word.word_steps]
  | .right mcount lacount _ => cases mcount <;> cases lacount <;> simp [kOperators.complement, kDerivatives.derLB, Derivatives.derLB, kOperators.laStep, kOperators.unit, Operators.complement, Operators.laStep, Operators.unit, Word.word_steps]

theorem derLB_top (a : α) : derLB a (T : kLang α n) ≐ (T - (↑₂ T ∪ ↑₃ T ) : kLang α (n.succ)) := by
  intro w
  match w with
  | .left _ _ _ => simp [kOperators.union, kOperators.complement, kDerivatives.derLB, Derivatives.derLB, kOperators.matchStep, kOperators.laStep, kOperators.top, Operators.union, Operators.complement, Operators.matchStep, Operators.laStep, Word.word_steps]
  | .middle mcount _ _ => cases mcount <;> simp [kOperators.union, kOperators.complement, kDerivatives.derLB, Derivatives.derLB, kOperators.matchStep, kOperators.laStep, kOperators.top, Operators.union, Operators.complement, Operators.matchStep, Operators.laStep, Word.word_steps]
  | .right mcount lacount _ => cases mcount <;> cases lacount <;> simp [kOperators.union, kOperators.complement, kDerivatives.derLB, Derivatives.derLB, kOperators.matchStep, kOperators.laStep, kOperators.top, Operators.union, Operators.complement, Operators.matchStep, Operators.laStep, Word.word_steps] <;> omega


theorem derLB_symb (a b : α) : derLB b (#a : kLang α n) ≐ (#a - (↑₂ #a ∪ ↑₃ #a) : kLang α (n.succ)) := by
  exact derLBLaws.derLB_symb a b

theorem derLB_union (a : α) (k l : kLang α n) : derLB a (k ∪ l) ≐ derLB a k ∪ derLB a l := by
  exact derLBLaws.derLB_union a k.1 l.1

theorem derLB_intersection (a : α) (k l : kLang α n): derLB a (k ∩ l) ≐ (derLB a k) ∩ (derLB a l) := by
  exact derLBLaws.derLB_intersection a k.1 l.1

theorem derLB_complement (a : α) (k l : kLang α n): derLB a (k - l) ≐ ((derLB a k) - (derLB a l)) := by
  exact derLBLaws.derLB_complement a k.1 l.1

theorem derLB_concat (a : α) (k l : kLang α n) : derLB a (k • l) ≐ derLB a k • derLB a l := by
  exact derLBLaws.derLB_concat a k.1 l.1

theorem derLB_star (a : α) (l base : kLang α n) : derLB a (star l base) ≐ star (derLB a l) (derLB a base) := by
  exact derLBLaws.derLB_star a l.1 base.1

theorem derLB_lb (a : α) (l : kLang α n) : derLB a (◁ l) ≐ ◁ (der a l) := by
  exact derLBLaws.derLB_lb a l.1

theorem derLB_la (a : α) (l : kLang α n) : derLB a (▷ l) ≐ ▷ (derLB a l) := by
  exact derLBLaws.derLB_la a l.1

theorem derLB_matchStep (a : α) (l : kLang α n) : derLB a (↑₂ l) ≐ (∅ : kLang α (n + 2)) := by
  exact derLBLaws.derLB_matchStep a l.1

theorem derLB_LAStep (a : α) (l : kLang α n) : derLB a (↑₃ l) ≐ (∅ : kLang α (n + 2)) := by
  exact derLBLaws.derLB_LAStep a l.1

end kderLBLaws

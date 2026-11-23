import Thesis.Semantics.kLang.«1_StructuredWords»
import Thesis.Semantics.kLang.«2_Operators»
import Thesis.Semantics.kLang.«3_Derivatives»

namespace kNullabilityLaws

open StructuredWords
open kStructuredWords
open kOperators
open kDerivatives

theorem nullable_empty : ¬ nullable (∅ : kLang α n) mc lac := by
  simp [nullable, empty, Operators.empty]

theorem nullable_unit : nullable (I : kLang α n) mc lac ↔ mc = 0 ∧ lac ≤ n := by
  simp [nullable, unit, Operators.unit, word_steps]; omega

theorem nullable_top : nullable (T : kLang α n) mc lac ↔ mc + lac ≤ n := by
  simp [nullable, top, word_steps]

theorem nullable_symb (a : α) : ¬ nullable (#a : kLang α n) mc lac := by
  simp [nullable, symb, Operators.symb]

theorem nullable_union (k l : kLang α n) : nullable (k ∪ l) mc lac ↔ nullable k mc lac ∨ nullable l mc lac := by
  simp [nullable, union, Operators.union]

theorem nullable_intersection (k l : kLang α n) : nullable (k ∩ l) mc lac ↔ nullable k mc lac ∧ nullable l mc lac := by
  simp [nullable, intersection, Operators.intersection]

theorem nullable_diff (k l : kLang α n) : nullable (k - l) mc lac ↔ nullable k mc lac ∧ ¬ nullable l mc lac := by
  simp [nullable, complement, Operators.complement]

theorem nullable_concat (k l : kLang α n) : nullable (k • l) mc lac ↔ (∃ mc₁ mc₂, mc = mc₁ + mc₂ ∧ nullable k mc₁ (mc₂ + lac) ∧ nullable l mc₂ lac) := by
  constructor
  . rintro ⟨w₁, w₂, hk, hl, mc₁, mc₂, hn, rfl, rfl⟩; exact ⟨mc₁, mc₂, hn, hk, hl⟩
  . intro ⟨mc₁, mc₂, hn, hk, hl⟩; exact ⟨.right mc₁ (mc₂ + lac) [], .right mc₂ lac [], hk, hl, mc₁, mc₂, hn, rfl, rfl⟩

theorem nullable_star (l base : kLang α n) : nullable (star l base) mc lac ↔ nullable base mc lac ∨ ∃ mc₁ mc₂, mc = mc₁ + mc₂ ∧ nullable l mc₁ (mc₂ + lac) ∧ nullable (star l base) mc₂ lac := by
  constructor
  . intro hs;
    cases hs with
    | inUnit _ hbase => exact .inl hbase
    | inConcat w₁ w₂ _ hl hs hwc => obtain ⟨mc₁, mc₂, hn, rfl, rfl⟩ := hwc; exact .inr ⟨mc₁, mc₂, hn, hl, hs⟩
  . rintro (hbase | ⟨mc₁, mc₂, hn, hl, hs⟩)
    . exact .inUnit _ hbase
    . exact .inConcat _ _ _ hl hs ⟨mc₁, mc₂, hn, rfl, rfl⟩

theorem nullable_lookbehind (l : kLang α n) : nullable (◁ l) mc lac ↔ mc = 0 ∧ ∃ lbc ≤ n, nullable l lbc lac := by
  cases mc with
  | succ => simp [nullable, lookbehind, Operators.lookbehind]
  | zero =>
    simp only [nullable, lookbehind, Operators.lookbehind, true_and]
    constructor
    · intro ⟨lbc, hl⟩
      have h := l.2 _ hl
      exact ⟨lbc, by simp [word_steps] at h; omega, hl⟩
    · intro ⟨lbc, _, hl⟩; exact ⟨lbc, hl⟩

theorem nullable_lookahead (l : kLang α n) : nullable (▷ l) mc lac ↔ mc = 0 ∧ nullable l lac 0 := by
  cases mc <;> simp [nullable, lookahead, Operators.lookahead]

theorem nullable_matchStep (l : kLang α n) : nullable (↑₂ l) (.succ mc) lac ↔ nullable l mc lac := by
  simp [nullable, matchStep, Operators.matchStep]

theorem nullable_laStep (l : kLang α n) : nullable (↑₃ l) mc (.succ lac) ↔ nullable l mc lac := by
  simp [nullable, laStep, Operators.laStep]


end kNullabilityLaws

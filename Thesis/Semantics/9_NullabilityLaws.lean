import Thesis.Semantics.«1_StructuredWords»
import Thesis.Semantics.«2_Operators»
import Thesis.Semantics.«3_Derivatives»

namespace NullabilityLaws

open StructuredWords
open Operators

theorem nullable_empty : ¬ nullable (∅ : Lang α) mc lac := by simp [nullable, empty]

theorem nullable_unit : nullable (I : Lang α) mc lac ↔ mc = 0 := by simp [nullable, unit];

theorem nullable_top : nullable (T : Lang α) mc lac := by simp [nullable, top]

theorem nullable_symb (a : α) : ¬ nullable (#a : Lang α) mc lac := by simp [nullable, symb]

theorem nullable_union : nullable (k ∪ l) mc lac ↔ (nullable k mc lac) ∨ (nullable l mc lac) := by simp [nullable, union]

theorem nullable_intersection : nullable (k ∩ l) mc lac ↔ nullable k mc lac ∧ nullable l mc lac := by simp [nullable, intersection]

theorem nullable_diff : nullable (k - l) mc lac ↔ nullable k mc lac ∧ ¬ nullable l mc lac := by simp [nullable, complement]

theorem nullable_concat : nullable (k • l) mc lac ↔ (∃ mc₁ mc₂, mc = mc₁ + mc₂ ∧ nullable k mc₁ (mc₂ + lac) ∧ nullable l mc₂ lac) := by
  constructor
  . rintro ⟨w₁, w₂, hk, hl, mc₁, mc₂, hn, rfl, rfl⟩; exact ⟨mc₁, mc₂, hn, hk, hl⟩
  . intro ⟨mc₁, mc₂, hn, hk, hl⟩; exact ⟨.right mc₁ (mc₂ + lac) [], .right mc₂ lac [], hk, hl, mc₁, mc₂, hn, rfl, rfl⟩

theorem nullable_star (l base : Lang α) : nullable (star l base) mc lac ↔
    nullable base mc lac ∨ ∃ mc₁ mc₂, mc = mc₁ + mc₂ ∧ nullable l mc₁ (mc₂ + lac) ∧ nullable (star l base) mc₂ lac := by
  constructor
  . intro h; unfold star at h
    cases h with
    | inUnit _ hbase => exact .inl hbase
    | inConcat w₁ w₂ _ hl hs hwc => obtain ⟨mc₁, mc₂, hn, rfl, rfl⟩ := hwc; exact .inr ⟨mc₁, mc₂, hn, hl, hs⟩
  . rintro (hbase | ⟨mc₁, mc₂, hn, hl, hs⟩)
    . exact .inUnit _ hbase
    . exact .inConcat _ _ _ hl hs ⟨mc₁, mc₂, hn, rfl, rfl⟩

theorem nullable_lookbehind (l : Lang α) : nullable (◁ l) mc lac ↔ mc = 0 ∧ ∃ lbc, l (.right lbc lac []) := by cases mc <;> simp [nullable, lookbehind]

theorem nullable_lookahead (l : Lang α) : nullable (▷ l) mc lac ↔ mc = 0 ∧ l (.right lac 0 []) := by cases mc <;> simp [nullable, lookahead]

theorem nullable_matchStep : nullable (↑₂l) (.succ mc) lac ↔ nullable l mc lac := by simp only [nullable, matchStep]

theorem nullable_LAStep : nullable (↑₃l) mc (.succ lac) ↔ nullable l mc lac := by simp only [nullable, laStep]



theorem xnullable_empty : ¬ xnullable (∅ : Lang α) := by simp [xnullable, nullable, empty]

theorem xnullable_unit : xnullable (I : Lang α) := by simp [xnullable, nullable, unit]

theorem xnullable_top : xnullable (T : Lang α) := by simp [xnullable, nullable, top]

theorem xnullable_symb (a : α) : ¬ xnullable (#a : Lang α) := by simp [xnullable, nullable, symb]

theorem xnullable_union (l k : Lang α) : xnullable (k ∪ l) ↔ (xnullable k) ∨ (xnullable l) := by
  constructor
  . rintro ⟨mc, lac, hk | hl⟩
    . exact .inl ⟨mc, lac, hk⟩
    . exact .inr ⟨mc, lac, hl⟩
  . rintro (⟨mc, lac, hk⟩ | ⟨mc, lac, hl⟩)
    . exact ⟨mc, lac, .inl hk⟩
    . exact ⟨mc, lac, .inr hl⟩

theorem xnullable_intersection : xnullable (k ∩ l) ↔ ∃ mc lac, nullable k mc lac ∧ nullable l mc lac := by
  constructor
  . intro ⟨mc, lac, h⟩; exact ⟨mc, lac, nullable_intersection.mp h⟩
  . intro ⟨mc, lac, h⟩; exact ⟨mc, lac, nullable_intersection.mpr h⟩

theorem xnullable_diff : xnullable (k - l) ↔ ∃ mc lac, nullable k mc lac ∧ ¬ nullable l mc lac := by
  constructor
  . intro ⟨mc, lac, h⟩; exact ⟨mc, lac, nullable_diff.mp h⟩
  . intro ⟨mc, lac, h⟩; exact ⟨mc, lac, nullable_diff.mpr h⟩

theorem xnullable_concat : xnullable (k • l) ↔ (∃ mc₁ mc₂ lac, nullable k mc₁ (mc₂ + lac) ∧ nullable l mc₂ lac) := by
  constructor
  . intro ⟨_, lac, h⟩
    obtain ⟨mc₁, mc₂, _, hk, hl⟩ := nullable_concat.mp h
    exact ⟨mc₁, mc₂, lac, hk, hl⟩
  . intro ⟨mc₁, mc₂, lac, hk, hl⟩
    exact ⟨mc₁ + mc₂, lac, nullable_concat.mpr ⟨mc₁, mc₂, rfl, hk, hl⟩⟩

theorem xnullable_star (l base : Lang α) : xnullable (star l base) ↔ xnullable base := by
  constructor
  . intro ⟨mcount, lacount, h⟩
    unfold star nullable at h
    generalize hw : Word.right mcount lacount [] = w at h
    induction h generalizing mcount with
    | inUnit _ hbase => subst hw; exact ⟨mcount, lacount, hbase⟩
    | inConcat w₁ w₂ _ _ _ hwc ih =>
      subst hw; obtain ⟨mc₁, mc₂, _, _, rfl⟩ := hwc
      exact ih mc₂ rfl
  . intro ⟨mcount, lacount, hbase⟩; exact ⟨mcount, lacount, .inUnit _ hbase⟩

/-- The lookbehind's content may have any match count, so `◁ l` is nullable exactly when `l` is. -/
theorem xnullable_lookbehind (l : Lang α) : xnullable (◁ l) ↔ xnullable l := by
  constructor
  . intro ⟨mc, lac, h⟩
    cases mc with
    | zero => obtain ⟨k, h⟩ := h; exact ⟨k, lac, h⟩
    | succ n => simp [nullable, lookbehind] at h
  . intro ⟨mc, lac, h⟩; exact ⟨0, lac, mc, h⟩

theorem xnullable_lookahead (l : Lang α) : xnullable (▷ l) ↔ ∃ mc, nullable l mc 0 := by
  constructor
  . intro ⟨mc, lac, h⟩
    cases mc with
    | zero => exact ⟨lac, h⟩
    | succ mc => simp [nullable, lookahead] at h
  . intro ⟨mc, h⟩; exact ⟨0, mc, h⟩

theorem xnullable_matchStep : xnullable (↑₂l) ↔ xnullable l := by
  constructor
  . intro ⟨mc, lac, h⟩
    cases mc with
    | zero => simp [nullable, matchStep] at h
    | succ mc => exact ⟨mc, lac, h⟩
  . intro ⟨mc, lac, h⟩; exact ⟨mc.succ, lac, h⟩

theorem xnullable_LAStep : xnullable (↑₃l) ↔ xnullable l := by
  constructor
  . intro ⟨mc, lac, h⟩
    cases lac with
    | zero => simp [nullable, laStep] at h
    | succ lac => exact ⟨mc, lac, h⟩
  . intro ⟨mc, lac, h⟩; exact ⟨mc, lac.succ, h⟩

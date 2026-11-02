import Thesis.Semantics.«1_StructuredWords»
import Thesis.Semantics.«2_Operators»
import Thesis.Semantics.«3_Derivatives»

namespace NullabilityLaws

open StructuredWords
open Operators

theorem nullable_empty : ¬ nullable (∅ : Lang α)  lbc mc lac := by simp [nullable, empty]

theorem nullable_unit : nullable (I : Lang α) lbc mc lac ↔ mc = 0 := by simp [nullable, unit];

theorem nullable_top : nullable (T : Lang α) lbc mc lac := by simp [nullable, top]

theorem nullable_symb (a : α) : ¬ nullable (#a : Lang α) lbc mc lac := by simp [nullable, symb]

theorem nullable_union : nullable (k ∪ l) lbc mc lac ↔ (nullable k lbc mc lac) ∨ (nullable l lbc mc lac) := by simp [nullable, union]

theorem nullable_intersection : nullable (k ∩ l) lbc mc lac ↔ nullable k lbc mc lac ∧ nullable l lbc mc lac := by simp [nullable, intersection]

theorem nullable_diff : nullable (k - l) lbc mc lac ↔ nullable k lbc mc lac ∧ ¬ nullable l lbc mc lac := by simp [nullable, complement]

theorem nullable_concat : nullable (k • l) lbc mc lac ↔ (∃ mc₁ mc₂, mc = mc₁ + mc₂ ∧ nullable k lbc mc₁ (mc₂ + lac) ∧ nullable l (lbc + mc₁) mc₂ lac) := by
  constructor
  . rintro ⟨w₁, w₂, hk, hl, mc₁, mc₂, hn, rfl, rfl⟩; exact ⟨mc₁, mc₂, hn, hk, hl⟩
  . intro ⟨mc₁, mc₂, hn, hk, hl⟩; exact ⟨.right lbc mc₁ (mc₂ + lac) [], .right (lbc + mc₁) mc₂ lac [], hk, hl, mc₁, mc₂, hn, rfl, rfl⟩

theorem nullable_star (l base : Lang α) : nullable (star l base) lbc mc lac ↔
    nullable base lbc mc lac ∨ ∃ mc₁ mc₂, mc = mc₁ + mc₂ ∧ nullable l lbc mc₁ (mc₂ + lac) ∧ nullable (star l base) (lbc + mc₁) mc₂ lac := by
  constructor
  . intro h; unfold star at h
    cases h with
    | inUnit _ hbase => exact .inl hbase
    | inConcat w₁ w₂ _ hl hs hwc => obtain ⟨mc₁, mc₂, hn, rfl, rfl⟩ := hwc; exact .inr ⟨mc₁, mc₂, hn, hl, hs⟩
  . rintro (hbase | ⟨mc₁, mc₂, hn, hl, hs⟩)
    . exact .inUnit _ hbase
    . exact .inConcat _ _ _ hl hs ⟨mc₁, mc₂, hn, rfl, rfl⟩

theorem nullable_lookbehind (l : Lang α) : nullable (◁ l) lbc mc lac ↔ mc = 0 ∧ l (.right 0 lbc lac []) := by cases mc <;> simp [nullable, lookbehind]

theorem nullable_lookahead (l : Lang α) : nullable (▷ l) lbc mc lac ↔ mc = 0 ∧ l (.right lbc lac 0 []) := by cases mc <;> simp [nullable, lookahead]

theorem nullable_lbStep : nullable (↑₁l) (.succ lbc) mc lac ↔ nullable l lbc mc lac := by simp [nullable, lbStep]

theorem nullable_matchStep : nullable (↑₂l) lbc (.succ mc) lac ↔ nullable l lbc mc lac := by simp only [nullable, matchStep]

theorem nullable_LAStep : nullable (↑₃l) lbc mc (.succ lac) ↔ nullable l lbc mc lac := by simp only [nullable, laStep]





theorem xnullable_empty : ¬ xnullable (∅ : Lang α) := by simp [xnullable, nullable, empty]

theorem xnullable_unit : xnullable (I : Lang α) := by simp [xnullable, nullable, unit]

theorem xnullable_top : xnullable (T : Lang α) := by simp [xnullable, nullable, top]

theorem xnullable_symb (a : α) : ¬ xnullable (#a : Lang α) := by simp [xnullable, nullable, symb]

theorem xnullable_union (l k : Lang α) : xnullable (k ∪ l) ↔ (xnullable k) ∨ (xnullable l) := by
  constructor
  . rintro ⟨mc, lac, hb, hk | hl⟩
    . exact .inl ⟨mc, lac, hb, hk⟩
    . exact .inr ⟨mc, lac, hb, hl⟩
  . rintro (⟨mc, lac, hb, hk⟩ | ⟨mc, lac, hb, hl⟩)
    . exact ⟨mc, lac, hb, .inl hk⟩
    . exact ⟨mc, lac, hb, .inr hl⟩

theorem xnullable_intersection : xnullable (k ∩ l) ↔ ∃ lbc mc lac, nullable k lbc mc lac ∧ nullable l lbc mc lac := by
  constructor
  . intro ⟨lbc, mc, lac, h⟩; exact ⟨lbc, mc, lac, nullable_intersection.mp h⟩
  . intro ⟨lbc, mc, lac, h⟩; exact ⟨lbc, mc, lac, nullable_intersection.mpr h⟩

theorem xnullable_diff : xnullable (k - l) ↔ ∃ lbc mc lac, nullable k lbc mc lac ∧ ¬ nullable l lbc mc lac := by
  constructor
  . intro ⟨lbc, mc, lac, h⟩; exact ⟨lbc, mc, lac, nullable_diff.mp h⟩
  . intro ⟨lbc, mc, lac, h⟩; exact ⟨lbc, mc, lac, nullable_diff.mpr h⟩

theorem xnullable_concat : xnullable (k • l) ↔ (∃ lbc mc₁ mc₂ lac, nullable k lbc mc₁ (mc₂ + lac) ∧ nullable l (lbc + mc₁) mc₂ lac) := by
  constructor
  . intro ⟨lbc, _, lacount, h⟩
    obtain ⟨mc₁, mc₂, _, hk, hl⟩ := nullable_concat.mp h
    exact ⟨lbc, mc₁, mc₂, lacount, hk, hl⟩
  . intro ⟨lbc, mc₁, mc₂, lacount, hk, hl⟩
    exact ⟨lbc, mc₁ + mc₂, lacount, nullable_concat.mpr ⟨mc₁, mc₂, rfl, hk, hl⟩⟩

theorem xnullable_star (l base : Lang α) : xnullable (star l base) ↔ xnullable base := by
  constructor
  . intro ⟨lbcount, mcount, lacount, h⟩
    unfold star nullable at h
    generalize hw : Word.right lbcount mcount lacount [] = w at h
    induction h generalizing lbcount mcount with
    | inUnit _ hbase => subst hw; exact ⟨lbcount, mcount, lacount, hbase⟩
    | inConcat w₁ w₂ _ _ _ hwc ih =>
      subst hw; obtain ⟨mc₁, mc₂, _, _, rfl⟩ := hwc
      exact ih (lbcount + mc₁) mc₂ rfl
  . intro ⟨lbcount, mcount, lacount, hbase⟩; exact ⟨lbcount, mcount, lacount, .inUnit _ hbase⟩

theorem xnullable_lookbehind (l : Lang α) : xnullable (◁ l) ↔ ∃ mc lac, nullable l 0 mc lac := by
  constructor
  . intro ⟨lbc, mc, lac, h⟩
    cases mc with
    | zero => exact ⟨lbc, lac, h⟩
    | succ n => simp [nullable, lookbehind] at h
  . intro ⟨mc, lac, h⟩; exact ⟨mc, 0, lac, h⟩

theorem xnullable_lookahead (l : Lang α) : xnullable (▷ l) ↔ ∃ lbc mc, nullable l lbc mc 0 := by
  constructor
  . intro ⟨lbc, mc, lac, h⟩
    cases mc with
    | zero => exact ⟨lbc, lac, h⟩
    | succ mc => simp [nullable, lookahead] at h
  . intro ⟨lbc, mc, h⟩; exact ⟨lbc, 0, mc, h⟩

theorem xnullable_lbStep : xnullable (↑₁l) ↔ xnullable l := by
  constructor
  . intro ⟨lbc, mc, lac, h⟩
    cases lbc with
    | zero => simp [nullable, lbStep] at h
    | succ lbc => exact ⟨lbc, mc, lac, h⟩
  . intro ⟨lbc, mc, lac, h⟩; exact ⟨lbc.succ, mc, lac, h⟩

theorem xnullable_matchStep : xnullable (↑₂l) ↔ xnullable l := by
  constructor
  . intro ⟨lbc, mc, lac, h⟩
    cases mc with
    | zero => simp [nullable, matchStep] at h
    | succ mc => exact ⟨lbc, mc, lac, h⟩
  . intro ⟨lbc, mc, lac, h⟩; exact ⟨lbc, mc.succ, lac, h⟩


theorem xnullable_LAStep : xnullable (↑₃l) ↔ xnullable l  := by
  constructor
  . intro ⟨lbc, mc, lac, h⟩
    cases lac with
    | zero => simp [nullable, laStep] at h
    | succ lac => exact ⟨lbc, mc, lac, h⟩
  . intro ⟨lbc, mc, lac, h⟩; exact ⟨lbc, mc, lac.succ, h⟩

import Thesis.Semantics.«1_StructuredWords»
import Thesis.Semantics.«2_Operators»
import Thesis.Semantics.«3_Derivatives»

namespace NullabilityLaws

open StructuredWords
open Operators

theorem nullable_m_n_empty : ¬ nullable_m_n (∅ : Lang α) length n m := by rw [nullable_m_n, empty]; trivial

theorem nullable_m_n_unit (n : Nat) : nullable_m_n (I : Lang α) length n m  ↔ n == 0 := by simp [nullable_m_n, unit]

theorem nullable_m_n_top : nullable_m_n (T : Lang α) lenth n m := by rw [nullable_m_n, top]; trivial

theorem nullable_m_n_symb (a : α) : ¬ nullable_m_n (#a : Lang α) length n m := by simp [nullable_m_n, symb]

theorem nullable_m_n_union (l k : Lang α) n : nullable_m_n (k ∪ l) length n m ↔ (nullable_m_n k length n m) ∨ (nullable_m_n l length n m) := by simp [nullable_m_n, union]

theorem nullable_m_n_intersection : nullable_m_n (k ∩ l) length n m ↔ nullable_m_n k length n m ∧ nullable_m_n l length n m := by rw [nullable_m_n, intersection]; rfl

theorem nullable_m_n_diff : nullable_m_n (k - l) length n m ↔ nullable_m_n k length n m ∧ ¬ nullable_m_n l length n m := by rw [nullable_m_n, complement]; rfl

theorem nullable_m_n_concat : nullable_m_n (k • l) length n m ↔ (∃ mc₁ mc₂, n = mc₁ + mc₂ ∧ nullable_m_n k length mc₁ (mc₂ + m) ∧ nullable_m_n l length mc₂ m) := by
  simp [nullable_m_n]; constructor
  . intro ⟨w₁, w₂, hk, hl, mc₁, mc₂, hn, _, _⟩; subst w₁ w₂; exact ⟨mc₁, mc₂, hn, hk, hl⟩
  . intro ⟨mc₁, mc₂, hn, hk, hl⟩; exact ⟨.right mc₁ (mc₂ + m) [], .right mc₂ m [], hk, hl, mc₁, mc₂, hn, rfl, rfl⟩

theorem nullable_m_n_star (l base : Lang α) : nullable_m_n (star base l) length n m ↔
    nullable_m_n base length n m ∨
    ∃ mc₁ mc₂, n = mc₁ + mc₂ ∧ nullable_m_n l length mc₁ (mc₂ + m) ∧ nullable_m_n (star base l) length mc₂ m := by
  simp [nullable_m_n]; constructor
  . intro h
    cases h with
    | inUnit _ hb => exact .inl hb
    | inConcat w₁ w₂ _ hl hs hwc =>
      obtain ⟨mc₁, mc₂, hn, rfl, rfl⟩ := hwc
      exact .inr ⟨mc₁, mc₂, hn, hl, hs⟩
  . intro h
    rcases h with hb | ⟨mc₁, mc₂, hn, hl, hs⟩
    . exact .inUnit _ hb
    . exact .inConcat _ _ _ hl hs ⟨mc₁, mc₂, hn, rfl, rfl⟩


theorem nullable_m_n_lookbehind (l : Lang α) : nullable_m_n (◁ l) length n m ↔ n = 0 ∧ m = 0 ∧ ∃ mc, nullable_m_n l length mc 0 := by
  cases n <;> cases m <;> simp [nullable_m_n, lookbehind]

theorem nullable_m_n_lookahead (l : Lang α) : nullable_m_n (▷ l) length n m ↔ n = 0 ∧ nullable_m_n l length m 0 := by
  cases n <;> simp [nullable_m_n, lookahead]

theorem nullable_m_n_matchStep : nullable_m_n (▹ₘl) (.succ length) (.succ n) m ↔ nullable_m_n l length n m := by simp [nullable_m_n, matchStep]

theorem nullable_m_n_LAStep : nullable_m_n (▹ₗl) (.succ length) n (.succ m) ↔  nullable_m_n l length n m := by simp [nullable_m_n, LAStep]





theorem nullable_empty : ¬ nullable (∅ : Lang α) length := by simp [nullable, nullable_m_n, empty]

theorem nullable_unit : nullable (I : Lang α) length := by simp [nullable, nullable_m_n, unit]

theorem nullable_top : nullable (T : Lang α) length := by simp [nullable, nullable_m_n, top]

theorem nullable_symb (a : α) : ¬ nullable (#a : Lang α) length := by simp [nullable, nullable_m_n, symb]

theorem nullable_union (l k : Lang α) : nullable (k ∪ l) length ↔ (nullable k length) ∨ (nullable l length) := by
  constructor
  . rintro ⟨mc, lac, hk | hl⟩
    . exact .inl ⟨mc, lac, hk⟩
    . exact .inr ⟨mc, lac, hl⟩
  . rintro (⟨mc, lac, hk⟩ | ⟨mc, lac, hl⟩)
    . exact ⟨mc, lac, .inl hk⟩
    . exact ⟨mc, lac, .inr hl⟩

theorem nullable_intersection : nullable (k ∩ l) length ↔ ∃ mc lac, nullable_m_n k length mc lac ∧ nullable_m_n l length mc lac := by simp [intersection, nullable, nullable_m_n]

theorem nullable_diff : nullable (k - l) length ↔ ∃ mc lac, nullable_m_n k length mc lac ∧ ¬ nullable_m_n l length mc lac := by simp [complement, nullable_m_n, nullable]

theorem nullable_concat : nullable (k • l) length ↔ (∃ mc₁ mc₂ m, nullable_m_n k length mc₁ (mc₂ + m) ∧ nullable_m_n l length mc₂ m) := by
  constructor
  . intro ⟨mcount, lacount, w₁, w₂, hk, hl, mc₁, mc₂, hmcount, _, _⟩; subst w₁ w₂; exact ⟨mc₁, mc₂, lacount, hk, hl⟩
  . intro ⟨mc₁, mc₂, lacount, hk, hl⟩; exact ⟨(mc₁ + mc₂), lacount, .right mc₁ (mc₂ + lacount) [], .right mc₂ lacount [], hk, hl, mc₁, mc₂, rfl, rfl, rfl⟩

theorem nullable_star (l base : Lang α) : nullable (star base l) length ↔ nullable base length := by
  constructor
  . intro ⟨mcount, lacount, h⟩
    unfold nullable_m_n at h
    generalize hw : Word.right mcount lacount [] = w at h
    induction h generalizing mcount with
    | inUnit _ hb => subst hw; exact ⟨mcount, lacount, hb⟩
    | inConcat w₁ w₂ _ hl hs hwc ih =>
      subst hw
      obtain ⟨mc₁, mc₂, hn, rfl, rfl⟩ := hwc
      exact ih mc₂ rfl
  . intro ⟨mcount, lacount, hb⟩
    exact ⟨mcount, lacount, .inUnit _ hb⟩


theorem nullable_lookbehind (l : Lang α) : nullable (◁ l) length ↔ ∃ mc, nullable_m_n l length mc 0 := by
  constructor
  . intro ⟨n, m, h⟩; cases n <;> cases m <;> simp [nullable_m_n, lookbehind] at h; exact h
  . intro ⟨mc, h⟩; exact ⟨0, 0, by simp [nullable_m_n, lookbehind]; exact ⟨mc, h⟩⟩


theorem nullable_lookahead (l : Lang α) : nullable (▷ l) length ↔ ∃ mc, nullable_m_n l length mc 0 := by
  constructor
  . intro ⟨n, m, h⟩
    cases n with
    | zero => exact ⟨m, h⟩
    | succ n => simp [nullable_m_n, lookahead] at h
  . intro ⟨mc, h⟩; exact ⟨0, mc, h⟩


theorem nullable_matchStep : nullable (▹ₘl) (.succ length) ↔ nullable l length := by
  constructor
  . intro ⟨n, m, h⟩
    cases n with
    | zero => simp [nullable_m_n, matchStep] at h
    | succ n => exact ⟨n, m, h⟩
  . intro ⟨n, m, h⟩; exact ⟨n.succ, m, h⟩

theorem nullable_LAStep : nullable (▹ₗl) (.succ length) ↔ nullable l length := by
  constructor
  . intro ⟨n, m, h⟩
    cases m with
    | zero => simp [nullable_m_n, LAStep] at h
    | succ m => exact ⟨n, m, h⟩
  . intro ⟨n, m, h⟩; exact ⟨n, m.succ, h⟩

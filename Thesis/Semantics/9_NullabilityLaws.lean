import Thesis.Semantics.«1_StructuredWords»
import Thesis.Semantics.«2_Operators»
import Thesis.Semantics.«3_Derivatives»

namespace NullabilityLaws

open StructuredWords
open Operators

theorem nullable_m_n_empty : ¬ nullable_m_n (∅ : Lang α) length n m := by simp [nullable_m_n, empty]

theorem nullable_m_n_unit (n : Nat) : nullable_m_n (I : Lang α) length n m ↔ n = 0 ∧ m ≤ length := by
  simp [nullable_m_n, unit]; omega

theorem nullable_m_n_top (h : n + m ≤ length) : nullable_m_n (T : Lang α) length n m := ⟨h, trivial⟩

theorem nullable_m_n_symb (a : α) : ¬ nullable_m_n (#a : Lang α) length n m := by simp [nullable_m_n, symb]

theorem nullable_m_n_union (l k : Lang α) n : nullable_m_n (k ∪ l) length n m ↔ (nullable_m_n k length n m) ∨ (nullable_m_n l length n m) := by
  simp only [nullable_m_n, union]; exact and_or_left

theorem nullable_m_n_intersection : nullable_m_n (k ∩ l) length n m ↔ nullable_m_n k length n m ∧ nullable_m_n l length n m := by
  simp only [nullable_m_n, intersection]
  constructor
  . intro ⟨hb, hk, hl⟩; exact ⟨⟨hb, hk⟩, ⟨hb, hl⟩⟩
  . intro ⟨⟨hb, hk⟩, ⟨_, hl⟩⟩; exact ⟨hb, hk, hl⟩

theorem nullable_m_n_diff : nullable_m_n (k - l) length n m ↔ nullable_m_n k length n m ∧ ¬ nullable_m_n l length n m := by
  simp only [nullable_m_n, complement]
  constructor
  . intro ⟨hb, hk, hl⟩; exact ⟨⟨hb, hk⟩, fun ⟨_, h⟩ => hl h⟩
  . intro ⟨⟨hb, hk⟩, hl⟩; exact ⟨hb, hk, fun h => hl ⟨hb, h⟩⟩

theorem nullable_m_n_concat : nullable_m_n (k • l) length n m ↔ (∃ mc₁ mc₂, n = mc₁ + mc₂ ∧ nullable_m_n k length mc₁ (mc₂ + m) ∧ nullable_m_n l length mc₂ m) := by
  constructor
  . intro ⟨hb, w₁, w₂, hk, hl, mc₁, mc₂, hn, h₁, h₂⟩; subst h₁ h₂
    exact ⟨mc₁, mc₂, hn, ⟨by omega, hk⟩, ⟨by omega, hl⟩⟩
  . intro ⟨mc₁, mc₂, hn, ⟨hb, hk⟩, ⟨_, hl⟩⟩
    exact ⟨by omega, .right mc₁ (mc₂ + m) [], .right mc₂ m [], hk, hl, mc₁, mc₂, hn, rfl, rfl⟩

theorem nullable_m_n_star (l base : Lang α) : nullable_m_n (star base l) length n m ↔
    nullable_m_n base length n m ∨
    ∃ mc₁ mc₂, n = mc₁ + mc₂ ∧ nullable_m_n l length mc₁ (mc₂ + m) ∧ nullable_m_n (star base l) length mc₂ m := by
  constructor
  . intro ⟨hb, h⟩
    unfold star at h
    cases h with
    | inUnit _ hbase => exact .inl ⟨hb, hbase⟩
    | inConcat w₁ w₂ _ hl hs hwc =>
      obtain ⟨mc₁, mc₂, hn, rfl, rfl⟩ := hwc
      exact .inr ⟨mc₁, mc₂, hn, ⟨by omega, hl⟩, ⟨by omega, hs⟩⟩
  . rintro (⟨hb, hbase⟩ | ⟨mc₁, mc₂, hn, ⟨hb, hl⟩, ⟨_, hs⟩⟩)
    . exact ⟨hb, .inUnit _ hbase⟩
    . exact ⟨by omega, .inConcat _ _ _ hl hs ⟨mc₁, mc₂, hn, rfl, rfl⟩⟩

theorem nullable_m_n_lookbehind (l : Lang α) : nullable_m_n (◁ l) length n m ↔ n = 0 ∧ ∃ mc, mc + m = length ∧ l (.right mc m []) := by
  cases n <;> simp [nullable_m_n, lookbehind]

theorem nullable_m_n_lookahead (l : Lang α) : nullable_m_n (▷ l) length n m ↔ n = 0 ∧ nullable_m_n l length m 0 := by
  cases n <;> simp [nullable_m_n, lookahead]

theorem nullable_m_n_matchStep : nullable_m_n (▹ₘl) (.succ length) (.succ n) m ↔ nullable_m_n l length n m := by
  simp only [nullable_m_n, matchStep]
  constructor <;> (intro ⟨hb, h⟩; exact ⟨by omega, h⟩)

theorem nullable_m_n_LAStep : nullable_m_n (▹ₗl) (.succ length) n (.succ m) ↔ nullable_m_n l length n m := by
  simp only [nullable_m_n, LAStep]
  constructor <;> (intro ⟨hb, h⟩; exact ⟨by omega, h⟩)





theorem nullable_empty : ¬ nullable (∅ : Lang α) length := by simp [nullable, nullable_m_n, empty]

theorem nullable_unit : nullable (I : Lang α) length := ⟨0, 0, Nat.zero_le _, rfl⟩

theorem nullable_top : nullable (T : Lang α) length := ⟨0, 0, Nat.zero_le _, trivial⟩

theorem nullable_symb (a : α) : ¬ nullable (#a : Lang α) length := by simp [nullable, nullable_m_n, symb]

theorem nullable_union (l k : Lang α) : nullable (k ∪ l) length ↔ (nullable k length) ∨ (nullable l length) := by
  constructor
  . rintro ⟨mc, lac, hb, hk | hl⟩
    . exact .inl ⟨mc, lac, hb, hk⟩
    . exact .inr ⟨mc, lac, hb, hl⟩
  . rintro (⟨mc, lac, hb, hk⟩ | ⟨mc, lac, hb, hl⟩)
    . exact ⟨mc, lac, hb, .inl hk⟩
    . exact ⟨mc, lac, hb, .inr hl⟩

theorem nullable_intersection : nullable (k ∩ l) length ↔ ∃ mc lac, nullable_m_n k length mc lac ∧ nullable_m_n l length mc lac := by
  constructor
  . intro ⟨mc, lac, h⟩; exact ⟨mc, lac, nullable_m_n_intersection.mp h⟩
  . intro ⟨mc, lac, h⟩; exact ⟨mc, lac, nullable_m_n_intersection.mpr h⟩

theorem nullable_diff : nullable (k - l) length ↔ ∃ mc lac, nullable_m_n k length mc lac ∧ ¬ nullable_m_n l length mc lac := by
  constructor
  . intro ⟨mc, lac, h⟩; exact ⟨mc, lac, nullable_m_n_diff.mp h⟩
  . intro ⟨mc, lac, h⟩; exact ⟨mc, lac, nullable_m_n_diff.mpr h⟩

theorem nullable_concat : nullable (k • l) length ↔ (∃ mc₁ mc₂ m, nullable_m_n k length mc₁ (mc₂ + m) ∧ nullable_m_n l length mc₂ m) := by
  constructor
  . intro ⟨_, lacount, h⟩
    obtain ⟨mc₁, mc₂, _, hk, hl⟩ := nullable_m_n_concat.mp h
    exact ⟨mc₁, mc₂, lacount, hk, hl⟩
  . intro ⟨mc₁, mc₂, lacount, hk, hl⟩
    exact ⟨mc₁ + mc₂, lacount, nullable_m_n_concat.mpr ⟨mc₁, mc₂, rfl, hk, hl⟩⟩

theorem nullable_star (l base : Lang α) : nullable (star base l) length ↔ nullable base length := by
  constructor
  . intro ⟨mcount, lacount, hb, h⟩
    unfold star at h
    generalize hw : Word.right mcount lacount [] = w at h
    induction h generalizing mcount with
    | inUnit _ hbase => subst hw; exact ⟨mcount, lacount, hb, hbase⟩
    | inConcat w₁ w₂ _ hl hs hwc ih =>
      subst hw
      obtain ⟨mc₁, mc₂, hn, rfl, rfl⟩ := hwc
      exact ih mc₂ (by omega) rfl
  . intro ⟨mcount, lacount, hb, hbase⟩
    exact ⟨mcount, lacount, hb, .inUnit _ hbase⟩

-- The lookbehind's match count is unconstrained, and any lookahead count up to `length` is allowed.
theorem nullable_lookbehind (l : Lang α) : nullable (◁ l) length ↔ ∃ mc lac, lac ≤ length ∧ l (.right mc lac []) := by
  constructor
  . intro ⟨n, m, hb, h⟩
    cases n with
    | zero => obtain ⟨mc, h⟩ := h; exact ⟨mc, m, by omega, h⟩
    | succ n => simp [lookbehind] at h
  . intro ⟨mc, lac, hb, h⟩; exact ⟨0, lac, by omega, mc, h⟩

theorem nullable_lookahead (l : Lang α) : nullable (▷ l) length ↔ ∃ mc, nullable_m_n l length mc 0 := by
  constructor
  . intro ⟨n, m, hb, h⟩
    cases n with
    | zero => exact ⟨m, by omega, h⟩
    | succ n => simp [lookahead] at h
  . intro ⟨mc, hb, h⟩; exact ⟨0, mc, by omega, h⟩

theorem nullable_matchStep : nullable (▹ₘl) (.succ length) ↔ nullable l length := by
  constructor
  . intro ⟨n, m, hb, h⟩
    cases n with
    | zero => simp [matchStep] at h
    | succ n => exact ⟨n, m, by omega, h⟩
  . intro ⟨n, m, hb, h⟩; exact ⟨n.succ, m, by omega, h⟩

theorem nullable_LAStep : nullable (▹ₗl) (.succ length) ↔ nullable l length := by
  constructor
  . intro ⟨n, m, hb, h⟩
    cases m with
    | zero => simp [LAStep] at h
    | succ m => exact ⟨n, m, by omega, h⟩
  . intro ⟨n, m, hb, h⟩; exact ⟨n, m.succ, by omega, h⟩

import Thesis.Semantics.«1_StructuredWords»
import Thesis.Semantics.«2_Operators»
import Thesis.Semantics.«3_Derivatives»

namespace NullabilityLaws

open StructuredWords
open Operators

theorem nullable_m_n_empty : ¬ nullable_m_n (∅ : Lang α) n m := by rw [nullable_m_n, empty]; trivial

theorem nullable_m_n_unit (n : Nat) : nullable_m_n (I : Lang α) n m  ↔ n == 0 := by simp [nullable_m_n, unit]

theorem nullable_m_n_top : nullable_m_n (T : Lang α) n m := by rw [nullable_m_n, top]; trivial

theorem nullable_m_n_symb (a : α) : ¬ nullable_m_n (#a : Lang α) n m := by simp [nullable_m_n, symb]

theorem nullable_m_n_union (l k : Lang α) n : nullable_m_n (k ∪ l) n m ↔ (nullable_m_n k n m) ∨ (nullable_m_n l n m) := by simp [nullable_m_n, union]

theorem nullable_m_n_intersection : nullable_m_n (k ∩ l) n m ↔ nullable_m_n k n m ∧ nullable_m_n l n m := by rw [nullable_m_n, intersection]; rfl

theorem nullable_m_n_diff : nullable_m_n (k - l) n m ↔ nullable_m_n k n m ∧ ¬ nullable_m_n l n m := by rw [nullable_m_n, complement]; rfl

theorem nullable_m_n_concat : nullable_m_n (k • l) n m ↔ (∃ mc₁ mc₂, n = mc₁ + mc₂ ∧ nullable_m_n k mc₁ (mc₂ + m) ∧ nullable_m_n l mc₂ m) := by
  simp [nullable_m_n]; constructor
  . intro ⟨w₁, w₂, hk, hl, mc₁, mc₂, hn, _, _⟩; subst w₁ w₂; exact ⟨mc₁, mc₂, hn, hk, hl⟩
  . intro ⟨mc₁, mc₂, hn, hk, hl⟩; exact ⟨.right mc₁ (mc₂ + m) [], .right mc₂ m [], hk, hl, mc₁, mc₂, hn, rfl, rfl⟩

theorem nullable_m_n_star (l base : Lang α) : nullable_m_n (star base l) n m ↔
    nullable_m_n base n m ∨
    ∃ mc₁ mc₂, n = mc₁ + mc₂ ∧ nullable_m_n l mc₁ (mc₂ + m) ∧ nullable_m_n (star base l) mc₂ m := by
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


theorem nullable_m_n_lookbehind (l : Lang α) : nullable_m_n (◁ l) n m ↔ n = 0 ∧ m = 0 ∧ ∃ mc, nullable_m_n l mc 0  := by
  cases n <;> cases m <;> simp [nullable_m_n, lookbehind]

theorem nullable_m_n_lookahead (l : Lang α) : nullable_m_n (▷ l) n m ↔ n = 0 ∧ nullable_m_n l m 0 := by
  cases n <;> simp [nullable_m_n, lookahead]

theorem nullable_m_n_matchStep : nullable_m_n (▹ₘl) (.succ n) m ↔ nullable_m_n l n m := by simp [nullable_m_n, matchStep]

theorem nullable_m_n_LAStep : nullable_m_n (▹ₗl) n (.succ m) ↔  nullable_m_n l n m := by simp [nullable_m_n, LAStep]





theorem nullable_empty : ¬ nullable (∅ : Lang α) := by simp [nullable, empty]

theorem nullable_unit : nullable (I : Lang α) := by simp [nullable, unit]

theorem nullable_top : nullable (T : Lang α) := by simp [nullable, top]

theorem nullable_symb (a : α) : ¬ nullable (#a : Lang α) := by simp [nullable, symb]

theorem nullable_union (l k : Lang α) : nullable (k ∪ l) ↔ (nullable k) ∨ (nullable l) := by
  constructor
  . rintro ⟨mc, lac, hk | hl⟩
    . exact .inl ⟨mc, lac, hk⟩
    . exact .inr ⟨mc, lac, hl⟩
  . rintro (⟨mc, lac, hk⟩ | ⟨mc, lac, hl⟩)
    . exact ⟨mc, lac, .inl hk⟩
    . exact ⟨mc, lac, .inr hl⟩

theorem nullable_intersection : nullable (k ∩ l) ↔ ∃ mc lac, nullable_m_n k mc lac ∧ nullable_m_n l mc lac := by simp [intersection, nullable, nullable_m_n]

theorem nullable_diff : nullable (k - l) ↔ ∃ mc lac, nullable_m_n k mc lac ∧ ¬ nullable_m_n l mc lac := by simp [complement, nullable_m_n, nullable]

theorem nullable_concat : nullable (k • l) ↔ (∃ mc₁ mc₂ m, nullable_m_n k mc₁ (mc₂ + m) ∧ nullable_m_n l mc₂ m) := by
  constructor
  . intro ⟨mcount, lacount, w₁, w₂, hk, hl, mc₁, mc₂, hmcount, _, _⟩; subst w₁ w₂; refine ⟨mc₁, mc₂, lacount, hk, hl⟩
  . intro ⟨mc₁, mc₂, lacount, hk, hl⟩; refine ⟨(mc₁ + mc₂), lacount, .right mc₁ (mc₂ + lacount) [], .right mc₂ lacount [], hk, hl, mc₁, mc₂, rfl, rfl, rfl⟩

theorem nullable_star (l base : Lang α) : nullable (star base l) ↔ nullable base := by
  constructor
  . intro ⟨mcount, lacount, h⟩
    generalize hw : Word.right mcount lacount [] = w at h
    induction h generalizing mcount with
    | inUnit _ hb => subst hw; exact ⟨mcount, lacount, hb⟩
    | inConcat w₁ w₂ _ hl hs hwc ih =>
      subst hw
      obtain ⟨mc₁, mc₂, hn, rfl, rfl⟩ := hwc
      exact ih mc₂ rfl
  . intro ⟨mcount, lacount, hb⟩
    exact ⟨mcount, lacount, .inUnit _ hb⟩


theorem nullable_lookbehind (l : Lang α) : nullable (◁ l) ↔ ∃ mc, nullable_m_n l mc 0 := by
  constructor
  . intro ⟨n, m, h⟩; cases n <;> cases m <;> simp [lookbehind] at h; exact ⟨h.choose, h.choose_spec⟩
  . intro ⟨mc, h⟩; exact ⟨0, 0, by simp [lookbehind]; exact ⟨mc, h⟩⟩


theorem nullable_lookahead (l : Lang α) : nullable (▷ l) ↔ ∃ mc, nullable_m_n l mc 0 := by
  constructor
  . intro ⟨n, m, h⟩
    cases n with
    | zero => exact ⟨m, h⟩
    | succ n => simp [lookahead] at h
  . intro ⟨mc, h⟩; exact ⟨0, mc, h⟩


theorem nullable_matchStep : nullable (▹ₘl) ↔ nullable l := by
  constructor
  . intro ⟨n, m, h⟩
    cases n with
    | zero => simp [matchStep] at h
    | succ n => exact ⟨n, m, h⟩
  . intro ⟨n, m, h⟩; exact ⟨n.succ, m, h⟩

theorem nullable_LAStep : nullable (▹ₗl) ↔ nullable l := by
  constructor
  . intro ⟨n, m, h⟩
    cases m with
    | zero => simp [LAStep] at h
    | succ m => exact ⟨n, m, h⟩
  . intro ⟨n, m, h⟩; exact ⟨n, m.succ, h⟩

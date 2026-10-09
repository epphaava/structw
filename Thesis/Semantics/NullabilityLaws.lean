import Thesis.Semantics.StructuredWords
import Thesis.Semantics.Operators
import Thesis.Semantics.Derivatives

namespace NullabilityLaws

open StructuredWords
open Operators

theorem nullable_n_m_empty : ¬ nullable_n_m (∅ : Lang α) n m := by rw [nullable_n_m, empty]; trivial

theorem nullable_n_m_unit (n : Nat) : nullable_n_m (I : Lang α) n m  ↔ n == 0 := by simp [nullable_n_m, unit]

theorem nullable_n_m_top : nullable_n_m (T : Lang α) n m := by rw [nullable_n_m, top]; trivial

theorem nullable_n_m_symb (a : α) : ¬ nullable_n_m (#a : Lang α) n m := by simp [nullable_n_m, symb]

theorem nullable_n_m_union (l k : Lang α) n : nullable_n_m (k ∪ l) n m ↔ (nullable_n_m k n m) ∨ (nullable_n_m l n m) := by simp [nullable_n_m, union]

theorem nullable_n_m_intersection : nullable_n_m (k ∩ l) n m ↔ nullable_n_m k n m ∧ nullable_n_m l n m := by rw [nullable_n_m, intersection]; rfl

theorem nullable_n_m_diff : nullable_n_m (k // l) n m ↔ nullable_n_m k n m ∧ ¬ nullable_n_m l n m := by rw [nullable_n_m, complement]; rfl

theorem nullable_n_m_concat : nullable_n_m (k • l) n m ↔ (∃ mc₁ mc₂, n = mc₁ + mc₂ ∧ nullable_n_m k mc₁ (mc₂ + m) ∧ nullable_n_m l mc₂ m) := by
  simp [nullable_n_m]; constructor
  . intro ⟨w₁, w₂, hk, hl, mc₁, mc₂, hn, _, _⟩; subst w₁ w₂; refine ⟨mc₁, mc₂, hn, hk, hl⟩
  . intro ⟨mc₁, mc₂, hn, hk, hl⟩; exact ⟨.right mc₁ (mc₂ + m) [], .right mc₂ m [], hk, hl, mc₁, mc₂, hn, rfl, rfl⟩

theorem nullable_n_m_star (l base : Lang α) : nullable_n_m (star base l) n m ↔
    nullable_n_m base n m ∨
    ∃ mc₁ mc₂, n = mc₁ + mc₂ ∧ nullable_n_m l mc₁ (mc₂ + m) ∧ nullable_n_m (star base l) mc₂ m := by
  simp [nullable_n_m]; constructor
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


theorem nullable_n_m_lookbehind (l : Lang α) : nullable_n_m (◁ l) n m ↔ n = 0 ∧ m = 0 ∧ ∃ mc, nullable_n_m l mc 0  := by
  cases n <;> cases m <;> simp [nullable_n_m, lookbehind]

def mk_word : Nat → List α → List α → Word α
  | lacount, [], la => .right lacount 0 la
  | lacount, y :: ys, la => .middle lacount (y, ys) la

theorem nullable_n_m_lookahead (l : Lang α) : nullable_n_m (▷ l) n m ↔ n = 0 ∧ nullable_n_m l m 0 := by
  cases n <;> simp [nullable_n_m, lookahead]


theorem nullable_n_m_LAStep : nullable_n_m (▹ₗl) n (.succ m) ↔  nullable_n_m l n m := by simp [nullable_n_m, LAStep]

theorem nullable_n_m_matchStep : nullable_n_m (▹ₘl) (.succ n) m ↔ nullable_n_m l n m := by simp [nullable_n_m, matchStep]

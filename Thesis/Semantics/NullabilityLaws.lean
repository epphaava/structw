import Thesis.Semantics.StructuredWords
import Thesis.Semantics.Operators
import Thesis.Semantics.Derivatives

namespace NullabilityLaws

open StructuredWords
open Operators

theorem nullable_n_m_empty : ¬ nullable_n_m (∅ : Lang α) n m := by rw [nullable_n_m, empty]; trivial

theorem nullable_n_m_unit (n : Nat) : nullable_n_m (I : Lang α) n m := by
  rw [nullable_n_m]
  sorry

theorem nullable_n_m_top : nullable_n_m (T : Lang α) n m := by rw [nullable_n_m, top]; trivial

theorem nullable_n_m_symb (a : α) : ¬ nullable_n_m (#a : Lang α) n m := by simp [nullable_n_m, symb]

theorem nullable_n_m_union (l k : Lang α) n : nullable_n_m (k ∪ l) n m ↔ (nullable_n_m k n m) ∨ (nullable_n_m l n m) := by simp [nullable_n_m, union]

theorem nullable_n_m_intersection : nullable_n_m (k ∩ l) n m ↔ nullable_n_m k n m ∧ nullable_n_m l n m := by rw [nullable_n_m, intersection]; rfl

theorem nullable_n_m_diff : nullable_n_m (k // l) n m ↔ nullable_n_m k n m ∧ ¬ nullable_n_m l n m := by rw [nullable_n_m, complement]; rfl

theorem nullable_n_m_mult : nullable_n_m (k • l) n m ↔ nullable_n_m l n m ∧ (∃ n', nullable_n_m k (n'+m')) := by
  rw [nullable_n_m, concat];
  constructor
  . intro ⟨x, y, hx, hy, ⟨n', _, _⟩⟩; subst x y; exact ⟨hy, ⟨n', hx⟩⟩
  . intro ⟨hl, n', hk⟩; refine ⟨(Sum.inr (n+n', [])), (Sum.inr (n, [])), hk, hl, ⟨n', rfl, rfl⟩⟩

theorem nullable_n_m_la : nullable_n_m (la l) n m ↔ n = 0 ∧ nullable_n_m l 0 m := by
  cases n with
  | zero => simp [nullable_n_m, la]
  | succ n' => simp [nullable_n_m, la]

theorem nullable_n_m_star (l : Lang α) (n : Nat) : nullable_n_m (l*) n m := by
  rw [nullable_n_m, star]
  exact star_help.inUnit (l := l) n []

theorem nullable_n_m_step : nullable_n_m (▹l) (n + 1) m ↔ nullable_n_m l n m := by simp [nullable_n_m, step]

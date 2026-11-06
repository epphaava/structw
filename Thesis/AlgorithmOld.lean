import Thesis.Syntax.Nullability
import Thesis.Syntax.«2_Derivatives»
import Thesis.Semantics.«3_Derivatives»
import Thesis.Syntax.NullabilityCorrectness

namespace Algorithm

open Expr
open ExprDerivatives
open NullabilityCorrect



-- Definition 5.1.2 (Matching algorithm).
def findAllMatches [DecidableEq α] (r : Expr α) (w : List α) : Tbl := (NT (xD w r)) w.length


theorem matchesUpTo_iff (m : MatchSet) (w : List α) (k : Nat) :
    k ∈ Algorithm.matchesUpTo m w.length ↔ k ∈ m ∧ k ≤ w.length := by
  cases m with
  | inl included =>
    simp only [Algorithm.matchesUpTo, Membership.mem]
    constructor
    · intro h
      rcases List.mem_filter.mp h with ⟨hi, hb⟩
      exact ⟨hi, Nat.le_of_ble_eq_true hb⟩
    · rintro ⟨hi, hk⟩
      refine List.mem_filter.mpr ⟨hi, ?_⟩
      simp [Nat.ble_eq, hk]
  | inr excluded =>
    simp only [Algorithm.matchesUpTo, Membership.mem]
    constructor
    · intro h
      rcases List.mem_filter.mp h with ⟨hr, hb⟩
      refine ⟨?_, Nat.lt_succ_iff.mp (List.mem_range.mp hr)⟩
      intro hk
      have he : List.elem k excluded = true := List.elem_eq_true_of_mem hk
      cases h : List.elem k excluded <;> simp_all
    · rintro ⟨hnd, hk⟩
      refine List.mem_filter.mpr ⟨List.mem_range.mpr (Nat.lt_succ_iff.mpr hk), ?_⟩
      cases h : List.elem k excluded
      · simp
      · exact False.elim (hnd (List.mem_of_elem_eq_true h))

-- Theorem 5.1.1 — correctness of `findAllMatches` / `matchesUpTo` vs semantic nullability
-- Theorem 5.1.1 — correctness of `findAllMatches` / `matchesUpTo` vs semantic nullability
theorem algorithm_correctness [DecidableEq α] (r : Expr α) (w : List α) (lbc mc lac : Nat) :
    (lbc, mc, lac) ∈ findAllMatches r w ↔ nullable (sem (xD w r)) lbc mc lac  := by
  simp [findAllMatches]

end Algorithm

import Thesis.Semantics.kLang.«1_StructuredWords»
import Thesis.Semantics.kLang.«2_Operators»
import Thesis.Semantics.kLang.Helpers
import Thesis.Semantics.Lang.«8_AlgebraicLaws»


namespace kAlgebraicLaws

open StructuredWords
open kStructuredWords
open kOperators
open Operators
open AlgebraicLaws
open helpers

-- Proposition 3.5.1 (Basic algebraic laws).

-- Equation (3.1)
theorem union_assoc (k l m : kLang α n) : k ∪ (l ∪ m) ≐ (k ∪ l) ∪ m := by intro w; simp [kOperators.union, or_assoc, Operators.union]

-- Equation (3.2)
theorem union_comm (k l : kLang α n) : k ∪ l ≐ l ∪ k := by intro w; simp [kOperators.union, or_comm, Operators.union]

-- Equation (3.3)
theorem union_idempotent (l : kLang α n) : l ∪ l ≐ l := by intro w; simp [kOperators.union, Operators.union]

-- Equation (3.4)
theorem union_identity (l : kLang α n) : l ∪ ∅ ≐ l := by intro w; simp [kOperators.empty, kOperators.union, Operators.empty, Operators.union]

-- Equation (3.5)
theorem intersection_assoc (k l m : kLang α n) : k ∩ (l ∩ m) ≐ (k ∩ l) ∩ m := by
  intro w; simp [kOperators.intersection, and_assoc, Operators.intersection]

-- Equation (3.6)
theorem intersection_comm (k l : kLang α n) : k ∩ l ≐ l ∩ k := by
  intro w; simp [kOperators.intersection, and_comm, Operators.intersection]

-- Equation (3.7)
theorem intersection_idempotent (l : kLang α n) : l ∩ l ≐ l := by intro w; simp [kOperators.intersection, Operators.intersection]

-- Equation (3.8)
theorem intersection_top (l : kLang α n) : T ∩ l ≐ l := by intro w; simp [kOperators.top, kOperators.intersection, Operators.intersection]; exact l.2 w

-- Equation (3.9)
theorem complement_empty (l : kLang α n) : (l - ∅) ≐ l := by intro w; simp [kOperators.empty, kOperators.complement, Operators.empty, Operators.complement]

-- Equation (3.10)
theorem complement_self (l : kLang α n) : (l - l) ≐ (∅ : kLang α n) := by intro w; simp [kOperators.complement, kOperators.empty, Operators.complement, Operators.empty]

-- Equation (3.11)
theorem complement_top (l : kLang α n) : (l - T) ≐ (∅ : kLang α n) := by intro w; simp [kOperators.top, kOperators.complement, kOperators.empty, Operators.complement, Operators.empty]; exact l.2 w

-- Equation (3.12)
theorem concat_distrib_union_left (k l m : kLang α n) : k • (l ∪ m) ≐ (k • l) ∪ (k • m) := by
  exact AlgebraicLaws.concat_distrib_union_left k.val l.val m.val

-- Equation (3.13)
theorem concat_distrib_union_right (k l m : kLang α n) : (k ∪ l) • m ≐ (k • m) ∪ (l • m) := by
  exact AlgebraicLaws.concat_distrib_union_right k.val l.val m.val

-- Equation (3.14)
theorem empty_concat_left (l : kLang α n) : (∅ : kLang α n) • l ≐ (∅ : kLang α n) := by
  exact AlgebraicLaws.empty_concat_left l.val

theorem empty_concat_right (l : kLang α n) : l • (∅ : kLang α n) ≐ (∅ : kLang α n) := by
  exact AlgebraicLaws.empty_concat_right l.val

-- Equation (3.15)
theorem star_unfold (l base : kLang α n) : (star l base) ≐ base ∪ (l • (star l base)) := by
  exact AlgebraicLaws.star_unfold l.val base.val


-- Proposition 3.5.3 (Left identity).
theorem concat_left_identity (l : kLang α n) : I • l ≐ l := by
  intro w
  constructor
  · rintro ⟨u, v, hu, hv, hwc⟩
    exact (AlgebraicLaws.concat_left_identity l.1 w).1 ⟨u, v, hu.2, hv, hwc⟩
  · intro h
    obtain ⟨u, v, hu, hv, hwc⟩ := (AlgebraicLaws.concat_left_identity l.1 w).2 h
    exact ⟨u, v, ⟨Nat.le_trans (wc_steps_le hwc).1 (l.2 w h), hu⟩, hv, hwc⟩

-- Proposition 3.5.4 (Right identity).
theorem concat_right_identity (l : kLang α n) : l • I ≐ l := by
  intro w
  constructor
  · rintro ⟨u, v, hu, hv, hwc⟩
    exact (AlgebraicLaws.concat_right_identity l.1 w).1 ⟨u, v, hu, hv.2, hwc⟩
  · intro h
    obtain ⟨u, v, hu, hv, hwc⟩ := (AlgebraicLaws.concat_right_identity l.1 w).2 h
    exact ⟨u, v, hu, ⟨Nat.le_trans (wc_steps_le hwc).2 (l.2 w h), hv⟩, hwc⟩

-- Proposition 3.5.6 (Associativity).
theorem concat_assoc (k l m : kLang α n) : k • (l • m) ≐ (k • l) • m := by
  exact AlgebraicLaws.concat_assoc k.val l.val m.val

end kAlgebraicLaws

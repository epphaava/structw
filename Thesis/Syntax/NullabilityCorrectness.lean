import Thesis.Syntax.Expressions
import Thesis.Syntax.Nullability
import Thesis.Semantics.NullabilityLaws
import Thesis.Semantics.StructuredWords

namespace NullabilityCorrect

open Expr
open NullabilityLaws
open Operators
open StructuredWords

-- Theorem 4.3.1 — Correctness of nullability
theorem nullability_correct [DecidableEq α] (r : Expr α) (mc lac : Nat) (n : Nat) :
  ((mc + lac : Nat) ≤ n) → (N r n mc lac ↔ nullable_m_n (sem r) mc lac) := by
  induction r generalizing mc lac with
  | empty => simp [nullable_m_n, sem, empty, N]
  | unit => simp [nullable_m_n, sem, unit, N]
  | top => simp [nullable_m_n, sem, top, N]
  | symbol _ => simp [nullable_m_n, sem, symb, N]
  | plus r₁ r₂ ih₁ ih₂ =>
    intro hn
    if hr₁ : N r₁ n mc lac then
      have := (ih₁ mc lac hn).mp hr₁; simp [nullable_m_n] at this
      simp [N, hr₁, nullable_m_n, sem, union, this]
    else
      if hr₂ : N r₂ n mc lac then
        have := (ih₂ mc lac hn).mp hr₂; simp [nullable_m_n] at this
        simp [N, hr₂, nullable_m_n, sem, union, this]
      else
        simp [N, hr₁, hr₂, nullable_m_n, sem, union];
        exact ⟨mt (ih₁ mc lac hn).mpr hr₁, mt (ih₂ mc lac hn).mpr hr₂⟩
  | intersection r₁ r₂ ih₁ ih₂ =>
    intro hn
    if hr₁ : N r₁ n mc lac then
      if hr₂ : N r₂ n mc lac then
        simp [N, hr₁, hr₂, nullable_m_n, sem, intersection]
        exact ⟨(ih₁ mc lac hn).mp hr₁, (ih₂ mc lac hn).mp hr₂⟩
      else
        have := mt (ih₂ mc lac hn).mpr hr₂; simp [nullable_m_n] at this
        simp [N, hr₂, nullable_m_n, sem, intersection, this]
    else
      have := mt (ih₁ mc lac hn).mpr hr₁; simp [nullable_m_n] at this
      simp [N, hr₁, nullable_m_n, sem, intersection, this]
  | complement r₁ r₂ ih₁ ih₂ =>
    intro hn
    if hr₁ : N r₁ n mc lac then
      if hr₂ : N r₂ n mc lac then
        have := (ih₂ mc lac hn).mp hr₂; simp [nullable_m_n] at this
        simp [N, hr₂, nullable_m_n, sem, complement, this]
      else
        simp [N, hr₁, hr₂, nullable_m_n, sem, complement]
        exact ⟨(ih₁ mc lac hn).mp hr₁, mt (ih₂ mc lac hn).mpr hr₂⟩
    else
      have := mt (ih₁ mc lac hn).mpr hr₁; simp [nullable_m_n] at this
      simp [N, hr₁, nullable_m_n, sem, complement, this]
  | mult r₁ r₂ ih₁ ih₂ =>
    intro hn
    constructor
    . simp [N]; intro n' hn' hr₁ hr₂
      simp [nullable_m_n, sem]
      have hl₁ := (ih₁ n' (.sub mc n' + lac) (by simp [Nat.sub_eq]; omega)).mp hr₁;
      have hl₂ := (ih₂ (.sub mc n') lac (by simp [Nat.sub_eq]; omega)).mp hr₂; simp [nullable_m_n] at hl₁ hl₂
      exact ⟨.right n' (.sub mc n' + lac) [], .right (.sub mc n') lac [], hl₁, hl₂, n', .sub mc n', by rw [Nat.sub_eq]; omega, rfl, rfl⟩
    . rintro ⟨w₁, w₂, hl₁, hl₂, mc₁, mc₂, rfl, rfl, rfl⟩; simp [N]
      have hr₁ := (ih₁ mc₁ (mc₂ + lac) (by simp [←Nat.add_assoc]; exact hn)).mpr hl₁
      have hr₂ := (ih₂ mc₂ lac (by omega)).mpr hl₂
      exact ⟨mc₁, by omega, by simp; exact hr₁, by simp; exact hr₂⟩
  | star r b ihᵣ ih =>
    intro hn
    simp only [N, sem]
    constructor
    . induction mc using Nat.strongRecOn with
      | _ mc ihm =>
        intro h; rw [NStar, Bool.or_eq_true] at h
        rcases h with h | h
        · exact .inUnit _ ((ih mc lac hn).mp h)
        · rw [List.any_eq_true] at h
          obtain ⟨⟨k, hk⟩, _, h⟩ := h
          have hk := List.mem_range.mp hk
          simp at h; obtain ⟨hr, hstar⟩ := h
          have hl := (ihᵣ k.succ (.add (.sub mc k.succ) lac) (by simp [Nat.sub_eq]; omega)).mp hr
          have hs := ihm (.sub mc k.succ) (by simp [Nat.sub_eq]; omega) (by simp [Nat.sub_eq]; omega) hstar
          exact (nullable_n_m_star (sem r) (sem b)).mpr (.inr ⟨k.succ, Nat.sub mc k.succ, by simp [Nat.sub_eq]; omega, hl, hs⟩)
    . intro h
      simp [nullable_m_n, star] at h
      generalize hw : Word.right mc lac [] = w at h
      induction h generalizing mc with
      | inUnit _ hb => subst hw; rw [NStar, (ih mc lac hn).mpr hb]; rfl
      | inConcat w₁ w₂ _ hl _ hwc ih =>
        subst hw; obtain ⟨mc₁, mc₂, rfl, rfl, rfl⟩ := hwc
        have hstar := ih mc₂ (by omega) rfl
        cases mc₁ with
        | zero => simp [hstar]
        | succ k =>
          rw [NStar, Bool.or_eq_true, List.any_eq_true]; right
          exact ⟨⟨k, List.mem_range.mpr (by omega)⟩, List.mem_attach _ _, by simp; exact ⟨(ihᵣ k.succ (Nat.add mc₂ lac) (by simp; omega)).mpr hl, hstar⟩⟩
  | lb r ih =>
    intro hn
    rcases mc with zero | mc.succ
    . rcases lac with zero | lac.succ
      . simp [nullable_m_n, sem, lookbehind, N]
        constructor
        . intro ⟨mc, hmc, hr⟩; exact ⟨mc, (ih mc 0 (by omega)).mp hr⟩
        . intro ⟨mc, hl⟩
          have := ih mc 0
          refine ⟨mc, ?_⟩
          sorry
      . simp [nullable_m_n, sem, lookbehind, N]
    . simp [nullable_m_n, sem, lookbehind, N]
  | _ => sorry

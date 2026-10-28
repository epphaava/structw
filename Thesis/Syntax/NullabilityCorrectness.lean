import Thesis.Syntax.Expressions
import Thesis.Syntax.Nullability
import Thesis.Semantics.«9_NullabilityLaws»
import Thesis.Semantics.«1_StructuredWords»

namespace NullabilityCorrect

open Expr
open NullabilityLaws
open Operators
open StructuredWords

-- Theorem 4.3.1 — Correctness of nullability
theorem nullability_correct [DecidableEq α] (r : Expr α) (lbc mc lac : Nat) : (N r lbc mc lac ↔ nullable (sem r) lbc mc lac) := by
  induction r generalizing lbc mc lac with
  | empty => simp [nullable, sem, empty, N]
  | unit => simp [nullable, sem, unit, N]
  | top => simp [nullable, sem, top, N]
  | symbol _ => simp [nullable, sem, symb, N]
  | plus r₁ r₂ ih₁ ih₂ =>
    if hr₁ : N r₁ lbc mc lac then
      have := (ih₁ lbc mc lac).mp hr₁; simp [nullable] at this
      simp [N, hr₁, nullable, sem, union, this]
    else
      if hr₂ : N r₂ lbc mc lac then
        have := (ih₂ lbc mc lac).mp hr₂; simp [nullable] at this
        simp [N, hr₂, nullable, sem, union, this]
      else
        simp [N, hr₁, hr₂, nullable, sem, union];
        exact ⟨mt (ih₁ lbc mc lac).mpr hr₁, mt (ih₂ lbc mc lac).mpr hr₂⟩
  | intersection r₁ r₂ ih₁ ih₂ =>
    if hr₁ : N r₁ lbc mc lac then
      if hr₂ : N r₂ lbc mc lac then
        simp [N, hr₁, hr₂, nullable, sem, intersection]
        exact ⟨(ih₁ lbc mc lac).mp hr₁, (ih₂ lbc mc lac).mp hr₂⟩
      else
        have := mt (ih₂ lbc mc lac).mpr hr₂; simp [nullable] at this
        simp [N, hr₂, nullable, sem, intersection, this]
    else
      have := mt (ih₁ lbc mc lac).mpr hr₁; simp [nullable] at this
      simp [N, hr₁, nullable, sem, intersection, this]
  | complement r₁ r₂ ih₁ ih₂ =>
    if hr₁ : N r₁ lbc mc lac then
      if hr₂ : N r₂ lbc mc lac then
        have := (ih₂ lbc mc lac).mp hr₂; simp [nullable] at this
        simp [N, hr₂, nullable, sem, complement, this]
      else
        simp [N, hr₁, hr₂, nullable, sem, complement]
        exact ⟨(ih₁ lbc mc lac).mp hr₁, mt (ih₂ lbc mc lac).mpr hr₂⟩
    else
      have := mt (ih₁ lbc mc lac).mpr hr₁; simp [nullable] at this
      simp [N, hr₁, nullable, sem, complement, this]
  | mult r₁ r₂ ih₁ ih₂ =>
    constructor
    . simp [N]; intro mc' hmc' hr₁ hr₂
      simp [nullable, sem]
      have hl₁ := (ih₁ lbc mc' (.add (.sub mc mc') lac)).mp hr₁
      have hl₂ := (ih₂ (.add lbc mc') (.sub mc mc') lac).mp hr₂; simp [nullable] at hl₁ hl₂
      exact ⟨.right lbc mc' (.sub mc mc' + lac) [], .right (.add lbc mc') (.sub mc mc') lac [], hl₁, hl₂, mc', .sub mc mc', by rw [Nat.sub_eq]; omega, rfl, rfl⟩
    . rintro ⟨w₁, w₂, hl₁, hl₂, mc₁, mc₂, rfl, rfl, rfl⟩; simp [N]
      have hr₁ := (ih₁ lbc mc₁ (mc₂ + lac)).mpr hl₁
      have hr₂ := (ih₂ (lbc + mc₁) mc₂ lac).mpr hl₂
      exact ⟨mc₁, by omega, by simp; exact hr₁, by simp; exact hr₂⟩
  | star r b ihᵣ ih =>
    simp only [N, sem]
    constructor
    . intro h
      induction mc using Nat.strongRecOn generalizing lbc with
      | _ mc ihm =>
        rw [NStar, Bool.or_eq_true] at h
        rcases h with h | h
        · exact .inUnit _ ((ih lbc mc lac).mp h)
        · rw [List.any_eq_true] at h
          obtain ⟨⟨k, hk⟩, _, h⟩ := h
          have hk := List.mem_range.mp hk
          simp only [Bool.and_eq_true] at h; obtain ⟨hr, hstar⟩ := h
          have hl := (ihᵣ lbc (k + 1) ((mc - (k + 1)) + lac)).mp hr
          have hs := ihm (mc - (k + 1)) (by omega) (lbc + (k + 1)) hstar
          exact star_help.inConcat _ _ _ hl hs ⟨k + 1, mc - (k + 1), by omega, rfl, rfl⟩
    . intro h
      unfold nullable star at h
      generalize hw : Word.right lbc mc lac [] = w at h
      induction h generalizing lbc mc with
      | inUnit _ hb => subst hw; rw [NStar, (ih lbc mc lac).mpr hb]; rfl
      | inConcat w₁ w₂ _ hl _ hwc ihs =>
        subst hw; obtain ⟨mc₁, mc₂, rfl, h₁, h₂⟩ := hwc; subst h₁
        have hstar := ihs (lbc + mc₁) mc₂ h₂.symm
        cases mc₁ with
        | zero => simpa using hstar
        | succ k =>
          rw [NStar, Bool.or_eq_true, List.any_eq_true]; right
          refine ⟨⟨k, List.mem_range.mpr (by omega)⟩, List.mem_attach _ _, ?_⟩
          simp only [Nat.add_sub_cancel_left, Bool.and_eq_true]
          exact ⟨(ihᵣ lbc (k + 1) (mc₂ + lac)).mpr hl, hstar⟩
  | lb r ih =>
    cases mc with
    | zero => simp only [N, nullable, sem, lookbehind]; simpa using ih 0 lbc lac
    | succ mc => simp [N, nullable, sem, lookbehind]
  | la r ih =>
    cases mc with
    | zero => simp only [N, nullable, sem, lookahead]; simpa using ih lbc lac 0
    | succ mc => simp [N, nullable, sem, lookahead]
  | lbStep r ih =>
    cases lbc with
    | zero => simp [N, nullable, sem, lbStep]
    | succ lbc => simp only [N, nullable, sem, lbStep]; exact ih lbc mc lac
  | mStep r ih =>
    cases mc with
    | zero => simp [N, nullable, sem, matchStep]
    | succ mc => simp only [N, nullable, sem, matchStep]; exact ih lbc mc lac
  | laStep r ih =>
    cases lac with
    | zero => simp [N, nullable, sem, laStep]
    | succ lac => simp only [N, nullable, sem, laStep]; exact ih lbc mc lac

import Thesis.Semantics.Lang.«1_StructuredWords»
import Thesis.Semantics.Lang.«2_Operators»
import Thesis.Semantics.Lang.«3_Derivatives»
import Thesis.Semantics.Lang.Helpers.«4_DerivativeAcceptance»

namespace DerAccept

open StructuredWords
open DerAcceptHelpers
open Derivatives


-- (0, main, la) ∈ derLB w L ↔ (w, main, la) ∈ L
theorem derLB_word_iff {α} (L : Lang α) (x : α) (xs main la : List α) :
    derLB_word (x :: xs) L (mk_mcount_word 0 main la) ↔ L (.left (x, xs) main la) := by
  induction xs generalizing L x with
  | nil => cases main <;> exact Iff.rfl
  | cons x' xs' ih =>
    exact ih (derLB x L) x'

-- (mc + n, 0, la) ∈ der w L ↔ (mc, w, la) ∈ L
theorem der_word_iff {α} (L : Lang α) (mcount : Nat) (y : α) (ys la : List α) :
    der_word (y :: ys) L (.right (mcount + ys.length.succ) 0 la) ↔ L (.middle mcount (y, ys) la) := by
  induction ys generalizing L mcount y with
  | nil => cases mcount <;> simp [der_word, der]
  | cons y' ys' ih =>
    have := ih (der y L) (mcount + 1) y'
    have e : mcount + 1 + ys'.length.succ = mcount + (y' :: ys').length.succ := by simp [List.length_cons]; omega
    rw [e] at this
    exact this

-- (mc, lac + n, ε) ∈ derLA w L ↔ (mc, lac, w) ∈ L
theorem derLA_word_iff {α} (L : Lang α) (mcount lacount : Nat) (la : List α) :
    derLA_word la L (.right mcount (lacount + la.length) []) ↔ L (.right mcount lacount la) := by
  induction la generalizing L mcount lacount with
  | nil => simp [derLA_word]
  | cons z zs ih =>
    have := ih (derLA z L) (mcount) (lacount.succ)
    simp [Nat.add_assoc, Nat.one_add, derLA] at ⊢ this
    exact this
/-
-- Theorem 3.2.1 (Derivative characterization of membership).
theorem membership_left_iff_nullable (l : Lang α) (lb : NEList α) (main la : List α) :
    l (.left lb main la) ↔ nullable (derLA_word la (der_word main (derLB_word (toList lb) l))) main.length la.length := by
  have hlb := derLB_word_iff l lb.fst lb.snd main la
  have hla := derLA_word_iff (der_word main (derLB_word (toList lb) l)) main.length 0 la
  rw [Nat.zero_add] at hla
  unfold nullable
  refine Iff.trans ?_ hla.symm
  cases main with
  | nil => exact hlb.symm
  | cons y ys =>
    have hder := der_word_iff (derLB_word (toList lb) l) 0 y ys la
    rw [Nat.zero_add] at hder
    exact hlb.symm.trans hder.symm

theorem membership_middle_iff_nullable (L : Lang α) (mcount : Nat) (main : NEList α) (la : List α) :
    L (.middle mcount main la) ↔ nullable (derLA_word la (der_word (toList main) L)) (mcount + (toList main).length) la.length := by
  have hla := derLA_word_iff (der_word (toList main) L) (mcount + (toList main).length) 0 la
  rw [Nat.zero_add] at hla
  exact (der_word_iff L mcount main.fst main.snd la).symm.trans hla.symm

theorem membership_right_iff_nullable (L : Lang α) (mcount lacount : Nat) (la : List α) :
    L (.right mcount lacount la) ↔ nullable (derLA_word la L) mcount (lacount + la.length) :=
  (derLA_word_iff L mcount lacount la).symm


/-- Theorem 3.2.2 — existential derivative and indexed nullability. -/
theorem xder_nullable_iff {α} (l : Lang α) (w : List α) (mc lac : Nat) :
    nullable (xder w l) mc lac ↔ ∃ u, is_split w mc lac u ∧ l u :=
  (xder_right_iff l w mc lac).trans (exists_split_iff l w mc lac).symm
 -/

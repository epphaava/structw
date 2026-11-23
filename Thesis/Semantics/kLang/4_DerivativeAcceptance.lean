import Thesis.Semantics.kLang.«1_StructuredWords»
import Thesis.Semantics.kLang.«2_Operators»
import Thesis.Semantics.kLang.«3_Derivatives»
import Thesis.Semantics.Lang.«3_Derivatives»
import Thesis.Semantics.kLang.Helpers
import Thesis.Semantics.Lang.«4_DerivativeAcceptance»


namespace kDerAccept

open StructuredWords
open kStructuredWords
open Derivatives
open kDerivatives
open helpers
open DerAccept


-- (0, main, la) ∈ derLB w L ↔ (w, main, la) ∈ L
theorem derLB_word_iff {α} (l : kLang α n) (x : α) (xs main la : List α) : derLB_word (x :: xs) l (mk_mcount_word 0 main la) ↔ l (.left (x, xs) main la) := by
  rw [derLB_word_val]; exact DerAccept.derLB_word_iff l.val x xs main la

-- (mc + n, 0, la) ∈ der w L ↔ (mc, w, la) ∈ L
theorem der_word_iff {α} (l : kLang α n) (mcount : Nat) (y : α) (ys la : List α) : der_word (y :: ys) l (.right (mcount + ys.length.succ) 0 la) ↔ l (.middle mcount (y, ys) la) := by
  rw [der_word_val]; exact DerAccept.der_word_iff l.val mcount y ys la

-- (mc, lac + n, ε) ∈ derLA w L ↔ (mc, lac, w) ∈ L
theorem derLA_word_iff {α} (l : kLang α n) (mcount lacount : Nat) (la : List α) : derLA_word la l (.right mcount (lacount + la.length) []) ↔ l (.right mcount lacount la) := by
  rw [derLA_word_val]; exact DerAccept.derLA_word_iff l.val mcount lacount la

-- Theorem 3.2.1 (Derivative characterization of membership).
theorem membership_left_iff_nullable (l : kLang α n) (lb : NEList α) (main la : List α) :
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

theorem membership_middle_iff_nullable (L : kLang α n) (mcount : Nat) (main : NEList α) (la : List α) :
    L (.middle mcount main la) ↔ nullable (derLA_word la (der_word (toList main) L)) (mcount + (toList main).length) la.length := by
  have hla := derLA_word_iff (der_word (toList main) L) (mcount + (toList main).length) 0 la
  rw [Nat.zero_add] at hla
  exact (der_word_iff L mcount main.fst main.snd la).symm.trans hla.symm

theorem membership_right_iff_nullable (L : kLang α n) (mcount lacount : Nat) (la : List α) :
    L (.right mcount lacount la) ↔ nullable (derLA_word la L) mcount (lacount + la.length) :=
  (derLA_word_iff L mcount lacount la).symm


/-- Theorem 3.2.2 — existential derivative and indexed nullability. -/
theorem xder_nullable_iff {α} (l : kLang α n) (w : List α) (mc lac : Nat) : nullable (xder w l) mc lac ↔ ∃ u, is_split w mc lac u ∧ l u := by
  simp [nullable, xder_val]
  exact (DerAcceptHelpers.xder_right_iff l.1 w mc lac).trans (DerAcceptHelpers.exists_split_iff l.1 w mc lac).symm

end kDerAccept

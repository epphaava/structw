import Thesis.Semantics.«1_StructuredWords»
import Thesis.Semantics.«2_Operators»
import Thesis.Semantics.«3_Derivatives»
import Thesis.Semantics.Helpers.«4_DerivativeAcceptance»

namespace DerAccept

open StructuredWords
open DerAcceptHelpers


-- (lbc + n, 0, main, la) ∈ derLB w L ↔ (lbc, w, main, la) ∈ L
theorem derLB_word_iff {α} (L : Lang α) (lbcount : Nat) (x : α) (xs main la : List α) :
    derLB_word (x :: xs) L (mk_mcount_word (lbcount + xs.length.succ) 0 main la) ↔ L (.left lbcount (x, xs) main la) := by
  induction xs generalizing L lbcount x with
  | nil => cases main <;> exact Iff.rfl
  | cons x' xs' ih =>
    have := ih (derLB x L) (lbcount.succ) x'
    have e : lbcount + 1 + xs'.length.succ = lbcount + (x' :: xs').length.succ := by simp [List.length_cons]; omega
    rw [e] at this
    exact this

-- (lbc, mc + n, 0, la) ∈ der w L ↔ (lbc, mc, w, la) ∈ L
theorem der_word_iff {α} (L : Lang α) (lbcount mcount : Nat) (y : α) (ys la : List α) :
    der_word (y :: ys) L (.right lbcount (mcount + ys.length.succ) 0 la) ↔ L (.middle lbcount mcount (y, ys) la) := by
  induction ys generalizing L mcount y with
  | nil => cases mcount <;> simp [der_word, der]
  | cons y' ys' ih =>
    have := ih (der y L) (mcount + 1) y'
    have e : mcount + 1 + ys'.length.succ = mcount + (y' :: ys').length.succ := by simp [List.length_cons]; omega
    rw [e] at this
    exact this

-- (lbc, mc, lac + n, ε) ∈ derLA w L ↔ (lbc, mc, lac, w) ∈ L
theorem derLA_word_iff {α} (L : Lang α) (lbcount mcount lacount : Nat) (la : List α) :
    derLA_word la L (.right lbcount mcount (lacount + la.length) []) ↔ L (.right lbcount mcount lacount la) := by
  induction la generalizing L mcount lacount with
  | nil => simp [derLA_word]
  | cons z zs ih =>
    have := ih (derLA z L) (mcount) (lacount.succ)
    simp [Nat.add_assoc, Nat.one_add, derLA] at ⊢ this
    exact this

-- Theorem 3.2.1 (Derivative characterization of membership).
theorem membership_left_iff_nullable (l : Lang α) (lbcount : Nat) (lb : NEList α) (main la : List α) :
    l (.left lbcount lb main la) ↔ nullable (derLA_word la (der_word main (derLB_word (toList lb) l))) (lbcount + (toList lb).length) main.length la.length := by
  have hlb := derLB_word_iff l lbcount lb.fst lb.snd main la
  have hla := derLA_word_iff (der_word main (derLB_word (toList lb) l)) (lbcount + (toList lb).length) main.length 0 la
  rw [Nat.zero_add] at hla
  unfold nullable
  refine Iff.trans ?_ hla.symm
  cases main with
  | nil => exact hlb.symm
  | cons y ys =>
    have hder := der_word_iff (derLB_word (toList lb) l) (lbcount + (toList lb).length) 0 y ys la
    rw [Nat.zero_add] at hder
    exact hlb.symm.trans hder.symm

theorem membership_middle_iff_nullable (L : Lang α) (lbcount mcount : Nat) (main : NEList α) (la : List α) :
    L (.middle lbcount mcount main la) ↔ nullable (derLA_word la (der_word (toList main) L)) lbcount (mcount + (toList main).length) la.length := by
  have hla := derLA_word_iff (der_word (toList main) L) lbcount (mcount + (toList main).length) 0 la
  rw [Nat.zero_add] at hla
  exact (der_word_iff L lbcount mcount main.fst main.snd la).symm.trans hla.symm

theorem membership_right_iff_nullable (L : Lang α) (lbcount mcount lacount : Nat) (la : List α) :
    L (.right lbcount mcount lacount la) ↔ nullable (derLA_word la L) lbcount mcount (lacount + la.length) :=
  (derLA_word_iff L lbcount mcount lacount la).symm


/-- Theorem 3.2.2 — existential derivative and indexed nullability. -/
theorem xder_nullable_iff {α} (l : Lang α) (w : List α) (lbc mc lac : Nat) :
    nullable (xder w l) lbc mc lac ↔
      (∃ (lbc' : Nat) (lb : NEList α) (main la : List α),
        w = toList lb ++ main ++ la ∧ lbc = lbc' + (toList lb).length ∧ mc = main.length ∧ lac = la.length ∧ l (.left lbc' lb main la))
      ∨ (∃ (mc' : Nat) (main : NEList α) (la : List α),
        w = toList main ++ la ∧ mc = mc' + (toList main).length ∧ lac = la.length ∧ l (.middle lbc mc' main la))
      ∨ (∃ lac' : Nat, lac = lac' + w.length ∧ l (.right lbc mc lac' w)) :=
  xder_right_iff l w lbc mc lac

import Thesis.Semantics.«1_StructuredWords»
import Thesis.Semantics.«2_Operators»
import Thesis.Semantics.«3_Derivatives»

namespace DerAccept

open StructuredWords



theorem derLB_word_iff {α} (L : Lang α) (lbcount : Nat) (x : α) (xs main la : List α) :
    derLB_word (x :: xs) L (mk_mcount_word (lbcount + xs.length.succ) 0 main la) ↔ L (.left lbcount (x, xs) main la) := by
  induction xs generalizing L lbcount x with
  | nil => cases main <;> exact Iff.rfl
  | cons x' xs' ih =>
    have := ih (derLB x L) (lbcount.succ) x'
    have e : lbcount + 1 + xs'.length.succ = lbcount + (x' :: xs').length.succ := by simp [List.length_cons]; omega
    rw [e] at this
    exact this


theorem der_word_iff {α} (L : Lang α) (lbcount mcount : Nat) (y : α) (ys la : List α) :
    der_word (y :: ys) L (.right lbcount (mcount + ys.length.succ) 0 la) ↔ L (.middle lbcount mcount (y, ys) la) := by
  induction ys generalizing L mcount y with
  | nil => cases mcount <;> simp [der_word, der]
  | cons y' ys' ih =>
    have := ih (der y L) (mcount + 1) y'
    have e : mcount + 1 + ys'.length.succ = mcount + (y' :: ys').length.succ := by simp [List.length_cons]; omega
    rw [e] at this
    exact this

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

/-- Helper for Theorem 3.2.2: membership of the empty right word in an existential derivative. -/
theorem xder_right_iff {α} (l : Lang α) (w : List α) (lbc mc lac : Nat) :
    xder w l (.right lbc mc lac []) ↔
      (∃ (lbc' : Nat) (lb : NEList α) (main la : List α),
        w = toList lb ++ main ++ la ∧ lbc = lbc' + (toList lb).length ∧ mc = main.length ∧ lac = la.length ∧ l (.left lbc' lb main la))
      ∨ (∃ (mc' : Nat) (main : NEList α) (la : List α),
        w = toList main ++ la ∧ mc = mc' + (toList main).length ∧ lac = la.length ∧ l (.middle lbc mc' main la))
      ∨ (∃ lac' : Nat, lac = lac' + w.length ∧ l (.right lbc mc lac' w)) := by
  induction w generalizing l lbc mc lac with
  | nil =>
    constructor
    · intro h; right; right; exact ⟨lac, rfl, h⟩
    · rintro (⟨_, _, _, _, hw, _⟩ | ⟨_, _, _, hw, _⟩ | ⟨_, hm, h⟩)
      · simp [toList] at hw
      · simp [toList] at hw
      · simp at hm; subst hm; exact h
  | cons hd tl ih =>
    show xder tl _ _ ↔ _
    rw [ih]
    simp only [Operators.union]
    constructor
    · rintro (⟨lbc', lb, main, la, hw, hlbc, hmc, hlac, h⟩ | ⟨mc', main, la, hw, hmc, hlac, h⟩ | ⟨lac', hlac, h⟩)
      · rcases h with h | h | h
        · cases lbc' with
          | zero => simp [derLB] at h
          | succ k =>
            left
            refine ⟨k, (hd, toList lb), main, la, by simp [toList, hw], ?_, hmc, hlac, h⟩
            simp [toList] at hlbc ⊢; omega
        · simp [der] at h
        · simp [derLA] at h
      · rcases h with h | h | h
        · cases lbc with
          | zero => simp [derLB] at h
          | succ k =>
            cases mc' with
            | succ _ => simp [derLB] at h
            | zero =>
              left
              exact ⟨k, (hd, []), toList main, la, by simp [toList, hw], by simp [toList], by simpa using hmc, hlac, h⟩
        · cases mc' with
          | zero => simp [der] at h
          | succ k =>
            right; left
            refine ⟨k, (hd, toList main), la, by simp [toList, hw], ?_, hlac, h⟩
            simp [toList] at hmc ⊢; omega
        · simp [derLA] at h
      · rcases h with h | h | h
        · cases lbc with
          | zero => simp [derLB] at h
          | succ k =>
            cases mc with
            | succ _ => simp [derLB] at h
            | zero =>
              cases lac' with
              | succ _ => simp [derLB] at h
              | zero =>
                left
                exact ⟨k, (hd, []), [], tl, by simp [toList], by simp [toList], rfl, by simpa using hlac, h⟩
        · cases mc with
          | zero => simp [der] at h
          | succ k =>
            cases lac' with
            | succ _ => simp [der] at h
            | zero =>
              right; left
              exact ⟨k, (hd, []), tl, by simp [toList], by simp [toList], by simpa using hlac, h⟩
        · cases lac' with
          | zero => simp [derLA] at h
          | succ k =>
            right; right
            exact ⟨k, by simp at hlac ⊢; omega, h⟩
    · rintro (⟨lbc', ⟨x, xs⟩, main, la, hw, hlbc, hmc, hlac, h⟩ | ⟨mc', ⟨y, ys⟩, la, hw, hmc, hlac, h⟩ | ⟨lac', hlac, h⟩)
      · simp only [toList, List.cons_append, List.cons.injEq] at hw
        obtain ⟨rfl, hw⟩ := hw
        subst hmc hlac
        simp only [toList, List.length_cons] at hlbc
        subst hlbc
        cases xs with
        | nil =>
          cases main with
          | nil =>
            right; right
            exact ⟨0, by simp [hw], Or.inl (by simp only [List.nil_append] at hw; subst hw; exact h)⟩
          | cons y ys =>
            right; left
            exact ⟨0, (y, ys), la, by simp [toList, hw], by simp [toList], rfl, Or.inl h⟩
        | cons x' xs' =>
          left
          refine ⟨lbc' + 1, (x', xs'), main, la, by simp [toList, hw], by simp [toList]; omega, rfl, rfl, Or.inl h⟩
      · simp only [toList, List.cons_append, List.cons.injEq] at hw
        obtain ⟨rfl, hw⟩ := hw
        subst hmc hlac
        cases ys with
        | nil =>
          right; right
          exact ⟨0, by simp [hw], Or.inr (Or.inl (by simp only [List.nil_append] at hw; subst hw; exact h))⟩
        | cons y' ys' =>
          right; left
          refine ⟨mc' + 1, (y', ys'), la, by simp [toList, hw], by simp [toList]; omega, rfl, Or.inr (Or.inl h)⟩
      · right; right
        refine ⟨lac' + 1, by simp only [List.length_cons] at hlac; omega, Or.inr (Or.inr h)⟩

/-- Theorem 3.2.2 — existential derivative and indexed nullability. -/
theorem xder_nullable_iff {α} (l : Lang α) (w : List α) (lbc mc lac : Nat) :
    nullable (xder w l) lbc mc lac ↔
      (∃ (lbc' : Nat) (lb : NEList α) (main la : List α),
        w = toList lb ++ main ++ la ∧ lbc = lbc' + (toList lb).length ∧ mc = main.length ∧ lac = la.length ∧ l (.left lbc' lb main la))
      ∨ (∃ (mc' : Nat) (main : NEList α) (la : List α),
        w = toList main ++ la ∧ mc = mc' + (toList main).length ∧ lac = la.length ∧ l (.middle lbc mc' main la))
      ∨ (∃ lac' : Nat, lac = lac' + w.length ∧ l (.right lbc mc lac' w)) :=
  xder_right_iff l w lbc mc lac

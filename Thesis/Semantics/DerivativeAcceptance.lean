import Thesis.Semantics.StructuredWords
import Thesis.Semantics.Operators
import Thesis.Semantics.Derivatives

namespace DerAccept

open StructuredWords



theorem derLB_word_iff {α} (L : Lang α) (x : α) (xs main la : List α) :
    derLB_word (x :: xs) L (mk_mcount_word 0 main la) ↔ L (.left (x, xs) main la) := by
  induction xs generalizing x L with
  | nil => cases main <;> exact Iff.rfl
  | cons x' xs' ih => exact ih (derLB x L) x'


theorem der_word_iff {α} (L : Lang α) (mcount : Nat) (y : α) (ys la : List α) :
    der_word (y :: ys) L (.right (mcount + ys.length.succ) 0 la) ↔ L (.middle mcount (y, ys) la) := by
  induction ys generalizing L mcount y with
  | nil => cases mcount <;> simp [der_word, der]
  | cons y' ys' ih =>
    have := ih (der y L) (mcount + 1) y'
    have e : mcount + 1 + ys'.length.succ = mcount + (y' :: ys').length.succ := by simp [List.length_cons]; omega
    rw [e] at this
    exact this

theorem derLA_word_iff {α} (L : Lang α) (mcount lacount : Nat) (la : List α) :
    derLA_word la L (.right mcount (lacount + la.length) []) ↔ L (.right mcount lacount la) := by
  induction la generalizing L mcount lacount with
  | nil => simp [derLA_word]
  | cons z zs ih =>
    have := ih (derLA z L) (mcount) (lacount.succ)
    simp [Nat.add_assoc, Nat.one_add, derLA] at ⊢ this
    exact this

-- Theorem 3.2.1 (Derivative characterization of membership).
theorem membership_left_iff_nullable (l : Lang α) (lb : NEList α) (main la : List α) :
    l (.left lb main la) ↔ nullable_n_m (derLA_word la (der_word main (derLB_word (toList lb) l))) main.length la.length := by
  have hlb := derLB_word_iff l lb.fst lb.snd main la
  have hla := derLA_word_iff (der_word main (derLB_word (toList lb) l)) main.length 0 la
  rw [Nat.zero_add] at hla
  refine Iff.trans ?_ hla.symm
  cases main with
  | nil => exact hlb.symm
  | cons y ys =>
    have hder := der_word_iff (derLB_word (toList lb) l) 0 y ys la
    rw [Nat.zero_add] at hder
    exact hlb.symm.trans hder.symm

theorem membership_middle_iff_nullable (L : Lang α) (mcount : Nat) (main : NEList α) (la : List α) :
    L (.middle mcount main la) ↔ nullable_n_m (derLA_word la (der_word (toList main) L)) (mcount + (toList main).length) la.length := by
  have hla := derLA_word_iff (der_word (toList main) L) (mcount + (toList main).length) 0 la
  rw [Nat.zero_add] at hla
  exact (der_word_iff L mcount main.fst main.snd la).symm.trans hla.symm

theorem membership_right_iff_nullable (L : Lang α) (mcount lacount : Nat) (la : List α) :
    L (.right mcount lacount la) ↔ nullable_n_m (derLA_word la L) mcount (lacount + la.length) := by
  exact (derLA_word_iff L mcount lacount la).symm

/-- Theorem 3.2.2 — existential derivative and indexed nullability. -/
theorem xder_nullable_iff {α} (L : Lang α) (w : List α) (n : Nat) :
    nullable_n (xder w L) n ↔
      (∃ x : NEList α, ∃ y : List α, w = toList x ++ y ∧ y.length = n ∧ L (Sum.inl (x, y)))
      ∨ (∃ k : Nat, k + w.length = n ∧ L (Sum.inr (k, w))) := by
  induction w generalizing L n with
  | nil =>
    simp only [xder, nullable_n, List.length]
    constructor
    · intro h
      right
      exact ⟨n, rfl, h⟩
    · rintro (⟨x, y, hw, _, _⟩ | ⟨k, hk, hL⟩)
      · cases x with
        | mk xh xt =>
          simp [toList] at hw
      · simp at hk
        subst hk
        exact hL
  | cons hd tl ih =>
    simp only [xder, List.length]
    rw [ih (der hd L ∪ derLA hd L)]
    constructor
    . intro h
      cases h with
      | inl h =>
        left; obtain ⟨x, y, htl, hy, hunion⟩ := h
        refine ⟨(hd, toList x), y, by simp [toList] at ⊢ htl; trivial, hy, ?_⟩
        cases hunion with
        | inl hder => cases x with | mk x xs => simp [der, toList] at hder ⊢; exact hder
        | inr hderLA => simp [derLA] at hderLA
      | inr h =>
        obtain ⟨k, hk, hunion⟩ := h
        cases k with
        | zero =>
          cases hunion with
          | inl hder => left; exact ⟨(hd, []), tl, by simp [toList], by rw [Nat.zero_add] at hk; exact hk, hder⟩
          | inr hderLA => simp [derLA] at hderLA
        | succ k =>
          cases hunion with
          | inl hder => simp [der] at hder
          | inr hderLA => right; exact ⟨k, by rw [Nat.succ_add_eq_add_succ] at hk; exact hk, hderLA⟩
    . intro h
      cases h with
      | inl h =>
        obtain ⟨x, y, hw, hy, h⟩ := h
        cases x with | mk x xs =>
          cases xs with
          | nil => right; simp [toList] at hw; exact ⟨0, by rw [hw.2, Nat.zero_add]; exact hy, by rw [hw.1, hw.2]; exact Or.inl h⟩
          | cons xshd xstl => left; simp [toList] at hw; exact ⟨(xshd, xstl), y, by simp [toList] at ⊢ hw; exact hw.2, hy, by rw [hw.1]; exact Or.inl h⟩
      | inr h => obtain ⟨k, hk, h⟩ := h; right; exact ⟨k.succ, by rw [Nat.succ_add_eq_add_succ]; exact hk, Or.inr h⟩

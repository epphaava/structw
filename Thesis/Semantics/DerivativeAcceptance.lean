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
theorem xder_nullable_iff {α} (l : Lang α) (w : List α) (n m : Nat) :
    nullable_n_m (xder w l) n m ↔
      (∃ (lb : NEList α) (main la : List α),
        w = toList lb ++ main ++ la ∧ n = main.length ∧ m = la.length ∧ l (.left lb main la))
      ∨ (∃ (mc : Nat) (main : NEList α) (la : List α),
        w = toList main ++ la ∧ n = mc + (toList main).length ∧ m = la.length ∧ l (.middle mc main la))
      ∨ (∃ lac : Nat, m = lac + w.length ∧ l (.right n lac w)) := by
  induction w generalizing l n m with
  | nil =>
    constructor
    · intro h; right; right; exact ⟨m, rfl, h⟩
    · rintro (⟨_, _, _, hw, _⟩ | ⟨_, _, _, hw, _⟩ | ⟨_, hm, h⟩)
      · simp [toList] at hw
      · simp [toList] at hw
      · simp at hm; subst hm; exact h
  | cons hd tl ih =>
    simp [xder, ih]
    constructor
    · rintro (⟨lb, main, la, hw, hn, hm, h⟩ | ⟨mc, main, la, hw, hn, hm, h⟩ | ⟨lac, hm, h⟩)
      · left; exact ⟨(hd, toList lb), main, la, by simp [toList, hw], hn, hm, by simp [Operators.union, derLB, der, derLA] at h; exact h⟩
      · cases mc with
        | zero => left; exact ⟨(hd, []), toList main, la, by simp [toList, hw], by simpa using hn, hm, by simp [Operators.union, derLB, der, derLA] at h; exact h⟩
        | succ mc => right; left; exact ⟨mc, (hd, toList main), la, by simp [toList, hw], by simp [toList] at hn ⊢; omega, hm, by simp [Operators.union, derLB, der, derLA] at h; exact h⟩
      · rcases h with h | h | h
        · cases n with
          | succ n => simp [derLB] at h
          | zero =>
            cases lac with
            | succ lac => simp [derLB] at h
            | zero => left; exact ⟨(hd, []), [], tl, by simp [toList], rfl, by simp at hm; exact hm, h⟩;
        · cases lac with
          | succ lac => cases n <;> simp [der] at h
          | zero =>
            cases n with
            | zero => simp [der] at h
            | succ n => right; left; exact ⟨n, (hd, []), tl, by simp [toList], by simp [toList], by simp at hm; exact hm, h⟩
        · cases lac with
          | zero => simp [derLA] at h
          | succ lac => right; right; exact ⟨lac, by simp [Nat.add_comm] at hm ⊢; omega, h⟩;
    · rintro (⟨⟨x, xs⟩, main, la, hw, hn, hm, h⟩ | ⟨mc, ⟨y, ys⟩, la, hw, hn, hm, h⟩ | ⟨lac, hm, h⟩)
      · obtain ⟨rfl, hw⟩ := hw
        cases xs with
        | nil =>
          cases main with
          | nil => subst hn; right; right; exact ⟨0, by simp; exact hm, Or.inl h⟩
          | cons y ys => right; left; exact ⟨0, (y, ys), la, by simp [toList], by simp [toList]; exact hn, hm, Or.inl h⟩
        | cons x' xs' => left; exact ⟨(x', xs'), main, la, by simp [toList], hn, hm, Or.inl h⟩
      · obtain ⟨rfl, hw⟩ := hw
        cases ys with
        | nil => subst hn; right; right; exact ⟨0, by simp; exact hm, Or.inr (Or.inl h)⟩
        | cons y' ys' => right; left; exact ⟨mc + 1, (y', ys'), la, by simp [toList], by simp [toList] at hn ⊢; omega, hm, .inr (.inl h)⟩
      · right; right; refine ⟨lac + 1, ?_, .inr (.inr h)⟩; omega

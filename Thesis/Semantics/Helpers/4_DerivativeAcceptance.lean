import Thesis.Semantics.«1_StructuredWords»
import Thesis.Semantics.«2_Operators»
import Thesis.Semantics.«3_Derivatives»

namespace DerAcceptHelpers

open StructuredWords

theorem exists_split_iff {α} (l : Lang α) (w : List α) (mc lac : Nat) :
    (∃ u, is_split w mc lac u ∧ l u) ↔
      (∃ (lb : NEList α) (main la : List α),
        w = toList lb ++ main ++ la ∧ mc = main.length ∧ lac = la.length ∧ l (.left lb main la))
      ∨ (∃ (mc' : Nat) (main : NEList α) (la : List α),
        w = toList main ++ la ∧ mc = mc' + (toList main).length ∧ lac = la.length ∧ l (.middle mc' main la))
      ∨ (∃ lac' : Nat, lac = lac' + w.length ∧ l (.right mc lac' w)) := by
  constructor
  · rintro ⟨u, ⟨hw, hc⟩, h⟩
    cases u with
    | left lb main la =>
      simp only [Word.final_counts, Prod.mk.injEq] at hc
      exact Or.inl ⟨lb, main, la, hw.symm, hc.1.symm, hc.2.symm, h⟩
    | middle mc' main la =>
      simp only [Word.final_counts, Prod.mk.injEq] at hc
      exact Or.inr (Or.inl ⟨mc', main, la, hw.symm, hc.1.symm, hc.2.symm, h⟩)
    | right mc' lac' la =>
      simp only [Word.final_counts, Prod.mk.injEq] at hc
      simp only [Word.word_to_list] at hw
      obtain ⟨rfl, rfl⟩ := hc
      subst hw
      exact Or.inr (Or.inr ⟨lac', rfl, h⟩)
  · rintro (⟨lb, main, la, hw, hmc, hlac, h⟩ | ⟨mc', main, la, hw, hmc, hlac, h⟩ | ⟨lac', hlac, h⟩)
    · exact ⟨.left lb main la, ⟨hw.symm, by simp [Word.final_counts, hmc, hlac]⟩, h⟩
    · exact ⟨.middle mc' main la, ⟨hw.symm, by simp [Word.final_counts, hmc, hlac]⟩, h⟩
    · exact ⟨.right mc lac' w, ⟨rfl, by simp [Word.final_counts, hlac]⟩, h⟩

theorem xder_right_iff {α} (l : Lang α) (w : List α) (mc lac : Nat) :
    xder w l (.right mc lac []) ↔
      (∃ (lb : NEList α) (main la : List α),
        w = toList lb ++ main ++ la ∧ mc = main.length ∧ lac = la.length ∧ l (.left lb main la))
      ∨ (∃ (mc' : Nat) (main : NEList α) (la : List α),
        w = toList main ++ la ∧ mc = mc' + (toList main).length ∧ lac = la.length ∧ l (.middle mc' main la))
      ∨ (∃ lac' : Nat, lac = lac' + w.length ∧ l (.right mc lac' w)) := by
  induction w generalizing l mc lac with
  | nil =>
    constructor
    · intro h; right; right; exact ⟨lac, rfl, h⟩
    · rintro (⟨_, _, _, hw, _⟩ | ⟨_, _, _, hw, _⟩ | ⟨_, hm, h⟩)
      · simp [toList] at hw
      · simp [toList] at hw
      · simp at hm; subst hm; exact h
  | cons hd tl ih =>
    show xder tl _ _ ↔ _
    rw [ih _]
    simp only [Operators.union]
    constructor
    · rintro (⟨lb, main, la, hw, hmc, hlac, h⟩ | ⟨mc', main, la, hw, hmc, hlac, h⟩ | ⟨lac', hlac, h⟩)
      · rcases h with h | h | h
        · exact Or.inl ⟨(hd, toList lb), main, la, by simp [toList, hw], hmc, hlac, h⟩
        · simp [der] at h
        · simp [derLA] at h
      · rcases h with h | h | h
        · cases mc' with
          | succ _ => simp [derLB] at h
          | zero => exact Or.inl ⟨(hd, []), toList main, la, by simp [toList, hw], by simpa using hmc, hlac, h⟩
        · cases mc' with
          | zero => simp [der] at h
          | succ k =>
            right; left
            refine ⟨k, (hd, toList main), la, by simp [toList, hw], ?_, hlac, h⟩
            simp [toList] at hmc ⊢; omega
        · simp [derLA] at h
      · rcases h with h | h | h
        · cases mc with
          | succ _ => simp [derLB] at h
          | zero =>
            cases lac' with
            | succ _ => simp [derLB] at h
            | zero =>
              left
              exact ⟨(hd, []), [], tl, by simp [toList], rfl, by simpa using hlac, h⟩
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
    · rintro (⟨⟨x, xs⟩, main, la, hw, hmc, hlac, h⟩ | ⟨mc', ⟨y, ys⟩, la, hw, hmc, hlac, h⟩ | ⟨lac', hlac, h⟩)
      · simp only [toList, List.cons_append, List.cons.injEq] at hw
        obtain ⟨rfl, hw⟩ := hw
        subst hmc hlac
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
          exact ⟨(x', xs'), main, la, by simp [toList, hw], rfl, rfl, Or.inl h⟩
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

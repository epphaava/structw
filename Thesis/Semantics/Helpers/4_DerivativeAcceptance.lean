import Thesis.Semantics.«1_StructuredWords»
import Thesis.Semantics.«2_Operators»
import Thesis.Semantics.«3_Derivatives»

namespace DerAcceptHelpers

open StructuredWords

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

import Thesis.Semantics.kLang.«1_StructuredWords»
import Thesis.Semantics.kLang.«2_Operators»
import Thesis.Semantics.Lang.«3_Derivatives»

namespace kDerivatives

open kStructuredWords
open kOperators
open StructuredWords
open Derivatives


-- Lookbehind derivative
def derLB {α} (a : α) (l : kLang α n) : kLang α (n.succ) :=
  ⟨λ w => Derivatives.derLB a l.val w,
   λ w _ => by
    match w with
    | .left .. => simp [word_steps]
    | .middle 0 .. => simp [word_steps]
    | .right 0 0 _ => simp [word_steps]
    | .middle (_ + 1) .. | .right (_ + 1) _ _ | .right 0 (_ + 1) _ => contradiction⟩

-- Match derivative
def der {α} (a : α) (l : kLang α n) : kLang α (n.succ) :=
  ⟨λ w => Derivatives.der a l.val w,
   λ w hw => by
    match w with
    | .middle (_ + 1) .. => have hb := l.2 _ hw; simp [word_steps] at hb ⊢; omega
    | .right (_ + 1) 0 _ => have hb := l.2 _ hw; simp [word_steps] at hb ⊢; omega
    | .left .. | .middle 0 .. | .right 0 _ _ | .right (_ + 1) (_ + 1) _ => contradiction⟩

-- Lookahead derivative
def derLA (a : α) (l : kLang α n) : kLang α (n + 1) :=
  ⟨λ w => Derivatives.derLA a l.val w,
   λ w hw => by
    match w with
    | .right _ (_ + 1) _ => have hb := l.2 _ hw; simp [word_steps] at hb ⊢; omega
    | .left .. | .middle .. | .right _ 0 _ => contradiction⟩

-- Definition 3.2.3 (Iterated derivatives).

def derLB_word (w : List α) (l : kLang α n) : kLang α (n + w.length) :=
  match w with
  | [] => l
  | a :: w =>
    let l' := derLB_word w (derLB a l)
    ⟨l'.1, λ u hu => by have := l'.2 u hu; simp at this ⊢; omega⟩

def der_word {α} (w : List α) (l : kLang α n) : kLang α (n + w.length) :=
  match w with
  | [] => l
  | a :: w =>
    let l' := der_word w (der a l)
    ⟨l'.1, λ u hu => by have := l'.2 u hu; simp at this ⊢; omega⟩

def derLA_word (w : List α) (l : kLang α n) : kLang α (n + w.length) :=
  match w with
  | [] => l
  | a :: w =>
    let l' := derLA_word w (derLA a l)
    ⟨l'.1, λ u hu => by have := l'.2 u hu; simp at this ⊢; omega⟩



 /-- Definition 3.2.4 (Indexed nullability). -/
def nullable (l : kLang α k) (mcount lacount : Nat)  : Prop := l (.right mcount lacount [])

 /-- Existential nullability. -/
def xnullable (l : kLang α k) : Prop :=
  ∃ mcount lacount, nullable l mcount lacount


 -- Definition 3.2.5 (Existential derivative).
def xder (w : List α) (l : kLang α n) : kLang α (n + w.length) :=
  match w with
  | [] => l
  | hd :: tl =>
    let d : kLang α (n.succ) :=
      ⟨(derLB hd l).1 ∪ (der hd l).1 ∪ (derLA hd l).1, λ u hu =>
        hu.elim ((derLB hd l).2 u) (λ h => h.elim ((der hd l).2 u) ((derLA hd l).2 u))⟩
    let l' := xder tl d
    ⟨l'.1, λ u hu => by have := l'.2 u hu; simp at this ⊢; omega⟩


-- Lemma 3.2.1.
theorem derLB_der_empty (L : kLang α n) : derLB a (der a L) ≐ (∅ : kLang α (n + 2)) :=
  Derivatives.derLB_der_empty (a := a) L.1

theorem der_derLA_empty (L : kLang α n) : der a (derLA a L) ≐ (∅ : kLang α (n + 2)) :=
  Derivatives.der_derLA_empty (a := a) L.1

theorem derLB_derLA_empty (L : kLang α n) : derLB a (derLA a L) ≐ (∅ : kLang α (n + 2)) :=
  Derivatives.derLB_derLA_empty (a := a) L.1


theorem xder_val (s : List α) (l : kLang α n) : (xder s l).1 = Derivatives.xder s l.1 := by
  induction s generalizing n l with
  | nil => rfl
  | cons a tl ih => exact ih _

/-- Helper for Theorem 4.2.3 (`xder_correct`). -/
theorem xder_congr {α} (s : List α) (l₁ l₂ : kLang α n) : l₁ ≐ l₂ → xder s l₁ ≐ xder s l₂ := by
  intro h w
  simp [xder_val]
  exact Derivatives.xder_congr s _ _ h w

end kDerivatives

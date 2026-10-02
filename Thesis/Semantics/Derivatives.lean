import Thesis.Semantics.StructuredWords
import Thesis.Semantics.Operators

open StructuredWords
open Operators

-- Lookbehind derivative
def derLB {α} (a : α) (l : Lang α) : Lang α := λ w =>
  match w with
  | .left lb main la => l (.left (a, toList lb) main la)
  | .middle 0 main la => l (.left (a, []) (toList main) la)
  | .right 0 0 la => l (.left (a, []) [] la)
  | _ => False

-- Match derivative
def der {α} (a : α) (l : Lang α) : Lang α := λ w =>
  match w with
  | .middle (.succ mcount) main la => l (.middle mcount (a, toList main) la)
  | .right (.succ mcount) 0 la => l (.middle mcount (a, []) la)
  | _ => False

-- Lookahead derivative
def derLA (a : α) (l : Lang α) : Lang α := λ w =>
  match w with
  | .right mcount (.succ lacount) la => l (.right mcount lacount (a :: la))
  | _ => False

-- Definition 3.2.3 (Iterated derivatives).

def derLB_word (w : List α) (l : Lang α) : Lang α :=
  match w with
  | [] => l
  | a :: w => derLB_word w (derLB a l)

def der_word {α} (w : List α) (l : Lang α) : Lang α :=
  match w with
  | [] => l
  | a :: w => der_word w (der a l)

def derLA_word (w : List α) (l : Lang α) : Lang α :=
  match w with
  | [] => l
  | a :: w => derLA_word w (derLA a l)



 /-- Definition 3.2.4 (Indexed nullability). -/
def nullable_n_m (l : Lang α) (mcount lacount : Nat) : Prop :=
  l (.right mcount lacount [])

 -- Definition 3.2.5 (Existential derivative).
def xder (w : List α) (l : Lang α) : Lang α :=
  match w with
  | [] => l
  | hd :: tl => xder tl ((derLB hd l) ∪ (der hd l) ∪ (derLA hd l))


/- -- Lemma 3.2.1.
theorem der_derLA_empty (L : Lang α) : der a (derLA a L) ≐ ∅ := by
  intro w
  cases w with
  | inl w => cases w with | mk u v => cases u with | mk hd tl => simp [der, derLA, empty]
  | inr w => cases w with | mk n v => cases n <;> simp [der, derLA, empty]
 -/
/- /-- Helper for Theorem 4.2.3 (`xder_correct`). -/
theorem xder_congr {α} (s : List α) (l₁ l₂ : Lang α) : l₁ ≐ l₂ → xder s l₁ ≐ xder s l₂ := by
  intro h
  induction s generalizing l₁ l₂ with
  | nil => simp [xder]; trivial
  | cons a tl ih =>
    have hder : der a l₁ ≐ der a l₂ := by
      intro u; match u with
      | Sum.inl ((hd, tl), v) => exact h (Sum.inl ((a, hd :: tl), v))
      | Sum.inr (n, v) =>
        cases n with
        | zero => exact h (Sum.inl ((a, []), v))
        | succ n => simp [der]
    have hderLA : derLA a l₁ ≐ derLA a l₂ := by
      intro u; match u with
      | Sum.inl ((hd, tl), v) => simp [derLA]
      | Sum.inr (n, v) =>
        cases n with
        | zero => simp [derLA]
        | succ n => simp [derLA]; exact h (Sum.inr (n, a :: v))
    have hunion : (der a l₁ ∪ derLA a l₁) ≐ (der a l₂ ∪ derLA a l₂) := by
      intro u; simp [union, hder u, hderLA u]
    exact ih (der a l₁ ∪ derLA a l₁) (der a l₂ ∪ derLA a l₂) hunion
 -/

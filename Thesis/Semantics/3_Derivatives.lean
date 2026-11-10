import Thesis.Semantics.«1_StructuredWords»
import Thesis.Semantics.«2_Operators»

open StructuredWords
open Operators

-- Lookbehind derivative
def derLB {α} (a : α) (l : Lang α) : Lang α := λ w =>
  match w with
  | .left lb main la => l (.left (a, toList lb) main la)
  | .middle  0 main la => l (.left (a, []) (toList main) la)
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
def nullable (l : Lang α) (mcount lacount : Nat)  : Prop := l (.right mcount lacount [])

 /-- Existential nullability. -/
def xnullable (l : Lang α) : Prop :=
  ∃ mcount lacount, nullable l mcount lacount


 -- Definition 3.2.5 (Existential derivative).
def xder (w : List α) (l : Lang α) : Lang α :=
  match w with
  | [] => l
  | hd :: tl => xder tl ((derLB hd l) ∪ (der hd l) ∪ (derLA hd l))


-- Lemma 3.2.1.
theorem derLB_der_empty (L : Lang α) : derLB a (der a L) ≐ ∅ := by
  intro w
  rcases w with ⟨⟩ | ⟨_ | _⟩ | ⟨_ | _, _ | _⟩ <;> simp [derLB, der, empty]

theorem der_derLA_empty (L : Lang α) : der a (derLA a L) ≐ ∅ := by
  intro w
  rcases w with ⟨⟩ | ⟨_ | _⟩ | ⟨_ | _, _ | _⟩ <;> simp [derLA, der, empty]

theorem derLB_derLA_empty (L : Lang α) : derLB a (derLA a L) ≐ ∅ := by
  intro w
  rcases w with ⟨⟩ | ⟨_ | _⟩ | ⟨_ | _, _ | _⟩ <;> simp [derLB, derLA, empty]


/-- Helper for Theorem 4.2.3 (`xder_correct`). -/
theorem xder_congr {α} (s : List α) (l₁ l₂ : Lang α) : l₁ ≐ l₂ → xder s l₁ ≐ xder s l₂ := by
  intro h
  induction s generalizing l₁ l₂ with
  | nil => simp [xder]; trivial
  | cons a tl ih =>
    -- Each derivative either looks `l` up at a single word or is `False`, so congruence is immediate.
    have hderLB : derLB a l₁ ≐ derLB a l₂ := by
      intro w; simp only [derLB]; split <;> first | exact h _ | exact Iff.rfl
    have hder : der a l₁ ≐ der a l₂ := by
      intro w; simp only [der]; split <;> first | exact h _ | exact Iff.rfl
    have hderLA : derLA a l₁ ≐ derLA a l₂ := by
      intro w; simp only [derLA]; split <;> first | exact h _ | exact Iff.rfl
    have hunion : (derLB a l₁ ∪ der a l₁ ∪ derLA a l₁) ≐ (derLB a l₂ ∪ der a l₂ ∪ derLA a l₂) := by
      intro u; simp [union, hderLB u, hder u, hderLA u]
    exact ih (derLB a l₁ ∪ der a l₁ ∪ derLA a l₁) (derLB a l₂ ∪ der a l₂ ∪ derLA a l₂) hunion

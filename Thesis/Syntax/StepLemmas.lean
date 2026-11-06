import Thesis.Syntax.«1_Expressions»
import Thesis.Semantics.«2_Operators»

/-! General facts about steps on languages, used by the derivative
correctness proofs for stepped atoms. -/

namespace DerCorrect

open SRegex
open StructuredWords
open Operators

section
variable {α : Type}

/-- A function on languages that respects `≐`. -/
def Congr (f : Lang α → Lang α) : Prop := ∀ l₁ l₂, l₁ ≐ l₂ → f l₁ ≐ f l₂

theorem lbStep_congr : Congr (α := α) lbStep := by
  intro l₁ l₂ h w; unfold lbStep; split <;> first | exact h _ | exact Iff.rfl

theorem matchStep_congr : Congr (α := α) matchStep := by
  intro l₁ l₂ h w; unfold matchStep; split <;> first | exact h _ | exact Iff.rfl

theorem laStep_congr : Congr (α := α) laStep := by
  intro l₁ l₂ h w; unfold laStep; split <;> first | exact h _ | exact Iff.rfl

theorem repeat_congr {f : Lang α → Lang α} (hf : Congr f) (n : Nat) :
    Congr (Nat.repeat f n) := by
  induction n with
  | zero => intro l₁ l₂ h; exact h
  | succ n ih => intro l₁ l₂ h; exact hf _ _ (ih _ _ h)

theorem repeat_comm {f g : Lang α → Lang α} (hf : Congr f) (hc : ∀ l, g (f l) ≐ f (g l)) (n : Nat) (l : Lang α) :
    g (Nat.repeat f n l) ≐ Nat.repeat f n (g l) := by
  induction n with
  | zero => intro w; exact Iff.rfl
  | succ n ih => intro w; exact (hc _ w).trans (hf _ _ ih w)

theorem repeat_empty {f : Lang α → Lang α} (hf : Congr f) (h0 : f ∅ ≐ ∅) (n : Nat) : Nat.repeat f n ∅ ≐ ∅ := by
  induction n with
  | zero => intro w; exact Iff.rfl
  | succ n ih => intro w; exact (hf _ _ ih w).trans (h0 w)

theorem lbStep_empty : lbStep (∅ : Lang α) ≐ ∅ := by
  intro w; unfold lbStep; split <;> simp [empty]

theorem matchStep_empty : matchStep (∅ : Lang α) ≐ ∅ := by
  intro w; unfold matchStep; split <;> simp [empty]

theorem steps_congr (s : Steps) : Congr (SRegex.sem.steps (α := α) s) := by
  intro l₁ l₂ h
  exact repeat_congr lbStep_congr _ _ _ (repeat_congr matchStep_congr _ _ _ (repeat_congr laStep_congr _ _ _ h))

theorem steps_empty (s : Steps) (h : s.la = 0) : SRegex.sem.steps (α := α) s ∅ ≐ ∅ := by
  intro w
  simp [SRegex.sem.steps, h, Nat.repeat]
  exact (repeat_congr lbStep_congr _ _ _ (repeat_empty matchStep_congr matchStep_empty _) w).trans
    (repeat_empty lbStep_congr lbStep_empty _ w)

theorem repeat_succ_inner (f : Lang α → Lang α) (n : Nat) (l : Lang α) :
    Nat.repeat f n (f l) = Nat.repeat f (n + 1) l := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Nat.repeat] at *; rw [ih]

theorem star_congr {l₁ l₂ b₁ b₂ : Lang α} (hl : l₁ ≐ l₂) (hb : b₁ ≐ b₂) :
    star l₁ b₁ ≐ star l₂ b₂ := by
  intro w
  constructor
  · intro h
    induction h with
    | inUnit w hu => exact star_help.inUnit w ((hb w).mp hu)
    | inConcat w₁ w₂ w h₁ _ hwc ih => exact star_help.inConcat w₁ w₂ w ((hl w₁).mp h₁) ih hwc
  · intro h
    induction h with
    | inUnit w hu => exact star_help.inUnit w ((hb w).mpr hu)
    | inConcat w₁ w₂ w h₁ _ hwc ih => exact star_help.inConcat w₁ w₂ w ((hl w₁).mpr h₁) ih hwc

/-- `I` with zero steps is plain `I`. -/
theorem sem_unit_zero [DecidableEq α] : SRegex.sem (α := α) (.unit [Steps.zeroSteps]) ≐ Operators.unit := by
  intro w
  simp [SRegex.sem, SRegex.sem.atom, SRegex.sem.steps, Steps.zeroSteps, Nat.repeat, union, empty]

end

end DerCorrect

import Thesis.SyntaxOld.Expressions
import Thesis.SyntaxOld.Derivatives
import Thesis.SyntaxOld.Nullability
import Thesis.SyntaxOld.NullabilityCorrectness
import Thesis.Semantics.«3_Derivatives»
import Thesis.Semantics.«5_LookbehindDerivativeLaws»
import Thesis.Semantics.«6_LookaheadDerivativeLaws»
import Thesis.Semantics.«7_DerivativeLaws»


namespace DerCorrect

open Expr
open ExprDerivatives
open NullabilityCorrect
open DerCorrect
open DerLaws
open StructuredWords
open Operators

open derLBLaws
open derLALaws

theorem star_congr {α} {l₁ l₂ b₁ b₂ : Lang α} (hl : l₁ ≐ l₂) (hb : b₁ ≐ b₂) :
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

mutual
/-- Theorem 4.2.1 (match derivative): `⟦D_a r⟧ = der_a ⟦r⟧`. -/
theorem der_correct {α} [DecidableEq α] (a : α) (r : Expr α) : (der a (sem r) ) ≐ (sem (D a r) ) := by
  intro w
  match r with
  | .empty => rw [D, sem, der_empty a]
  | .unit => rw [D, sem, sem, der_unit a]
  | .top => rw [sem, D, der_top a, sem, complement, complement, sem, sem]; rfl
  | .symbol x =>
    by_cases h : x = a
    · rw [sem, D, der_symb_match x a h]; simp [sem, complement, matchStep, unit, h]
    · rw [sem, D, der_symb_no_match x a h]; simp [sem, empty, if_neg (Ne.symm h)]
  | .plus r₁ r₂ => rw [D, sem, sem, der_union a (sem r₁) (sem r₂), union, union, der_correct a r₁, der_correct a r₂]
  | .intersection r₁ r₂ => rw [D, sem, sem, der_intersection a (sem r₁) (sem r₂), intersection, intersection, der_correct a r₁, der_correct a r₂]
  | .complement r₁ r₂ => rw [D, sem, sem, der_complement a (sem r₁) (sem r₂), complement, complement, der_correct a r₁, der_correct a r₂]
  | .mult r₁ r₂ =>
    rw [sem, der_concat a (sem r₁) (sem r₂), D, sem, sem, sem]
    constructor
    · intro h; cases h with
      | inl h =>
        obtain ⟨x, y, hx, hy, hc⟩ := h
        exact Or.inl ⟨x, y, (der_correct a r₁ x).mp hx, (derLB_correct a r₂ y).mp hy, hc⟩
      | inr h =>
        obtain ⟨x, y, hx, hy, hc⟩ := h
        exact Or.inr ⟨x, y, (derLA_correct a r₁ x).mp hx, (der_correct a r₂ y).mp hy, hc⟩
    · intro h; cases h with
      | inl h =>
        obtain ⟨x, y, hx, hy, hc⟩ := h
        exact Or.inl ⟨x, y, (der_correct a r₁ x).mpr hx, (derLB_correct a r₂ y).mpr hy, hc⟩
      | inr h =>
        obtain ⟨x, y, hx, hy, hc⟩ := h
        exact Or.inr ⟨x, y, (derLA_correct a r₁ x).mpr hx, (der_correct a r₂ y).mpr hy, hc⟩
  | .star r b =>
    rw [sem, D, sem, sem, der_star a (sem r)]
    have hx : ∀ x, star (derLA a (sem r)) I x ↔ sem (.star (DLA a r) I) x := by
      intro x; exact star_congr (derLA_correct a r) (fun _ => Iff.rfl) x
    have hy : ∀ y, (der a (sem b) ∪ (der a (sem r) • star (derLB a (sem r)) (derLB a (sem b)))) y ↔
        sem (D a b + (D a r • Expr.star (DLB a r) (DLB a b))) y := by
      intro y
      apply or_congr (der_correct a b y)
      constructor
      · rintro ⟨u, v, hu, hv, hc⟩; exact ⟨u, v, (der_correct a r u).mp hu, (star_congr (derLB_correct a r) (derLB_correct a b) v).mp hv, hc⟩
      · rintro ⟨u, v, hu, hv, hc⟩; exact ⟨u, v, (der_correct a r u).mpr hu, (star_congr (derLB_correct a r) (derLB_correct a b) v).mpr hv, hc⟩
    constructor
    · rintro ⟨x, y, h₁, h₂, hc⟩; exact ⟨x, y, (hx x).mp h₁, (hy y).mp h₂, hc⟩
    · rintro ⟨x, y, h₁, h₂, hc⟩; exact ⟨x, y, (hx x).mpr h₁, (hy y).mpr h₂, hc⟩
  | .lb r => exact der_lb a (sem r) w
  | .la r => exact der_la a (sem r) w
  | .lbStep r =>
    refine (der_lbStep a (sem r) w).trans ?_
    match w with
    | .left (_ + 1) _ _ _ | .middle (_ + 1) _ _ _ | .right (_ + 1) _ _ _ => simp [lbStep]; exact der_correct a r _
    | .left 0 _ _ _ | .middle 0 _ _ _ | .right 0 _ _ _ => simp [D, sem, lbStep]
  | .mStep r =>
    refine (der_matchStep a (sem r) w).trans ?_
    match w with
    | .middle _ (_ + 1) _ _ | .right _ (_ + 1) _ _ => simp [matchStep]; exact der_correct a r _
    | .left _ _ _ _ | .middle _ 0 _ _ | .right _ 0 _ _ => simp [D, sem, matchStep]
  | .laStep r => refine (der_laStep a (sem r) w).trans ?_; cases w <;> simp [D, sem]


theorem derLB_correct {α} [DecidableEq α] (a : α) (r : Expr α) : derLB a (sem r) ≐ sem (DLB a r) := by
  intro w
  match r with
  | .empty => rw [DLB, sem, derLB_empty a]
  | .unit => rw [sem, DLB, derLB_unit a, sem, sem, sem, sem, sem]
  | .top => rw [sem, DLB, derLB_top a, sem, complement, complement, sem, sem]; rfl
  | .symbol x => rw [sem, DLB, derLB_symb x a]; simp [sem, complement]
  | .plus r₁ r₂ => rw [DLB, sem, sem, derLB_union a (sem r₁) (sem r₂), union, union, derLB_correct a r₁, derLB_correct a r₂]
  | .intersection r₁ r₂ => rw [DLB, sem, sem, derLB_intersection a (sem r₁) (sem r₂), intersection, intersection, derLB_correct a r₁, derLB_correct a r₂]
  | .complement r₁ r₂ => rw [DLB, sem, sem, derLB_complement a (sem r₁) (sem r₂), complement, complement, derLB_correct a r₁, derLB_correct a r₂]
  | .mult r₁ r₂ =>
    rw [sem, (derLB_concat a (sem r₁) (sem r₂))]
    constructor
    . rintro ⟨x, y, hx, hy, hc⟩; exact ⟨x, y, ((derLB_correct a r₁) x).mp hx, ((derLB_correct a r₂) y).mp hy, hc⟩
    . rintro ⟨x, y, hx, hy, hc⟩; exact ⟨x, y, ((derLB_correct a r₁) x).mpr hx, ((derLB_correct a r₂) y).mpr hy, hc⟩
  | .star r b => exact (derLB_star a (sem r) (sem b) w).trans (star_congr (derLB_correct a r) (derLB_correct a b) w)
  | .lb r =>
    refine (derLB_lb a (sem r) w).trans ?_
    match w with
    | .left _ _ [] _ | .right _ 0 _ _ => exact der_correct a r _
    | .left _ _ (_ :: _) _ | .middle _ _ _ _ | .right _ (_ + 1) _ _ => simp [sem, DLB, lookbehind]
  | .la r => exact derLB_la a (sem r) w
  | .lbStep r =>
    refine (derLB_lbStep a (sem r) w).trans ?_
    match w with
    | .left (_ + 1) _ _ _ | .middle (_ + 1) _ _ _ | .right (_ + 1) _ _ _ => simp [lbStep]; exact derLB_correct a r _
    | .left 0 _ _ _ | .middle 0 _ _ _ | .right 0 _ _ _ => simp [DLB, sem, lbStep]
  | .mStep r => exact derLB_matchStep a (sem r) w
  | .laStep r => exact derLB_LAStep a (sem r) w



/-- Theorem 4.2.1 (lookahead derivative): `⟦D▷_a r⟧ = der▷_a ⟦r⟧`. -/
theorem derLA_correct {α} [DecidableEq α] (a : α) (r : Expr α) : derLA a (sem r) ≐ sem (DLA a r) := by
  intro w
  match r with
  | .empty => rw [DLA, sem, derLA_empty a]
  | .unit => rw [sem, DLA, derLA_unit a, sem, sem]
  | .top => rw [sem, DLA, derLA_top a, sem, sem]
  | .symbol x => rw [sem, DLA, derLA_symb x a, sem, empty]
  | .plus r₁ r₂ => rw [DLA, sem, sem, derLA_union a (sem r₁) (sem r₂), union, union, derLA_correct a r₁, derLA_correct a r₂]
  | .intersection r₁ r₂ => rw [DLA, sem, sem, derLA_intersection a (sem r₁) (sem r₂), intersection, intersection, derLA_correct a r₁, derLA_correct a r₂]
  | .complement r₁ r₂ => rw [DLA, sem, sem, derLA_complement a (sem r₁) (sem r₂), complement, complement, derLA_correct a r₁, derLA_correct a r₂]
  | .mult r₁ r₂ =>
    rw [sem, (derLA_concat a (sem r₁) (sem r₂))]
    constructor
    . rintro ⟨x, y, hx, hy, hc⟩; exact ⟨x, y, ((derLA_correct a r₁) x).mp hx, ((derLA_correct a r₂) y).mp hy, hc⟩
    . rintro ⟨x, y, hx, hy, hc⟩; exact ⟨x, y, ((derLA_correct a r₁) x).mpr hx, ((derLA_correct a r₂) y).mpr hy, hc⟩
  | .star r b => exact (derLA_star a (sem r) (sem b) w).trans (star_congr (derLA_correct a r) (derLA_correct a b) w)
  | .lb r =>
    rw [sem, DLA, sem]
    refine (derLA_lb a (sem r) w).trans ?_
    match w with
    | .left _ _ [] _ | .right _ 0 _ _ => simp only [lookbehind]; exact derLA_correct a r _
    | .left _ _ (_ :: _) _ | .middle _ _ _ _ | .right _ (_ + 1) _ _ => simp [lookbehind]
  | .la r =>
    refine (derLA_la a (sem r) w).trans ?_
    match w with
    | .right _ 0 _ [] | .right _ 0 _ (_ :: _) => simp only [lookahead]; exact der_correct a r _
    | .left _ _ _ _ | .middle _ _ _ _ | .right _ (_ + 1) _ _ => simp [DLA, sem, lookahead]
  | .lbStep r =>
    refine (derLA_lbStep a (sem r) w).trans ?_
    match w with
    | .left (_ + 1) _ _ _ | .middle (_ + 1) _ _ _ | .right (_ + 1) _ _ _ =>
      simp only [lbStep]; exact derLA_correct a r _
    | .left 0 _ _ _ | .middle 0 _ _ _ | .right 0 _ _ _ => simp [DLA, sem, lbStep]
  | .mStep r =>
    refine (derLA_matchStep a (sem r) w).trans ?_
    match w with
    | .middle _ (_ + 1) _ _ | .right _ (_ + 1) _ _ => simp only [matchStep]; exact derLA_correct a r _
    | .left _ _ _ _ | .middle _ 0 _ _ | .right _ 0 _ _ => simp [DLA, sem, matchStep]
  | .laStep r =>
    refine (derLA_laStep a (sem r) w).trans ?_
    match w with
    | .right _ _ (_ + 1) _ => simp only [laStep]; exact derLA_correct a r _
    | .left _ _ _ _ | .middle _ _ _ _ | .right _ _ 0 _ => simp [DLA, sem, laStep]
end


-- Theorem 4.2.2 (iterated derivatives vs `der_word` / `derLA_word`).
theorem der_word_correct {α} [DecidableEq α] (w : List α) (r : Expr α) : (der_word w (sem r)) ≐ (sem (D_word w r)) := by
  induction w generalizing r with
  | nil => intro u; simp [der_word, D_word]
  | cons whd wtl ih =>
    intro u
    simp only [der_word, D_word]
    have hder := der_correct whd r
    have der_word_congr :
        ∀ (tl : List α) (l₁ l₂ : Lang α), l₁ ≐ l₂ → ∀ u : Word α, der_word tl l₁ u ↔ der_word tl l₂ u := by
      intro tl l₁ l₂ h
      induction tl generalizing l₁ l₂ with
      | nil => intro v; exact h v
      | cons y ys ih₂ =>
        intro u'; simp [der_word]
        have : der y l₁ ≐ der y l₂ := by
          intro v
          match v with
          | .middle _ (_ + 1) _ _ | .right _ (_ + 1) 0 _ => exact h _
          | .left _ _ _ _ | .middle _ 0 _ _ | .right _ 0 _ _ | .right _ (_ + 1) (_ + 1) _ => exact Iff.rfl
        exact ih₂ (der y l₁) (der y l₂) this u'
    exact Iff.trans (der_word_congr wtl (der whd (sem r)) (sem (D whd r)) hder u) (ih (D whd r) u)

theorem derLB_word_correct {α} [DecidableEq α] (w : List α) (r : Expr α) :
    (derLB_word w (sem r)) ≐ (sem (DLB_word w r)) := by
  induction w generalizing r with
  | nil => intro u; simp [derLB_word, DLB_word]
  | cons whd wtl ih =>
    intro u
    simp only [derLB_word, DLB_word]
    have hderLB := derLB_correct whd r
    have der_word_congr :
        ∀ (tl : List α) (l₁ l₂ : Lang α), l₁ ≐ l₂ → ∀ u : Word α, derLB_word tl l₁ u ↔ derLB_word tl l₂ u := by
      intro tl l₁ l₂ h
      induction tl generalizing l₁ l₂ with
      | nil => intro v; exact h v
      | cons y ys ih₂ =>
        intro u'; simp [derLB_word]
        have : derLB y l₁ ≐ derLB y l₂ := by
          intro v
          match v with
          | .left (_ + 1) _ _ _ | .middle (_ + 1) 0 _ _ | .right (_ + 1) 0 0 _ => exact h _
          | .left 0 _ _ _ | .middle 0 _ _ _ | .middle (_ + 1) (_ + 1) _ _ | .right 0 _ _ _ | .right (_ + 1) (_ + 1) _ _ | .right (_ + 1) 0 (_ + 1) _ => exact Iff.rfl
        exact ih₂ (derLB y l₁) (derLB y l₂) this u'
    exact Iff.trans (der_word_congr wtl (derLB whd (sem r)) (sem (DLB whd r)) hderLB u) (ih (DLB whd r) u)

theorem derLA_word_correct {α} [DecidableEq α] (w : List α) (r : Expr α) :
    (derLA_word w (sem r)) ≐ (sem (DLA_word w r)) := by
  induction w generalizing r with
  | nil => intro u; simp [derLA_word, DLA_word]
  | cons whd wtl ih =>
    intro u
    simp only [derLA_word, DLA_word]
    have hderLA := derLA_correct whd r
    have derLA_word_congr :
        ∀ (tl : List α) (l₁ l₂ : Lang α), l₁ ≐ l₂ → ∀ u : Word α, derLA_word tl l₁ u ↔ derLA_word tl l₂ u := by
      intro tl l₁ l₂ h
      induction tl generalizing l₁ l₂ with
      | nil => intro v; exact h v
      | cons y ys ih₂ =>
        intro u'
        simp [derLA_word]
        have : derLA y l₁ ≐ derLA y l₂ := by
          intro v
          match v with
          | .right _ _ (_ + 1) _ => exact h _
          | .left _ _ _ _ | .middle _ _ _ _ | .right _ _ 0 _ => exact Iff.rfl
        exact ih₂ (derLA y l₁) (derLA y l₂) this u'
    exact Iff.trans (derLA_word_congr wtl (derLA whd (sem r)) (sem (DLA whd r)) hderLA u) (ih (DLA whd r) u)


/-- Theorem 4.2.3 — correctness of the existential derivative: `⟦xD_w r⟧ = xder_w ⟦r⟧`. -/
theorem xder_correct {α} [DecidableEq α] (s : List α) (r : Expr α) : (xder s (sem r)) ≐ (sem (xD s r) ) := by
  induction s generalizing r with
  | nil => intro w; simp [xder, xD]
  | cons a tl ih =>
    intro w
    have : (derLB a (sem r) ∪ der a (sem r) ∪ derLA a (sem r)) ≐ sem (DLB a r + D a r + DLA a r) := by
      intro u; simp [sem, union, derLB_correct a r u, der_correct a r u, derLA_correct a r u]
    exact (xder_congr tl _ _ this w).trans (ih (DLB a r + D a r + DLA a r) w)

end DerCorrect

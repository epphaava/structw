import Thesis.Semantics.StructuredWords
import Thesis.Semantics.Operators
import Thesis.Semantics.Derivatives

namespace derLBws

open StructuredWords
open Operators

-- Proposition 3.4.1 (Derivative laws for structured languages).

theorem derLB_empty (a : α) : derLB a ∅ ≐ ∅ := by
  intro w
  match w with
  | .left _ _ _ => simp [derLB, empty]
  | .middle mcount _ _ => cases mcount <;> simp [derLB, empty]
  | .right mcount lacount _ => cases mcount <;> cases lacount <;> simp [derLB, empty]

theorem derLB_unit (a : α) : derLB a I ≐ (I - ▹ₗ I) := by
  intro w
  match w with
  | .left _ _ _ => simp [complement, derLB, LAStep, unit]
  | .middle mcount _ _ => cases mcount <;> simp [complement, derLB, LAStep, unit, toList]
  | .right mcount lacount _ => cases mcount <;> cases lacount <;> simp [complement, derLB, LAStep, unit]

theorem derLB_top (a : α) : derLB a T ≐ (T - (▹ₘ T ∪ ▹ₗ T )) := by
  intro w
  match w with
  | .left _ _ _ => simp [union, complement, derLB, matchStep, LAStep, top]
  | .middle mcount _ _ =>
    cases mcount <;> simp [union, complement, derLB, matchStep, LAStep, top]
  | .right mcount lacount _ => cases mcount <;> cases lacount <;> simp [union, complement, derLB, matchStep, LAStep, top]

theorem derLB_symb (a b : α) : derLB b (#a) ≐ (#a - (matchStep #a ∪ LAStep #a)):= by
  intro w
  match w with
  | .left _ _ _ => simp [derLB, complement, union, matchStep, LAStep, symb]
  | .middle mcount (y, ys) _ =>
    cases mcount with
    | zero => cases ys <;> simp [derLB, complement, union, matchStep, LAStep, symb, toList, Eq.comm]
    | succ n => simp [derLB, complement, union, matchStep, LAStep, symb]
  | .right mcount lacount _ => cases mcount <;> cases lacount <;> simp [derLB, complement, union, matchStep, LAStep, symb]

theorem derLB_union (a : α) (k l : Lang α) : derLB a (k ∪ l) ≐ derLB a k ∪ derLB a l := by
  intro w
  match w with
  | .left _ _ _ => simp [derLB, union]
  | .middle mcount _ _ => cases mcount <;> simp [derLB, union]
  | .right mcount lacount _ => cases mcount <;> cases lacount <;> simp [derLB, union]

theorem derLB_intersection (a : α) (k l : Lang α): derLB a (k ∩ l) ≐ (derLB a k) ∩ (derLB a l) := by
  intro w
  match w with
  | .left _ _ _ => simp [intersection, derLB]
  | .middle mcount _ _ => cases mcount <;> simp [intersection, derLB]
  | .right mcount lacount _ => cases mcount <;> cases lacount <;> simp [intersection, derLB]

theorem derLB_complement (a : α) (k l : Lang α): derLB a (k - l) ≐ ((derLB a k) - (derLB a l)) := by
  intro w
  match w with
  | .left _ _ _ => simp [complement, derLB]
  | .middle mcount _ _ => cases mcount <;> simp [complement, derLB]
  | .right mcount lacount _ => cases mcount <;> cases lacount <;> simp [complement, derLB]



theorem derLB_concat (a : α) (k l : Lang α) : derLB a (k • l) ≐ derLB a k • derLB a l := by
  intro w
  match w with
  | .left lb main la =>
    constructor
    . intro h; obtain ⟨w₁, w₂, hk, hl, pref, suff, hmain, _, _⟩ := h; subst w₁ w₂; exact ⟨.left lb pref (suff ++ la), .left (lb.fst, lb.snd ++ pref) suff la, hk, hl, pref, suff, hmain, rfl, rfl⟩
    . intro h; obtain ⟨w₁, w₂, hk, hl, pref, suff, hmain, hw₁, hw₂⟩ := h; subst w₁ w₂; exact ⟨.left (a, toList lb) pref (suff ++ la), .left (a, (toList lb) ++ pref) suff la, hk, hl, pref, suff, hmain, rfl, rfl⟩
  | .middle mcount main la =>
    constructor
    . intro h
      cases mcount with
      | zero =>
        obtain ⟨w₁, w₂, hk, hl, pref, suff, hmain, _, _⟩ := h; subst w₁ w₂;
        cases pref with
        | nil => simp [toList] at hmain; exact ⟨.right 0 0 (suff ++ la), .middle 0 main la, hk, by simp [←hmain] at hl; exact hl, Or.inr ⟨0, 0, rfl, by simp [toList, hmain], rfl⟩⟩
        | cons y ys  => simp [toList] at hmain; exact ⟨.middle 0 (y, ys) (suff ++ la), .left (y, ys) suff la, hk, hl, Or.inl ⟨ys, suff, hmain.2, by simp [hmain], by simp [hmain]⟩⟩
      | succ mcount => simp [derLB] at h
    . intro h
      cases mcount with
      | zero =>
        obtain ⟨w₁, w₂, hk, hl, h⟩ := h;
        cases h with
        | inl h => obtain ⟨pref, suff, hmain, _, _⟩ := h; subst w₁ w₂; exact ⟨.left (a, []) (main.fst :: pref) (suff ++ la), .left (a, main.fst :: pref) suff la, hk, hl, (main.fst :: pref), suff, by simp [toList, hmain], rfl, rfl⟩
        | inr h => obtain ⟨mc₁, mc₂, hmcount, _, _⟩ := h; simp at hmcount; obtain ⟨_, _⟩ := hmcount; subst mc₁ mc₂ w₁ w₂; exact ⟨.left (a, []) [] (toList main ++ la), .left (a, []) (toList main) la, hk, hl, [], (toList main), rfl, rfl, rfl⟩
      | succ mcount =>
        obtain ⟨w₁, w₂, hk, hl, h⟩ := h;
        cases h with
        | inl h => obtain ⟨_, _, _, _, _⟩ := h; subst w₁; simp [derLB] at hk
        | inr h => obtain ⟨mc₁, mc₂, hmcount, _, _⟩ := h; subst w₁ w₂; cases mc₁ <;> cases mc₂ <;> simp [derLB] at hk hl; simp at hmcount
  | .right mcount lacount la =>
      cases mcount with
      | zero =>
        cases lacount with
        | zero =>
          constructor
          . intro ⟨w₁, w₂, hk, hl, pref, suff, hmain, _, _⟩; simp at hmain; obtain ⟨_, _⟩ := hmain; subst pref suff w₁ w₂; exact ⟨.right 0 0 la, .right 0 0 la, hk, hl, 0, 0, rfl, rfl, rfl⟩
          . intro ⟨w₁, w₂, hk, hl, mc₁, mc₂, hmcount, _, _⟩; symm at hmcount; simp [Nat.add_eq_zero_iff] at hmcount; obtain ⟨_, _⟩ := hmcount; subst mc₁ mc₂ w₁ w₂
            exact ⟨.left (a, []) [] la, .left (a, []) [] la, hk, hl, [], [], rfl, rfl, rfl⟩
        | succ lacount => simp [derLB]; intro ⟨w₁, _, hk, _, _, _, _, _, _⟩; subst w₁; simp [derLB] at hk
      | succ mcount =>
        cases lacount with
        | zero => simp [derLB]; intro ⟨w₁, w₂, hk, hl, mc₁, mc₂, hmcount, _, _⟩; subst w₁ w₂; cases mc₁ <;> cases mc₂ <;> simp [derLB] at hk hl hmcount
        | succ lacounct => simp [derLB]; intro ⟨w₁, w₂, hk, hl, mc₁, mc₂, hmcount, _, _⟩; subst w₁ w₂; cases mc₁ <;> cases mc₂ <;> simp [derLB] at hk hl hmcount


theorem derLB_star_left (a : α) (l base : Lang α) : ∀ (x : α) (xs main la : List α),
    star_help base l (.left (a, x :: xs) main la) ↔ star_help (derLB a base) (derLB a l) (.left (x, xs) main la) := by
  intro x xs main la
  constructor
  · suffices key : ∀ w, star_help base l w →
        ∀ x xs main la, w = .left (a, x :: xs) main la →
          star_help (derLB a base) (derLB a l) (.left (x, xs) main la) by
      intro h; exact key _ h x xs main la rfl
    intro _ h
    induction h with
    | inUnit w hunit => intro _ _ _ _ _ ; subst w; exact star_help.inUnit _ hunit
    | inConcat w₁ w₂ w hl _ hwc ih =>
      intro x xs main la _; subst w; obtain ⟨pref, suff, hmain, _, _⟩ := hwc; subst w₁ w₂
      exact star_help.inConcat (.left (x, xs) pref (suff ++ la)) (.left (x, xs ++ pref) suff la) (.left (x, xs) main la) hl (ih x (xs ++ pref) suff la rfl) ⟨pref, suff, hmain, rfl, rfl⟩
  · suffices key : ∀ w, star_help (derLB a base) (derLB a l) w →
        ∀ x xs main la, w = .left (x, xs) main la →
          star_help base l (.left (a, x :: xs) main la) by
      intro h; exact key _ h x xs main la rfl
    intro _ h
    induction h with
    | inUnit w hunit => intro _ _ _ _ _ ; subst w; exact star_help.inUnit _ hunit
    | inConcat w₁ w₂ w hl _ hwc ih =>
      intro x xs main la _; subst w; obtain ⟨pref, suff, hmain, _, _⟩ := hwc; subst w₁ w₂
      exact star_help.inConcat (.left (a, x :: xs) pref (suff ++ la)) (.left (a, x :: (xs ++ pref)) suff la) (.left (a, x :: xs) main la) hl (ih x (xs ++ pref) suff la rfl) ⟨pref, suff, hmain, rfl, rfl⟩

theorem derLB_star_middle (a : α) (l base : Lang α) : ∀ (main : NEList α) (la : List α),
    star_help base l (.left (a, []) (toList main) la) ↔ star_help (derLB a base) (derLB a l) (.middle 0 main la) := by
  intro main la
  constructor
  · suffices key : ∀ w, star_help base l w →
        ∀ (main : NEList α) la, w = .left (a, []) (toList main) la →
          star_help (derLB a base) (derLB a l) (.middle 0 main la) by
      intro h; exact key _ h main la rfl
    intro _ h
    induction h with
    | inUnit w hunit => intro _ _ _; subst w; exact star_help.inUnit _ hunit
    | inConcat w₁ w₂ w hl hstar hwc ih =>
      intro main la _; subst w; obtain ⟨pref, suff, hmain, _, _⟩ := hwc; subst w₁ w₂
      cases pref with
      | nil => exact ih main la (by simp [hmain])
      | cons y ys =>
        simp [toList] at hmain; obtain ⟨hy, hys⟩ := hmain
        exact star_help.inConcat (.middle 0 (y, ys) (suff ++ la)) (.left (y, ys) suff la) (.middle 0 main la) hl ((derLB_star_left a l base y ys suff la).mp hstar) (Or.inl ⟨ys, suff, hys, by simp [hy], by simp [hy]⟩)
  · suffices key : ∀ w, star_help (derLB a base) (derLB a l) w →
        ∀ (main : NEList α) la, w = .middle 0 main la →
          star_help base l (.left (a, []) (toList main) la) by
      intro h; exact key _ h main la rfl
    intro _ h
    induction h with
    | inUnit w hunit => intro _ _ _; subst w; exact star_help.inUnit _ hunit
    | inConcat w₁ w₂ w hl hstar hwc ih =>
      intro main la _; subst w
      cases hwc with
      | inl hwc =>
        obtain ⟨pref, suff, hmain, _, _⟩ := hwc; subst w₁ w₂
        exact star_help.inConcat (.left (a, []) (main.1 :: pref) (suff ++ la))
          (.left (a, main.1 :: pref) suff la) (.left (a, []) (toList main) la)
          hl ((derLB_star_left a l base main.1 pref suff la).mpr hstar)
          ⟨main.1 :: pref, suff, by simp [toList, hmain], rfl, rfl⟩
      | inr hwc =>
        obtain ⟨mc₁, mc₂, hmcount, _, hw₂⟩ := hwc; simp at hmcount; obtain ⟨_, _⟩ := hmcount; subst mc₂
        exact ih main la hw₂

theorem derLB_star_right (a : α) (l base : Lang α) : ∀ (la : List α),
    star_help base l (.left (a, []) [] la) ↔ star_help (derLB a base) (derLB a l) (.right 0 0 la) := by
  intro la
  constructor
  · suffices key : ∀ w, star_help base l w →
        ∀ la, w = .left (a, []) [] la →
          star_help (derLB a base) (derLB a l) (.right 0 0 la) by
      intro h; exact key _ h la rfl
    intro _ h
    induction h with
    | inUnit w hunit => intro _ _; subst w; exact star_help.inUnit _ hunit
    | inConcat w₁ w₂ w hl _ hwc ih =>
      intro la _; subst w; obtain ⟨pref, suff, hmain, _, _⟩ := hwc; subst w₁ w₂
      obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp hmain.symm
      exact star_help.inConcat (.right 0 0 la) (.right 0 0 la) (.right 0 0 la) hl (ih la rfl) ⟨0, 0, rfl, rfl, rfl⟩
  · suffices key : ∀ w, star_help (derLB a base) (derLB a l) w →
        ∀ la, w = .right 0 0 la →
          star_help base l (.left (a, []) [] la) by
      intro h; exact key _ h la rfl
    intro _ h
    induction h with
    | inUnit w hunit => intro _ _; subst w; exact star_help.inUnit _ hunit
    | inConcat w₁ w₂ w hl _ hwc ih =>
      intro la _; subst w; obtain ⟨mc₁, mc₂, hmcount, _, _⟩ := hwc;  subst w₁ w₂
      obtain rfl : mc₁ = 0 := by omega
      obtain rfl : mc₂ = 0 := by omega
      exact star_help.inConcat (.left (a, []) [] la) (.left (a, []) [] la) (.left (a, []) [] la) hl (ih la rfl) ⟨[], [], rfl, rfl, rfl⟩

theorem derLB_star (a : α) (l base : Lang α) : derLB a (star base l) ≐ star (derLB a base) (derLB a l) := by
  intro w
  match w with
  | .left (x, xs) main la => exact derLB_star_left a l base x xs main la
  | .middle mcount main la =>
    cases mcount with
    | zero => exact derLB_star_middle a l base main la
    | succ mcount =>
      simp [derLB]
      intro h
      cases h with
      | inUnit w hunit => simp [derLB] at hunit
      | inConcat w₁ w₂ w hl _ hwc =>
        rcases hwc with ⟨pref, suff, hmain, _, _⟩ | ⟨mc₁, mc₂, hmcount, _, _⟩
        · subst w₁; simp [derLB] at hl
        · subst w₁
          cases mc₁ with
          | zero =>
            cases mc₂ with
            | zero => simp at hmcount
            | succ mc₂ => simp [derLB] at hl
          | succ mc₁ => simp [derLB] at hl
  | .right mcount lacount la =>
    cases mcount with
    | zero =>
      cases lacount with
      | zero => exact derLB_star_right a l base la
      | succ lacount =>
        simp [derLB]
        intro h
        cases h with
        | inUnit w hunit => simp [derLB] at hunit
        | inConcat w₁ w₂ w hl _ hwc => obtain ⟨mc₁, mc₂, hmcount, _, _⟩ := hwc; subst w₁; cases mc₁ <;> simp [derLB] at hl
    | succ mcount =>
      simp [derLB]; intro h
      cases h with
      | inUnit w hunit => simp [derLB] at hunit
      | inConcat w₁ w₂ w hl hsh hwc =>
        obtain ⟨mc₁, mc₂, hmcount, _, _⟩ := hwc; subst w₁
        cases mc₁ with
        | zero =>
          cases lacount with
          | zero => cases mc₂ <;> simp [derLB] at hl <;> simp at hmcount
          | succ lacount => cases mc₂ <;> simp [derLB] at hl
        | succ mc₁ => simp [derLB] at hl



theorem derLB_lb (a : α) (l : Lang α) : derLB a (◁ l) ≐ ◁ (der a l)  := by
  intro w
  match w with
  | .left (x, xs) main la =>
    constructor
    . intro h; cases main <;> cases la <;> obtain ⟨mc, h⟩ := h; exact ⟨mc.succ, h⟩
    . intro h; cases main <;> cases la <;> obtain ⟨mc, h⟩ := h;
      cases mc with
      | zero => simp [der] at h
      | succ mc => exact ⟨mc, h⟩
  | .middle mcount main la  => cases mcount <;> simp [derLB, lookbehind, toList]
  | .right mcount lacount la =>
    cases mcount with
    | zero =>
      cases lacount with
      | zero =>
        cases la <;> simp [derLB, lookbehind]
        constructor
        . intro ⟨mc, h⟩; refine ⟨mc.succ, h⟩
        . intro ⟨mc, h⟩; cases mc with
          | zero => simp [der] at h
          | succ mc => refine ⟨mc, h⟩
      | succ lacount => simp [derLB, lookbehind]
    | succ mcount => cases la <;> simp [derLB, lookbehind]

theorem derLB_la (a : α) (l : Lang α) : derLB a (▷ l) ≐ ∅ := by
  intro w
  match w with
  | .left _ _ _  => simp [derLB, lookahead, empty]
  | .middle mcount _ _  => cases mcount <;> simp [derLB, lookahead, empty]
  | .right mcount lacount la => cases mcount <;> cases lacount <;> cases la <;> simp [derLB, lookahead, empty]

theorem derLB_matchStep (a : α) (l : Lang α) : derLB a (matchStep l) ≐ ∅ := by
  intro w
  match w with
  | .left _ _ _   => simp [derLB, matchStep, empty]
  | .middle mcount _ _  => cases mcount <;> simp [derLB, matchStep, empty]
  | .right mcount lacount _ => cases mcount <;> cases lacount <;> simp [derLB, matchStep, empty]

theorem derLB_LAStep (a : α) (l : Lang α) : derLB a (LAStep l) ≐ ∅  := by
  intro w
  match w with
  | .left _ _ _   => simp [derLB, LAStep, empty]
  | .middle mcount _ _  => cases mcount <;> simp [derLB, LAStep, empty]
  | .right mcount lacount _ => cases lacount <;> cases mcount <;> simp [derLB, LAStep, empty]

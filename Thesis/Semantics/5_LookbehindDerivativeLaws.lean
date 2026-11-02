import Thesis.Semantics.«1_StructuredWords»
import Thesis.Semantics.«2_Operators»
import Thesis.Semantics.«3_Derivatives»

namespace derLBLaws

open StructuredWords
open Operators

-- Proposition 3.4.1 (Derivative laws for structured languages).

theorem derLB_empty (a : α) : derLB a ∅ ≐ ∅ := by
  intro w
  match w with
  | .left lbc _ _ _ => cases lbc <;> simp [derLB, empty]
  | .middle lbc mcount _ _ => cases lbc <;> cases mcount <;> simp [derLB, empty]
  | .right lbc mcount lacount _ => cases lbc <;> cases mcount <;> cases lacount <;> simp [derLB, empty]

theorem derLB_unit (a : α) : derLB a I ≐ (↑₁ I - ↑₃ I) := by
  intro w
  match w with
  | .left lbc _ _ _ => cases lbc <;> simp [complement, derLB, lbStep, laStep, unit]
  | .middle lbc mcount _ _ => cases lbc <;> cases mcount <;> simp [complement, derLB, lbStep, laStep, unit, toList]
  | .right lbc mcount lacount _ => cases lbc <;> cases mcount <;> cases lacount <;> simp [complement, derLB, lbStep, laStep, unit]

theorem derLB_top (a : α) : derLB a T ≐ (↑₁T - (↑₂ T ∪ ↑₃ T )) := by
  intro w
  match w with
  | .left lbc _ _ _ => cases lbc <;> simp [union, complement, derLB, lbStep, matchStep, laStep, top]
  | .middle lbc mcount _ _ => cases lbc <;> cases mcount <;> simp [union, complement, derLB, lbStep, matchStep, laStep, top]
  | .right lbc mcount lacount _ => cases lbc <;> cases mcount <;> cases lacount <;> simp [union, complement, derLB, lbStep, matchStep, laStep, top]

theorem derLB_symb (a b : α) : derLB b (#a) ≐ (↑₁ #a - (↑₂ #a ∪ ↑₃ #a)):= by
  intro w
  match w with
  | .left lbc _ _ _ => cases lbc <;> simp [derLB, complement, union, lbStep, matchStep, laStep, symb]
  | .middle lbc mcount (y, ys) _ =>
    cases lbc <;> cases mcount with
    | zero => cases ys <;> simp [derLB, complement, union, lbStep, matchStep, laStep, symb, toList, Eq.comm]
    | succ n => simp [derLB, complement, union, lbStep, matchStep, laStep, symb]
  | .right lbc mcount lacount _ => cases lbc <;> cases mcount <;> cases lacount <;> simp [derLB, complement, union, lbStep, matchStep, laStep, symb]

theorem derLB_union (a : α) (k l : Lang α) : derLB a (k ∪ l) ≐ derLB a k ∪ derLB a l := by
  intro w
  match w with
  | .left lbc _ _ _ => cases lbc <;> simp [derLB, union]
  | .middle lbc mcount _ _ => cases lbc <;> cases mcount <;> simp [derLB, union]
  | .right lbc mcount lacount _ => cases lbc <;> cases mcount <;> cases lacount <;> simp [derLB, union]

theorem derLB_intersection (a : α) (k l : Lang α): derLB a (k ∩ l) ≐ (derLB a k) ∩ (derLB a l) := by
  intro w
  match w with
  | .left lbc _ _ _ => cases lbc <;> simp [intersection, derLB]
  | .middle lbc mcount _ _ => cases lbc <;> cases mcount <;> simp [intersection, derLB]
  | .right lbc mcount lacount _ => cases lbc <;>cases mcount <;> cases lacount <;> simp [intersection, derLB]

theorem derLB_complement (a : α) (k l : Lang α): derLB a (k - l) ≐ ((derLB a k) - (derLB a l)) := by
  intro w
  match w with
  | .left lbc _ _ _ => cases lbc <;> simp [complement, derLB]
  | .middle lbc mcount _ _ => cases lbc <;> cases mcount <;> simp [complement, derLB]
  | .right lbc mcount lacount _ => cases lbc <;> cases mcount <;> cases lacount <;> simp [complement, derLB]



theorem derLB_concat (a : α) (k l : Lang α) : derLB a (k • l) ≐ derLB a k • derLB a l := by
  intro w
  match w with
  | .left lbcount lb main la =>
    cases lbcount with
    | zero => simp [derLB]; rintro ⟨_, _, hk, _, _, _, _, rfl, _⟩; simp [derLB] at hk
    | succ lbcount =>
      constructor
      . rintro ⟨w₁, w₂, hk, hl, pref, suff, hmain, rfl, rfl⟩; exact ⟨.left lbcount.succ lb pref (suff ++ la), .left lbcount.succ (lb.fst, lb.snd ++ pref) suff la, hk, hl, pref, suff, hmain, rfl, rfl⟩
      . rintro ⟨w₁, w₂, hk, hl, pref, suff, hmain, rfl, rfl⟩; exact ⟨.left lbcount (a, toList lb) pref (suff ++ la), .left lbcount (a, (toList lb) ++ pref) suff la, hk, hl, pref, suff, hmain, rfl, rfl⟩
  | .middle lbcount mcount main la =>
    cases lbcount with
    | zero =>
      simp [derLB]; rintro ⟨_, _, hk, _, ⟨_, _, _, rfl, _⟩ | ⟨_, _, _, rfl, _⟩⟩ <;> simp [derLB] at hk
    | succ lbcount =>
      constructor
      . cases mcount with
        | zero =>
          rintro ⟨_, _, hk, hl, pref, suff, hmain, rfl, rfl⟩
          cases pref with
          | nil => simp [toList] at hmain; exact ⟨.right lbcount.succ 0 0 (suff ++ la), .middle lbcount.succ 0 main la, hk, by simp [←hmain] at hl; exact hl, Or.inr ⟨0, 0, rfl, by simp [toList, hmain], rfl⟩⟩
          | cons y ys  => simp [toList] at hmain; exact ⟨.middle lbcount.succ 0 (y, ys) (suff ++ la), .left lbcount.succ (y, ys) suff la, hk, hl, Or.inl ⟨ys, suff, hmain.2, by simp [hmain], by simp [hmain]⟩⟩
        | succ mcount => simp [derLB]
      . cases mcount with
        | zero =>
          rintro ⟨_ , _, hk, hl, h⟩;
          cases h with
          | inl h => obtain ⟨pref, suff, hmain, rfl, rfl⟩ := h; exact ⟨.left lbcount (a, []) (main.fst :: pref) (suff ++ la), .left lbcount (a, main.fst :: pref) suff la, hk, hl, (main.fst :: pref), suff, by simp [toList, hmain], rfl, rfl⟩
          | inr h => obtain ⟨_ , _, hmcount, rfl, rfl⟩ := h; simp at hmcount; obtain ⟨rfl, rfl⟩ := hmcount; exact ⟨.left lbcount (a, []) [] (toList main ++ la), .left lbcount (a, []) (toList main) la, hk, hl, [], (toList main), rfl, rfl, rfl⟩
        | succ mcount =>
          rintro ⟨w₁, w₂, hk, hl, h⟩
          cases h with
          | inl h => obtain ⟨_, _, _, rfl, _⟩ := h; simp [derLB] at hk
          | inr h => obtain ⟨mc₁, mc₂, hmcount, rfl, rfl⟩ := h; cases mc₁ <;> cases mc₂ <;> simp [derLB] at hk hl; simp at hmcount
  | .right lbcount mcount lacount la =>
    cases lbcount with
    | zero =>
      simp [derLB]; rintro ⟨_, _, hk, _, _, _, _, rfl, _⟩; simp [derLB] at hk
    | succ lbcount =>
      cases mcount with
      | zero =>
        cases lacount with
        | zero =>
          constructor
          . rintro ⟨_, _, hk, hl, pref, suff, hmain, rfl, rfl⟩; simp at hmain; obtain ⟨rfl, rfl⟩ := hmain; exact ⟨.right lbcount.succ 0 0 la, .right lbcount.succ 0 0 la, hk, hl, 0, 0, rfl, rfl, rfl⟩
          . rintro ⟨_, _, hk, hl, mc₁, mc₂, hmcount, rfl, rfl⟩; symm at hmcount; simp [Nat.add_eq_zero_iff] at hmcount; obtain ⟨rfl, rfl⟩ := hmcount
            exact ⟨.left lbcount (a, []) [] la, .left lbcount (a, []) [] la, hk, hl, [], [], rfl, rfl, rfl⟩
        | succ lacount => simp [derLB]; rintro ⟨_, _, hk, _, _, _, _, rfl, _⟩; simp [derLB] at hk
      | succ mcount =>
        cases lacount with
        | zero => simp [derLB]; rintro ⟨_, _, hk, hl, mc₁, mc₂, hmcount, rfl, rfl⟩; cases mc₁ <;> cases mc₂ <;> simp [derLB] at hk hl hmcount
        | succ lacounct => simp [derLB]; rintro ⟨_, _, hk, hl, mc₁, mc₂, hmcount, rfl, rfl⟩; cases mc₁ <;> cases mc₂ <;> simp [derLB] at hk hl hmcount


theorem derLB_star_left (a : α) (l base : Lang α) : ∀ (lbcount : Nat) (x : α) (xs main la : List α),
    star_help l base (.left lbcount (a, x :: xs) main la) ↔ star_help (derLB a l) (derLB a base) (.left lbcount.succ (x, xs) main la) := by
  intro lbcount x xs main la
  constructor
  · suffices key : ∀ w, star_help l base w →
        ∀ lbcount x xs main la, w = .left lbcount (a, x :: xs) main la →
          star_help (derLB a l) (derLB a base) (.left lbcount.succ (x, xs) main la) by
      intro h; exact key _ h lbcount x xs main la rfl
    intro _ h
    induction h with
    | inUnit w hunit => intro _ _ _ _ _ hw; subst hw; exact star_help.inUnit _ hunit
    | inConcat w₁ w₂ w hl _ hwc ih =>
      intro lbc x xs main la hw; subst hw
      obtain ⟨pref, suff, hmain, h₁, h₂⟩ := hwc; subst h₁ h₂
      exact star_help.inConcat (.left lbc.succ (x, xs) pref (suff ++ la)) (.left lbc.succ (x, xs ++ pref) suff la) _
        hl (ih lbc x (xs ++ pref) suff la rfl) ⟨pref, suff, hmain, rfl, rfl⟩
  · suffices key : ∀ w, star_help (derLB a l) (derLB a base) w →
        ∀ lbcount x xs main la, w = .left lbcount.succ (x, xs) main la →
          star_help l base (.left lbcount (a, x :: xs) main la) by
      intro h; exact key _ h lbcount x xs main la rfl
    intro _ h
    induction h with
    | inUnit w hunit => intro _ _ _ _ _ hw; subst hw; exact star_help.inUnit _ hunit
    | inConcat w₁ w₂ w hl _ hwc ih =>
      intro lbc x xs main la hw; subst hw
      obtain ⟨pref, suff, hmain, h₁, h₂⟩ := hwc; subst h₁ h₂
      exact star_help.inConcat (.left lbc (a, x :: xs) pref (suff ++ la)) (.left lbc (a, x :: (xs ++ pref)) suff la) _
        hl (ih lbc x (xs ++ pref) suff la rfl) ⟨pref, suff, hmain, rfl, rfl⟩

theorem derLB_star_middle (a : α) (l base : Lang α) : ∀ (lbcount : Nat) (main : NEList α) (la : List α),
    star_help l base (.left lbcount (a, []) (toList main) la) ↔ star_help (derLB a l) (derLB a base) (.middle lbcount.succ 0 main la) := by
  intro lbcount main la
  constructor
  · suffices key : ∀ w, star_help l base w →
        ∀ lbcount (main : NEList α) la, w = .left lbcount (a, []) (toList main) la →
          star_help (derLB a l) (derLB a base) (.middle lbcount.succ 0 main la) by
      intro h; exact key _ h lbcount main la rfl
    intro _ h
    induction h with
    | inUnit w hunit => intro _ _ _ hw; subst hw; exact star_help.inUnit _ hunit
    | inConcat w₁ w₂ w hl hstar hwc ih =>
      intro lbc main la hw; subst hw
      obtain ⟨pref, suff, hmain, h₁, h₂⟩ := hwc; subst h₁ h₂
      cases pref with
      | nil => exact ih lbc main la (by simp [hmain])
      | cons y ys =>
        simp [toList] at hmain; obtain ⟨hy, hys⟩ := hmain
        exact star_help.inConcat (.middle lbc.succ 0 (y, ys) (suff ++ la)) (.left lbc.succ (y, ys) suff la) _
          hl ((derLB_star_left a l base lbc y ys suff la).mp hstar)
          (Or.inl ⟨ys, suff, hys, by simp [hy], by simp [hy]⟩)
  · suffices key : ∀ w, star_help (derLB a l) (derLB a base) w →
        ∀ lbcount (main : NEList α) la, w = .middle lbcount.succ 0 main la →
          star_help l base (.left lbcount (a, []) (toList main) la) by
      intro h; exact key _ h lbcount main la rfl
    intro _ h
    induction h with
    | inUnit w hunit => intro _ _ _ hw; subst hw; exact star_help.inUnit _ hunit
    | inConcat w₁ w₂ w hl hstar hwc ih =>
      intro lbc main la hw; subst hw
      rcases hwc with ⟨pref, suff, hmain, h₁, h₂⟩ | ⟨mc₁, mc₂, hmcount, _, hw₂⟩
      · subst h₁ h₂
        exact star_help.inConcat (.left lbc (a, []) (main.1 :: pref) (suff ++ la))
          (.left lbc (a, main.1 :: pref) suff la) _
          hl ((derLB_star_left a l base lbc main.1 pref suff la).mpr hstar)
          ⟨main.1 :: pref, suff, by simp [toList, hmain], rfl, rfl⟩
      · obtain ⟨rfl, rfl⟩ : mc₁ = 0 ∧ mc₂ = 0 := by omega
        exact ih lbc main la hw₂

theorem derLB_star_right (a : α) (l base : Lang α) : ∀ (lbcount : Nat) (la : List α),
    star_help l base (.left lbcount (a, []) [] la) ↔ star_help (derLB a l) (derLB a base) (.right lbcount.succ 0 0 la) := by
  intro lbcount la
  constructor
  · suffices key : ∀ w, star_help l base w →
        ∀ lbcount la, w = .left lbcount (a, []) [] la →
          star_help (derLB a l) (derLB a base) (.right lbcount.succ 0 0 la) by
      intro h; exact key _ h lbcount la rfl
    intro _ h
    induction h with
    | inUnit w hunit => intro _ _ hw; subst hw; exact star_help.inUnit _ hunit
    | inConcat w₁ w₂ w hl _ hwc ih =>
      intro lbc la hw; subst hw
      obtain ⟨pref, suff, hmain, h₁, h₂⟩ := hwc; subst h₁ h₂
      obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp hmain.symm
      exact star_help.inConcat (.right lbc.succ 0 0 la) (.right lbc.succ 0 0 la) _ hl (ih lbc la rfl) ⟨0, 0, rfl, rfl, rfl⟩
  · suffices key : ∀ w, star_help (derLB a l) (derLB a base) w →
        ∀ lbcount la, w = .right lbcount.succ 0 0 la →
          star_help l base (.left lbcount (a, []) [] la) by
      intro h; exact key _ h lbcount la rfl
    intro _ h
    induction h with
    | inUnit w hunit => intro _ _ hw; subst hw; exact star_help.inUnit _ hunit
    | inConcat w₁ w₂ w hl _ hwc ih =>
      intro lbc la hw; subst hw
      obtain ⟨mc₁, mc₂, hmcount, h₁, h₂⟩ := hwc
      obtain ⟨rfl, rfl⟩ : mc₁ = 0 ∧ mc₂ = 0 := by omega
      subst h₁
      exact star_help.inConcat (.left lbc (a, []) [] la) (.left lbc (a, []) [] la) _ hl (ih lbc la h₂) ⟨[], [], rfl, rfl, rfl⟩

theorem derLB_star (a : α) (l base : Lang α) : derLB a (star l base) ≐ star (derLB a l) (derLB a base) := by
  intro w
  match w with
  | .left lbcount (x, xs) main la =>
    cases lbcount with
    | zero =>
      simp [derLB]; intro h
      cases h with
      | inUnit w hunit => simp [derLB] at hunit
      | inConcat w₁ w₂ w hl _ hwc => obtain ⟨_, _, _, rfl, _⟩ := hwc; simp [derLB] at hl
    | succ lbcount => exact derLB_star_left a l base lbcount x xs main la
  | .middle lbcount mcount main la =>
    cases lbcount with
    | zero =>
      simp [derLB]; intro h
      cases h with
      | inUnit w hunit => simp [derLB] at hunit
      | inConcat w₁ w₂ w hl _ hwc =>
        rcases hwc with ⟨_, _, _, rfl, _⟩ | ⟨_, _, _, rfl, _⟩ <;> simp [derLB] at hl
    | succ lbcount =>
      cases mcount with
      | zero => exact derLB_star_middle a l base lbcount main la
      | succ mcount =>
        simp [derLB]; intro h
        cases h with
        | inUnit w hunit => simp [derLB] at hunit
        | inConcat w₁ w₂ w hl _ hwc =>
          rcases hwc with ⟨_, _, _, rfl, _⟩ | ⟨mc₁, mc₂, hmcount, rfl, _⟩
          · simp [derLB] at hl
          · cases mc₁ with
            | zero =>
              cases mc₂ with
              | zero => simp at hmcount
              | succ mc₂ => simp [derLB] at hl
            | succ mc₁ => simp [derLB] at hl
  | .right lbcount mcount lacount la =>
    cases lbcount with
    | zero =>
      simp [derLB]; intro h
      cases h with
      | inUnit w hunit => simp [derLB] at hunit
      | inConcat w₁ w₂ w hl _ hwc => obtain ⟨_, _, _, rfl, _⟩ := hwc; simp [derLB] at hl
    | succ lbcount =>
      cases mcount with
      | zero =>
        cases lacount with
        | zero => exact derLB_star_right a l base lbcount la
        | succ lacount =>
          simp [derLB]; intro h
          cases h with
          | inUnit w hunit => simp [derLB] at hunit
          | inConcat w₁ w₂ w hl _ hwc =>
            obtain ⟨mc₁, mc₂, _, rfl, _⟩ := hwc; cases mc₁ <;> simp [derLB] at hl
      | succ mcount =>
        simp [derLB]; intro h
        cases h with
        | inUnit w hunit => simp [derLB] at hunit
        | inConcat w₁ w₂ w hl _ hwc =>
          obtain ⟨mc₁, mc₂, hmcount, rfl, _⟩ := hwc
          cases mc₁ with
          | zero =>
            cases lacount with
            | zero => cases mc₂ <;> simp [derLB] at hl <;> simp at hmcount
            | succ lacount => cases mc₂ <;> simp [derLB] at hl
          | succ mc₁ => simp [derLB] at hl



theorem derLB_lb (a : α) (l : Lang α) : derLB a (◁ l) ≐ ◁ (der a l)  := by
  intro w
  match w with
  | .left lbcount (x, xs) main la => cases lbcount <;> cases main <;> simp [derLB, lookbehind, der]
  | .middle lbcount mcount main la  => cases lbcount <;> cases mcount <;> simp [derLB, lookbehind, toList]
  | .right lbcount mcount lacount la => cases lbcount <;> cases mcount <;> cases lacount <;> cases la <;> simp [derLB, lookbehind, der]

theorem derLB_la (a : α) (l : Lang α) : derLB a (▷ l) ≐ ∅ := by
  intro w
  match w with
  | .left lbcount _ _ _  => cases lbcount <;> simp [derLB, lookahead, empty]
  | .middle lbcount mcount _ _  => cases lbcount <;> cases mcount <;> simp [derLB, lookahead, empty]
  | .right lbcount mcount lacount la => cases lbcount <;> cases mcount <;> cases lacount <;> cases la <;> simp [derLB, lookahead, empty]

theorem derLB_lbStep (a : α) (l : Lang α) : derLB a (↑₁ l) ≐ ↑₁ (derLB a l) := by
  intro w
  match w with
  | .left lbcount _ _ _   => rcases lbcount with _ | _ | _ <;> simp [derLB, lbStep, toList]
  | .middle lbcount mcount _ _  => rcases lbcount with _ | _ | _ <;> cases mcount <;> simp [derLB, lbStep]
  | .right lbcount mcount lacount _ => rcases lbcount with _ | _ | _ <;> cases mcount <;> cases lacount <;> simp [derLB, lbStep]

theorem derLB_matchStep (a : α) (l : Lang α) : derLB a (↑₂ l) ≐ ∅ := by
  intro w
  match w with
  | .left lbcount _ _ _   => cases lbcount <;> simp [derLB, matchStep, empty]
  | .middle lbcount mcount _ _  => cases lbcount <;> cases mcount <;> simp [derLB, matchStep, empty]
  | .right lbcount mcount lacount _ => cases lbcount <;> cases mcount <;> cases lacount <;> simp [derLB, matchStep, empty]

theorem derLB_LAStep (a : α) (l : Lang α) : derLB a (↑₃ l) ≐ ∅  := by
  intro w
  match w with
  | .left lbcount _ _ _   => cases lbcount <;> simp [derLB, laStep, empty]
  | .middle lbcount mcount _ _  => cases lbcount <;> cases mcount <;> simp [derLB, laStep, empty]
  | .right lbcount mcount lacount _ => cases lbcount <;>cases lacount <;> cases mcount <;> simp [derLB, laStep, empty]

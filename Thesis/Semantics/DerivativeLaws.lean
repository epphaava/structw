import Thesis.Semantics.StructuredWords
import Thesis.Semantics.Operators
import Thesis.Semantics.Derivatives
import Thesis.Semantics.AlgebraicLaws
import Thesis.Semantics.LookaheadDerivativeLaws

namespace DerLaws

open StructuredWords
open Operators

-- Proposition 3.4.1 (Derivative laws for structured languages).

-- ======== DER ==========
theorem der_empty (a : α) : der a ∅ ≐ ∅ := by
  intro w
  match w with
  | .left lb main la => simp [der, empty]
  | .middle mcount main la => cases mcount <;> simp [der, empty]
  | .right mcount lacount la => cases mcount <;> cases lacount <;> simp [der, empty]

theorem der_unit (a : α) : der a I ≐ ∅ := by
  intro w
  match w with
  | .left lb main la => simp [der, empty]
  | .middle mcount main la => cases mcount <;> simp [der, unit, empty]
  | .right mcount lacount la => cases mcount <;> cases lacount <;> simp [der, unit, empty]

theorem der_top (a : α): (der a T) ≐ (▹ₘ T // ▹ₗ T) := by
  intro w
  match w with
  | .left lb main la => simp [complement, der, matchStep]
  | .middle mcount main la => cases mcount <;> simp [complement, der, matchStep, LAStep, top]
  | .right mcount lacount la => cases mcount <;> cases lacount <;> simp [complement, der, matchStep, LAStep, top]


theorem der_symb_match (a b: α) (h : a = b) : der b (#a) ≐ (▹ₘ I // ▹ₗ T) := by
  intro w
  match w with
  | .left lb main la => simp [complement, der, matchStep, LAStep]
  | .middle mcount main la => cases mcount <;> simp [complement, der, matchStep, LAStep, symb, unit, toList]
  | .right mcount lacount la =>
    cases mcount with
    | zero => cases lacount <;> simp [complement, der, matchStep, LAStep]
    | succ mcount => cases mcount <;> cases lacount <;> simp [complement, der, matchStep, LAStep, symb, unit, h , top]

theorem der_symb_no_match (a b: α) (h : ¬ (a = b)) : der b (#a) ≐ ∅ := by
  intro w
  match w with
  | .left lb main la => simp [der, empty]
  | .middle mcount main la => cases mcount <;> simp [der, symb, empty, toList]
  | .right mcount lacount la =>
    cases mcount with
    | zero => cases lacount <;> simp [der, empty]
    | succ mcount => cases mcount <;> cases lacount <;> simp [der, symb, empty, h]

theorem der_union (a : α) (k l : Lang α): der a (k ∪ l) ≐ (der a k) ∪ (der a l) := by
  intro w
  match w with
  | .left lb main la => simp [der, union]
  | .middle mcount main la => cases mcount <;> simp [der, union]
  | .right mcount lacount la => cases mcount <;> cases lacount <;> simp [der, union]

theorem der_intersection (a : α) (k l : Lang α): der a (k ∩ l) ≐ (der a k) ∩ (der a l) := by
  intro w
  match w with
  | .left lb main la => simp [der, intersection]
  | .middle mcount main la => cases mcount <;> simp [der, intersection]
  | .right mcount lacount la => cases mcount <;> cases lacount <;> simp [der, intersection]

theorem der_complement (a : α) (k l : Lang α): der a (k // l) ≐ ((der a k) // (der a l)) := by
  intro w
  match w with
  | .left lb main la => simp [der, complement]
  | .middle mcount main la => cases mcount <;> simp [der, complement]
  | .right mcount lacount la => cases mcount <;> cases lacount <;> simp [der, complement]

theorem der_concat (a : α) (k l : Lang α) :
  der a (concat k l) ≐  ((der a k) • (derLB a l)) ∪ ((derLA a k) • (der a l)) := by
  intro w
  match w with
  | .left lb main la =>
    constructor
    . intro h; simp [der] at h
    . intro h
      cases h with
      | inl h => obtain ⟨w₁, _, hk, _, ⟨_, _, _, _, _⟩⟩ := h; subst w₁; simp [der] at hk
      | inr h => obtain ⟨w₁, _, hk, _, ⟨_, _, _, _, _⟩⟩ := h; subst w₁; simp [derLA] at hk
  | .middle mcount main la =>
    constructor
    . intro h
      cases mcount with
      | zero => simp [der] at h
      | succ mcount =>
        obtain ⟨w₁, w₂, hk, hl, h⟩ := h
        cases h with
        | inl h =>
          obtain ⟨pref, suff, hmain, _, _⟩ := h; subst w₁ w₂; left
          cases pref with
          | nil => simp at hmain; subst suff; exact ⟨.right mcount.succ 0 (toList main ++ la), .middle 0 main la, hk, hl, Or.inr ⟨mcount.succ, 0, rfl, rfl, rfl⟩⟩
          | cons u us => simp [toList] at hmain; exact ⟨.middle mcount.succ (u, us) (suff ++ la), .left (u, us) suff la, hk, hl, Or.inl ⟨us, suff, hmain.2, by simp [hmain.1]⟩⟩
        | inr h =>
          obtain ⟨mc₁, mc₂, hmcount, _, _⟩ := h; subst w₁ w₂ mcount; right; exact ⟨.right mc₁ mc₂.succ (toList main ++ la), .middle mc₂.succ main la, hk, hl, Or.inr ⟨mc₁, mc₂.succ, rfl, rfl, rfl⟩⟩
    . intro h
      cases mcount with
      | zero =>
        cases h with
        | inl h =>
          obtain ⟨w₁, _, hk, _, h⟩ := h;
          cases h with
          | inl h => obtain ⟨_, _, _, _, _⟩ := h; subst w₁; simp [der] at hk
          | inr h => obtain ⟨mc₁, _, hmcount, _, _⟩ := h; subst w₁; cases mc₁ <;> simp [der] at hk; simp at hmcount
        | inr h =>
          obtain ⟨w₁, w₂, hk, hl, h⟩ := h
          cases h with
          | inl h => obtain ⟨_, _, _, _, _⟩ := h; subst w₁; simp [derLA] at hk
          | inr h => obtain ⟨mc₁, mc₂, hmcount, _, _⟩ := h; subst w₁ w₂; cases mc₁ <;> cases mc₂ <;> simp [der, derLA] at hk hl <;> simp at hmcount
      | succ mcount =>
        cases h with
        | inl h =>
          obtain ⟨w₁, w₂, hk, hl, h⟩ := h
          cases h with
          | inl h => obtain ⟨pref, suff, hmain, _, _⟩ := h; subst w₁ w₂; exact ⟨.middle mcount (a, main.1 :: pref) (suff ++ la), .left (a, main.1 :: pref) suff la, hk, hl, Or.inl ⟨main.1 :: pref, suff, by simp [toList]; exact hmain, rfl, rfl⟩⟩
          | inr h =>
            obtain ⟨mc₁, mc₂, hmcount, _, _⟩ := h; subst w₁ w₂;
            cases mc₁ with
            | zero => simp [der] at hk
            | succ mc₁ =>
              cases mc₂ <;> simp [derLB, der] at hl hk; simp at hmcount; subst mcount
              exact ⟨.middle mc₁ (a, []) (toList main ++ la), .left (a, []) (toList main) la, hk, hl, Or.inl ⟨[], (toList main), rfl, by simp [toList], rfl⟩⟩
        | inr h =>
          obtain ⟨w₁, w₂, hk, hl, h⟩ := h;
          cases h with
          | inl h => obtain ⟨_, _, h⟩ := h; simp [h, derLA] at hk
          | inr h =>
            obtain ⟨mc₁, mc₂, hmcount, _, _⟩ := h; subst w₁ w₂
            cases mc₂ with
            | zero => simp [der] at hl
            | succ mc₂ => exact ⟨.right mc₁ mc₂ (a :: (toList main) ++ la), .middle mc₂ (a, toList main) la, hk, hl, Or.inr ⟨mc₁, mc₂, by rw [←Nat.add_assoc, Nat.add_one_inj] at hmcount; exact hmcount, rfl, rfl⟩⟩
  | .right mcount lacount la =>
    cases lacount with
    | zero =>
      constructor
      . intro h
        cases mcount with
        | zero => simp [der] at h
        | succ mcount =>
          obtain ⟨w₁, w₂, hk, hl, h⟩ := h;
          cases h with
          | inl h => obtain ⟨pref, suff, hmain, _, _⟩ := h; simp at hmain; obtain ⟨_, _⟩ := hmain; subst w₁ w₂ pref suff; left; exact ⟨.right mcount.succ 0 la, .right 0 0 la, hk, hl, mcount.succ, 0, rfl, rfl, rfl⟩
          | inr h => obtain ⟨mc₁, mc₂, hmcount, _, _⟩ := h; subst w₁ w₂ mcount; right; exact ⟨.right mc₁ mc₂.succ la, .right mc₂.succ 0 la, hk, hl, mc₁, mc₂.succ, rfl, rfl, rfl⟩
      . intro h
        cases mcount with
        | zero =>
          cases h with
          | inl h => obtain ⟨w₁, _, hk, _, mc₁, mc₂, hmcount, _, _⟩ := h; subst w₁; cases mc₁ <;> cases mc₂ <;> simp [der] at hk; simp at hmcount
          | inr h => obtain ⟨_, w₂, _, hl, _, mc₂, hmcount, _, _⟩ := h; subst w₂; cases mc₂ <;> simp [der] at hl; simp at hmcount
        | succ mcount =>
          cases h with
          | inl h =>
            obtain ⟨w₁, w₂, hk, hl, mc₁, mc₂, hmcount, _, _⟩ := h; subst w₁ w₂;
            cases mc₂ with
            | zero => simp at hmcount; subst mc₁; exact ⟨.middle mcount (a, []) la, .left (a, []) [] la, hk, hl, Or.inl ⟨[], [], rfl, rfl, rfl⟩⟩
            | succ mc₂ => simp [der] at hk
          | inr h =>
            obtain ⟨w₁, w₂, hk, hl, mc₁, mc₂, hmcount, _, _⟩ := h; subst w₁ w₂;
            cases mc₂ with
            | zero => simp [derLA] at hk
            | succ mc₂ => rw [←Nat.add_assoc, Nat.add_one_inj] at hmcount; exact ⟨.right mc₁ mc₂ (a :: la), .middle mc₂ (a, []) la, hk, hl, Or.inr ⟨mc₁, mc₂, hmcount.symm, rfl, rfl⟩⟩
    | succ m =>
      constructor
      . simp [der]
      . intro h
        cases h with
        | inl h => obtain ⟨_, w₂, _, hl, _, _, _, _, _⟩ := h; subst w₂; simp [derLB] at hl
        | inr h => obtain ⟨_, w₂, _, hl, _, _, _, _, _⟩ := h; subst w₂; simp [der] at hl

def mk_mcount_word : Nat → List α → List α → Word α
  | n, [], la => .right n 0 la
  | n, x :: xs, la => .middle n (x, xs) la

def mk_word : List α → List α → List α → Word α
  | [], main, la => mk_mcount_word 0 main la
  | x :: xs, main, la => .left (x, xs) main la

theorem wc_mcount_word (p q : Nat) (r la : List α) : wc (.right p q (r ++ la)) (mk_mcount_word q r la) (mk_mcount_word (p + q) r la) := by
  cases r with
  | nil => exact ⟨p, q, rfl, rfl, rfl⟩
  | cons x xs => exact Or.inr ⟨p, q, rfl, rfl, rfl⟩

theorem wc_tail_inv {l : Lang α} {w₁ w₂ : Word α} {mcount : Nat} {main la : List α} :
    derLA a l w₁ → wc w₁ w₂ (mk_mcount_word mcount main la) → ∃ p q, w₁ = .right p q (main ++ la) ∧ w₂ = mk_mcount_word q main la ∧ p + q = mcount := by
  intro hx hwc
  cases main with
  | nil => obtain ⟨p, q, rfl, rfl, rfl⟩ := hwc; exact ⟨p, q, rfl, rfl, rfl⟩
  | cons z zs =>
    rcases hwc with ⟨_, _, _, rfl, _⟩ | ⟨p, q, rfl, rfl, rfl⟩
    · simp [derLA] at hx
    · exact ⟨p, q, rfl, rfl, rfl⟩


theorem der_star_fwd (a : α) (l : Lang α) : ∀ w, (l*) w → ∀ mcount main la, w = .middle mcount (a, main) la →
    (derLA a (l*) • der a l • derLB a (l*)) (mk_mcount_word (mcount.succ) main la) := by
  intro _ h
  induction h with
  | inUnit _ hu => intro _ _ _ rfl; simp [unit] at hu
  | inConcat w₁ w₂ _ hl hstar hwc ih =>
    intro mcount main la rfl
    rcases hwc with ⟨pref, suff, hmain, rfl, rfl⟩ | ⟨mc₁, mc₂, hm, rfl, rfl⟩
    · subst hmain; have := wc_mcount_word 0 (mcount.succ) (pref ++ suff) la
      refine ⟨.right 0 (mcount.succ) (pref ++ suff ++ la), mk_mcount_word (mcount.succ) (pref ++ suff) la,
        star_help.inUnit _ (by simp [unit]), ⟨mk_mcount_word (mcount.succ) pref (suff ++ la), mk_word pref suff la, by cases pref <;> exact hl, ?_, ?_⟩, by simpa [this]⟩
      · cases pref with
        | cons p ps => exact hstar
        | nil => cases suff <;> exact hstar
      · cases pref with
        | cons p ps => exact Or.inl ⟨ps, suff, rfl, rfl, rfl⟩
        | nil =>
          cases suff with
          | nil => exact ⟨mcount.succ, 0, rfl, rfl, rfl⟩
          | cons s ss => exact Or.inr ⟨mcount.succ, 0, rfl, rfl, rfl⟩
    · obtain ⟨w₁, w₂, hw₁, hw₂, hwc⟩ := ih mc₂ main la rfl
      obtain ⟨n, m, rfl, rfl, hmc₂⟩ := wc_tail_inv hw₁ hwc
      cases m with
      | zero => simp [derLA] at hw₁
      | succ m =>
        refine ⟨.right (mc₁ + n) (m.succ) (main ++ la), mk_mcount_word (m.succ) main la, ?_, hw₂, ?_⟩
        · exact star_help.inConcat _ (.right n m (a :: (main ++ la))) _ hl hw₁ ⟨mc₁, n, rfl, by simp [toList]; omega, rfl⟩
        · have := wc_mcount_word (mc₁ + n) (m.succ) main la
          rw [←Nat.add_assoc, Nat.succ_inj] at hmc₂; subst hmc₂ hm; simp [Nat.add_assoc] at this; exact this

theorem der_sub (a : α) {k l : Lang α} (h : k ⊆ l) : der a k ⊆ der a l := by
  intro w hw
  match w with
  | .middle (.succ mc) _ _ => exact h _ hw
  | .right (.succ mc) 0 _ => exact h _ hw

theorem concat_star_sub (l : Lang α) : l • l* ⊆ l* := by
  intro _ ⟨x, y, hx, hy, hwc⟩; exact star_help.inConcat x y _ hx hy hwc

theorem derLA_unit_wc {x y w : Word α} : derLA a I x → wc x y w → w = y := by
  intro hx hwc
  match x, w with
  | .right 0 (q + 1) _, .middle _ _ _ =>
    rcases hwc with ⟨_, _, _, h, _⟩ | ⟨mc₁, mc₂, hm, h, rfl⟩
    · cases h
    · simp at h; obtain ⟨rfl, rfl, _⟩ := h; simp at hm; subst hm; rfl
  | .right 0 (q + 1) _, .right _ _ _ =>
    obtain ⟨mc₁, mc₂, hm, h, rfl⟩ := hwc; simp at h; obtain ⟨rfl, _, _⟩ := h; simp at hm; subst hm; rfl
  | .right (_ + 1) lac _, _ => cases lac <;> simp [derLA, unit] at hx
  | .right 0 0 _, _ => simp [derLA] at hx
  | .left _ _ _, _ => simp [derLA] at hx
  | .middle _ _ _, _ => simp [derLA] at hx
  | .right 0 (q + 1) _, .left _ _ _ => obtain ⟨_, _, _, h, _⟩ := hwc; cases h

theorem der_star_bwd (a : α) (l : Lang α) :
    derLA a (l*) • der a l • derLB a (l*) ⊆ der a (l*) := by
  intro w ⟨x, y, hx, hy, hwc⟩
  have : der a l • derLB a (l*) ⊆ der a (l*) := by intro y hy; exact der_sub a ((concat_star_sub) l) y ((DerLaws.der_concat a l (l*) y).mpr (Or.inl hy))
  rw [DerLaws.derLA_star] at hx
  induction hx generalizing w with
  | inUnit x hu => rw [derLA_unit_wc hu hwc]; exact this y hy
  | inConcat x₁ x₂ x hl _ hwc₁ ih =>
    have := (AlgebraicLaws.concat_assoc (· = x₁) (· = x₂) (· = y) w).mpr ⟨x, y, ⟨x₁, x₂, rfl, rfl, hwc₁⟩, rfl, hwc⟩
    obtain ⟨x₁', w', h₁, ⟨x₂', y', h₂, h₃, hwc₂⟩, hwc₃⟩ := (AlgebraicLaws.concat_assoc (· = x₁) (· = x₂) (· = y) w).mpr ⟨x, y, ⟨x₁, x₂, rfl, rfl, hwc₁⟩, rfl, hwc⟩
    subst x₁' x₂' y'
    exact der_sub a (concat_star_sub l) w ((DerLaws.der_concat a l (l*) w).mpr (Or.inr ⟨x₁, w', hl, ih w' hwc₂, hwc₃⟩))

theorem der_star (a : α) (l : Lang α) : der a (l*) ≐ derLA a (l*) • der a l • derLB a (l*):= by
  intro w
  constructor
  . intro h
    match w with
    | .middle (.succ mcount) (y, ys) la =>
      exact der_star_fwd a l _ h mcount (y :: ys) la rfl
    | .right (.succ mcount) 0 la => exact der_star_fwd a l _ h mcount [] la rfl
  · intro h; exact der_star_bwd a l w h


theorem der_lb (a : α) (l : Lang α) : der a (◁ l) ≐ ∅  := by
  intro w
  match w with
  | .left lb main la => simp [der, empty]
  | .middle mcount main la => cases mcount <;> simp [der, lookbehind, empty]
  | .right mcount lacount la => cases mcount <;> cases lacount <;> simp [der, lookbehind, empty]

theorem der_la (a : α) (l : Lang α) : der a (▷ l) ≐ ∅  := by
  intro w
  match w with
  | .left lb main la => simp [der, empty]
  | .middle mcount main la => cases mcount <;> simp [der, empty, lookahead]
  | .right mcount lacount la => cases mcount <;> cases lacount <;> simp [der, lookahead, empty]

theorem der_matchStep (a : α) (l : Lang α) : der a (matchStep l) ≐ matchStep (der a l) := by
  intro w
  match w with
  | .left lb main la => simp [der, matchStep]
  | .middle mcount main la =>
    cases mcount with
    | zero => simp [der, matchStep]
    | succ mcount => cases mcount <;> simp [der, matchStep]
  | .right mcount lacount la =>
    cases mcount with
    | zero => simp [der, matchStep]
    | succ mcount => cases mcount <;> cases lacount <;> simp [der, matchStep]

theorem der_LAStep (a : α) (l : Lang α) : der a (LAStep l) ≐ ∅ := by
  intro w
  match w with
  | .left lb main la => simp [der, empty]
  | .middle mcount main la => cases mcount <;> simp [der, LAStep, empty]
  | .right mcount lacount la => cases mcount <;> cases lacount <;> simp [der, LAStep, empty]

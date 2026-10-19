import Thesis.Semantics.«1_StructuredWords»
import Thesis.Semantics.«2_Operators»
import Thesis.Semantics.«3_Derivatives»
import Thesis.Semantics.«8_AlgebraicLaws»
import Thesis.Semantics.«6_LookaheadDerivativeLaws»
import Thesis.Semantics.«5_LookbehindDerivativeLaws»


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

theorem der_top (a : α): (der a T) ≐ (▹ₘ T - ▹ₗ T) := by
  intro w
  match w with
  | .left lb main la => simp [complement, der, matchStep]
  | .middle mcount main la => cases mcount <;> simp [complement, der, matchStep, LAStep, top]
  | .right mcount lacount la => cases mcount <;> cases lacount <;> simp [complement, der, matchStep, LAStep, top]


theorem der_symb_match (a b: α) (h : a = b) : der b (#a) ≐ (▹ₘ I - ▹ₗ T) := by
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

theorem der_complement (a : α) (k l : Lang α): der a (k - l) ≐ ((der a k) - (der a l)) := by
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


theorem der_mono (a : α) {k l : Lang α} (h : ∀ w, k w → l w) : ∀ w, der a k w → der a l w := by
  intro w hw
  match w with
  | .left _ _ _ => simp [der] at hw
  | .middle mcount _ _ =>
    cases mcount with
    | zero => simp [der] at hw
    | succ _ => exact h _ hw
  | .right mcount lacount _ =>
    cases mcount with
    | zero => simp [der] at hw
    | succ _ =>
      cases lacount with
      | zero => exact h _ hw
      | succ _ => simp [der] at hw

theorem derLA_mono (a : α) {k l : Lang α} (h : ∀ w, k w → l w) : ∀ w, derLA a k w → derLA a l w := by
  intro w hw
  match w with
  | .left _ _ _ => simp [derLA] at hw
  | .middle _ _ _ => simp [derLA] at hw
  | .right _ lacount _ =>
    cases lacount with
    | zero => simp [derLA] at hw
    | succ _ => exact h _ hw

theorem derLB_mono (a : α) {k l : Lang α} (h : ∀ w, k w → l w) : ∀ w, derLB a k w → derLB a l w := by
  intro w hw
  match w with
  | .left _ _ _ => exact h _ hw
  | .middle mcount _ _ =>
    cases mcount with
    | zero => exact h _ hw
    | succ _ => simp [derLB] at hw
  | .right lacount mcount _ =>
    cases lacount with
    | zero =>
      cases mcount with
      | zero => exact h _ hw
      | succ _ => simp [derLB] at hw
    | succ lacount => simp [derLB] at hw

theorem der_helper (a : α) (k : Lang α) : ∀ w, der a k w → ∃ w', k w' ∧ ∀ l : Lang α, l w' → der a l w := by
  intro w hw
  match w with
  | .left _ _ _ => simp [der] at hw
  | .middle mcount _ _ =>
    cases mcount with
    | zero => simp [der] at hw
    | succ mcount => exact ⟨_, hw, fun _ h => h⟩
  | .right mcount lacount _ =>
    cases mcount with
    | zero => simp [der] at hw
    | succ _ =>
      cases lacount with
      | zero => exact ⟨_, hw, fun _ h => h⟩
      | succ _ => simp [der] at hw

theorem der_star_base (a : α) (l base : Lang α) : der a (star base l) ≐ star ((der a base) ∪ ((der a l) • star (derLB a base) (derLB a l))) (derLA a l) := by
  intro w
  constructor
  · intro h
    obtain ⟨w', hw', hd⟩ := der_helper a _ w h
    clear h
    induction hw' generalizing w with
    | inUnit w' hb => exact star_help.inUnit _ (.inl (hd _ hb))
    | inConcat w₁ w₂ w' hl hstar hwc ih =>
      have hc : der a ((· = w₁) • (· = w₂)) w := hd _ ⟨w₁, w₂, rfl, rfl, hwc⟩
      rcases (DerLaws.der_concat a _ _ w).mp hc with ⟨u, v, hu, hv, huv⟩ | ⟨u, v, hu, hv, huv⟩
      · have hu' := der_mono a (fun x hx => hx ▸ hl) u hu
        have hv' := (derLBws.derLB_star a l base v).mp (derLB_mono a (fun x hx => hx ▸ hstar) v hv)
        exact star_help.inUnit _ (Or.inr ⟨u, v, hu', hv', huv⟩)
      · exact star_help.inConcat u v w (derLA_mono a (fun x hx => hx ▸ hl) u hu) (ih v (fun _ h => der_mono a (fun x hx => hx ▸ h) v hv)) huv
  · intro h
    have hsub : ∀ v, (l • star base l) v → star base l v :=
      fun v ⟨x, y, hx, hy, hxy⟩ => star_help.inConcat x y v hx hy hxy
    induction h with
    | inUnit w hx =>
      rcases hx with hb | ⟨u, v, hu, hv, huv⟩
      · exact der_mono a (fun v hv => star_help.inUnit v hv) w hb
      · have hv' := (derLBws.derLB_star a l base v).mpr hv
        exact der_mono a hsub w ((DerLaws.der_concat a l (star base l) w).mpr (Or.inl ⟨u, v, hu, hv', huv⟩))
    | inConcat u v w hu _ huv ih =>
      exact der_mono a hsub w ((DerLaws.der_concat a l (star base l) w).mpr (Or.inr ⟨u, v, hu, ih, huv⟩))

theorem concat_mono {k k' l l' : Lang α} (hk : ∀ v, k v → k' v) (hl : ∀ v, l v → l' v) : ∀ w, (k • l) w → (k' • l') w := by
  intro _ ⟨x, y, hx, hy, hxy⟩; exact ⟨x, y, hk x hx, hl y hy, hxy⟩

theorem star_unit_concat (base l : Lang α) : star base l ≐ star I l • base := by
  intro w
  constructor
  · intro h
    induction h with
    | inUnit w hb => exact concat_mono (fun v hv => star_help.inUnit v hv) (fun _ h => h) w ((AlgebraicLaws.concat_left_identity base w).mpr hb)
    | inConcat u v w hu _ huv ih =>
      have h1 : (l • (star I l • base)) w := ⟨u, v, hu, ih, huv⟩
      exact concat_mono (fun x ⟨p, q, hp, hq, hpq⟩ => star_help.inConcat p q x hp hq hpq) (fun _ h => h) w ((AlgebraicLaws.concat_assoc l (star I l) base w).mp h1)
  · intro ⟨u, v, hu, hv, huv⟩
    suffices key : ∀ u, star I l u → ∀ w, ((· = u) • base) w → star base l w from
      key u hu w ⟨u, v, rfl, hv, huv⟩
    intro u hu
    induction hu with
    | inUnit u hI =>
      intro w hw
      exact star_help.inUnit w ((AlgebraicLaws.concat_left_identity base w).mp (concat_mono (fun x hx => hx ▸ hI) (fun _ h => h) w hw))
    | inConcat u₁ u₂ u hu₁ _ hwc ih =>
      intro w hw
      have h1 : (((· = u₁) • (· = u₂)) • base) w := concat_mono (fun x hx => hx ▸ ⟨u₁, u₂, rfl, rfl, hwc⟩) (fun _ h => h) w hw
      obtain ⟨p, q, rfl, hq, hpq⟩ := (AlgebraicLaws.concat_assoc _ _ _ w).mpr h1
      exact star_help.inConcat p q w hu₁ (ih q hq) hpq

theorem der_star (a : α) (l base : Lang α) : der a (star base l) ≐ star I (derLA a l) • ((der a base) ∪ ((der a l) • star (derLB a base) (derLB a l))) := by
  intro w; exact (der_star_base a l base w).trans (star_unit_concat _ _ w)

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

import Thesis.Semantics.«1_StructuredWords»
import Thesis.Semantics.«2_Operators»
import Thesis.Semantics.«3_Derivatives»
import Thesis.Semantics.«8_AlgebraicLaws»
import Thesis.Semantics.«6_LookaheadDerivativeLaws»
import Thesis.Semantics.«5_LookbehindDerivativeLaws»


namespace DerLaws

open StructuredWords
open Operators
open derLBLaws
open derLALaws

-- Proposition 3.4.1 (Derivative laws for structured languages).

-- ======== DER ==========
theorem der_empty (a : α) : der a ∅ ≐ ∅ := by
  intro w
  match w with
  | .left _ _ _ => simp [der, empty]
  | .middle mcount _ _ => cases mcount <;> simp [der, empty]
  | .right mcount lacount _ => cases mcount <;> cases lacount <;> simp [der, empty]

theorem der_unit (a : α) : der a I ≐ ∅ := by
  intro w
  match w with
  | .left _ _ _ => simp [der, empty]
  | .middle mcount _ _ => cases mcount <;> simp [der, unit, empty]
  | .right mcount lacount _ => cases mcount <;> cases lacount <;> simp [der, unit, empty]

theorem der_top (a : α): (der a T) ≐ (↑₂ T - ↑₃ T) := by
  intro w
  match w with
  | .left _ _ _ => simp [complement, der, matchStep]
  | .middle mcount _ _ => cases mcount <;> simp [complement, der, matchStep, laStep, top]
  | .right mcount lacount _ => cases mcount <;> cases lacount <;> simp [complement, der, matchStep, laStep, top]


theorem der_symb_match (a b: α) (h : a = b) : der b (#a) ≐ (↑₂ I - ↑₃ T) := by
  intro w
  match w with
  | .left _ _ _ => simp [complement, der, matchStep, laStep]
  | .middle mcount _ _ => cases mcount <;> simp [complement, der, matchStep, laStep, symb, unit, toList]
  | .right mcount lacount _ =>
    cases mcount with
    | zero => cases lacount <;> simp [complement, der, matchStep, laStep]
    | succ mcount => cases mcount <;> cases lacount <;> simp [complement, der, matchStep, laStep, symb, unit, h, top]

theorem der_symb_no_match (a b: α) (h : ¬ (a = b)) : der b (#a) ≐ ∅ := by
  intro w
  match w with
  | .left _ _ _ => simp [der, empty]
  | .middle mcount _ _ => cases mcount <;> simp [der, symb, empty, toList]
  | .right mcount lacount _ =>
    cases mcount with
    | zero => cases lacount <;> simp [der, empty]
    | succ mcount => cases mcount <;> cases lacount <;> simp [der, symb, empty, h]

theorem der_union (a : α) (k l : Lang α): der a (k ∪ l) ≐ (der a k) ∪ (der a l) := by
  intro w
  match w with
  | .left _ _ _ => simp [der, union]
  | .middle mcount _ _ => cases mcount <;> simp [der, union]
  | .right mcount lacount _ => cases mcount <;> cases lacount <;> simp [der, union]

theorem der_intersection (a : α) (k l : Lang α): der a (k ∩ l) ≐ (der a k) ∩ (der a l) := by
  intro w
  match w with
  | .left _ _ _ => simp [der, intersection]
  | .middle mcount _ _ => cases mcount <;> simp [der, intersection]
  | .right mcount lacount _ => cases mcount <;> cases lacount <;> simp [der, intersection]

theorem der_complement (a : α) (k l : Lang α): der a (k - l) ≐ ((der a k) - (der a l)) := by
  intro w
  match w with
  | .left _ _ _ => simp [der, complement]
  | .middle mcount _ _ => cases mcount <;> simp [der, complement]
  | .right mcount lacount _ => cases mcount <;> cases lacount <;> simp [der, complement]

theorem der_concat (a : α) (k l : Lang α) :
  der a (concat k l) ≐  ((der a k) • (derLB a l)) ∪ ((derLA a k) • (der a l)) := by
  intro w
  match w with
  | .left _ _ _ =>
    constructor
    . simp [der]
    . rintro (⟨_, _, hk, _, _, _, _, rfl, _⟩ | ⟨_, _, hk, _, _, _, _, rfl, _⟩)
      · simp [der] at hk
      · simp [derLA] at hk
  | .middle mcount main la =>
    constructor
    . cases mcount with
      | zero => simp [der]
      | succ mc =>
        rintro ⟨w₁, w₂, hk, hl, h⟩
        rcases h with ⟨pref, suff, hmain, rfl, rfl⟩ | ⟨mc₁, mc₂, hmcount, rfl, rfl⟩
        · left; cases pref with
          | nil =>
            simp at hmain; subst suff
            exact ⟨.right mc.succ 0 (toList main ++ la), .middle 0 main la, hk, hl, Or.inr ⟨mc.succ, 0, rfl, rfl, rfl⟩⟩
          | cons u us =>
            simp [toList] at hmain
            exact ⟨.middle mc.succ (u, us) (suff ++ la), .left (u, us) suff la, hk, hl, Or.inl ⟨us, suff, hmain.2, by simp [hmain.1], by simp [hmain.1]⟩⟩
        · exact Or.inr ⟨.right mc₁ mc₂.succ (toList main ++ la), .middle mc₂.succ main la, hk, hl, Or.inr ⟨mc₁, mc₂.succ, by omega, rfl, rfl⟩⟩
    . intro h
      cases mcount with
      | zero =>
        rcases h with ⟨w₁, w₂, hk, hl, h⟩ | ⟨w₁, w₂, hk, hl, h⟩
        · rcases h with ⟨_, _, _, rfl, _⟩ | ⟨mc₁, mc₂, hmcount, rfl, _⟩
          · simp [der] at hk
          · obtain ⟨rfl, rfl⟩ : mc₁ = 0 ∧ mc₂ = 0 := by omega
            simp [der] at hk
        · rcases h with ⟨_, _, _, rfl, _⟩ | ⟨mc₁, mc₂, hmcount, _, rfl⟩
          · simp [derLA] at hk
          · obtain ⟨rfl, rfl⟩ : mc₁ = 0 ∧ mc₂ = 0 := by omega
            simp [der] at hl
      | succ mc =>
        rcases h with ⟨w₁, w₂, hk, hl, h⟩ | ⟨w₁, w₂, hk, hl, h⟩
        · rcases h with ⟨pref, suff, hmain, rfl, rfl⟩ | ⟨mc₁, mc₂, hmcount, rfl, rfl⟩
          · exact ⟨.middle mc (a, main.1 :: pref) (suff ++ la), .left (a, main.1 :: pref) suff la, hk, hl,
              Or.inl ⟨main.1 :: pref, suff, by simp [toList, hmain], rfl, rfl⟩⟩
          · cases mc₁ with
            | zero => simp [der] at hk
            | succ mc₁ =>
              cases mc₂ with
              | succ mc₂ => simp [der] at hk
              | zero =>
                obtain rfl : mc₁ = mc := by omega
                exact ⟨.middle mc₁ (a, []) (toList main ++ la), .left (a, []) (toList main) la, hk, hl, Or.inl ⟨[], toList main, rfl, rfl, rfl⟩⟩
        · rcases h with ⟨_, _, _, rfl, _⟩ | ⟨mc₁, mc₂, hmcount, h₁, h₂⟩
          · simp [derLA] at hk
          · subst h₁ h₂
            cases mc₂ with
            | zero => simp [der] at hl
            | succ mc₂ => exact ⟨.right mc₁ mc₂ (a :: toList main ++ la), .middle mc₂ (a, toList main) la, hk, hl, Or.inr ⟨mc₁, mc₂, by omega, rfl, rfl⟩⟩
  | .right mcount lacount la =>
    cases lacount with
    | zero =>
      constructor
      . cases mcount with
        | zero => simp [der]
        | succ mc =>
          rintro ⟨w₁, w₂, hk, hl, h⟩
          rcases h with ⟨pref, suff, hmain, rfl, rfl⟩ | ⟨mc₁, mc₂, hmcount, rfl, rfl⟩
          · obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp hmain.symm; exact Or.inl ⟨.right mc.succ 0 la, .right 0 0 la, hk, hl, mc.succ, 0, rfl, rfl, rfl⟩
          · exact Or.inr ⟨.right mc₁ mc₂.succ la, .right mc₂.succ 0 la, hk, hl, mc₁, mc₂.succ, by omega, rfl, rfl⟩
      . intro h
        cases mcount with
        | zero =>
          rcases h with ⟨_, _, hk, _, mc₁, mc₂, hmcount, rfl, _⟩ | ⟨_, _, _, hl, mc₁, mc₂, hmcount, _, rfl⟩
          · obtain ⟨rfl, rfl⟩ : mc₁ = 0 ∧ mc₂ = 0 := by omega
            simp [der] at hk
          · obtain ⟨rfl, rfl⟩ : mc₁ = 0 ∧ mc₂ = 0 := by omega
            simp [der] at hl
        | succ mc =>
          rcases h with ⟨w₁, w₂, hk, hl, mc₁, mc₂, hmcount, rfl, rfl⟩ | ⟨w₁, w₂, hk, hl, mc₁, mc₂, hmcount, rfl, rfl⟩
          · cases mc₁ with
            | zero => simp [der] at hk
            | succ mc₁ =>
              cases mc₂ with
              | succ mc₂ => simp [der] at hk
              | zero =>
                obtain rfl : mc₁ = mc := by omega
                exact ⟨.middle mc₁ (a, []) la, .left (a, []) [] la, hk, hl, Or.inl ⟨[], [], rfl, rfl, rfl⟩⟩
          · cases mc₂ with
            | zero => simp [der] at hl
            | succ mc₂ => exact ⟨.right mc₁ mc₂ (a :: la), .middle mc₂ (a, []) la, hk, hl, Or.inr ⟨mc₁, mc₂, by omega, rfl, rfl⟩⟩
    | succ m =>
      constructor
      . cases mcount <;> simp [der]
      . rintro (⟨_, _, hk, _, mc₁, mc₂, _, rfl, _⟩ | ⟨_, _, _, hl, mc₁, mc₂, _, _, rfl⟩)
        · cases mc₁ <;> simp [der] at hk
        · cases mc₂ <;> simp [der] at hl


theorem der_mono (a : α) {k l : Lang α} (h : ∀ w, k w → l w) : ∀ w, der a k w → der a l w := by
  intro w hw
  match w with
  | .left _ _ _ => simp [der] at hw
  | .middle mcount _ _ => cases mcount <;> first | exact h _ hw | simp [der] at hw
  | .right mcount lacount _ => cases mcount <;> cases lacount <;> first | exact h _ hw | simp [der] at hw

theorem derLA_mono (a : α) {k l : Lang α} (h : ∀ w, k w → l w) : ∀ w, derLA a k w → derLA a l w := by
  intro w hw
  match w with
  | .left _ _ _ => simp [derLA] at hw
  | .middle _ _ _ => simp [derLA] at hw
  | .right _ lacount _ => cases lacount <;> first | exact h _ hw | simp [derLA] at hw

theorem derLB_mono (a : α) {k l : Lang α} (h : ∀ w, k w → l w) : ∀ w, derLB a k w → derLB a l w := by
  intro w hw
  match w with
  | .left _ _ _ => first | exact h _ hw | simp [derLB] at hw
  | .middle mcount _ _ => cases mcount <;> first | exact h _ hw | simp [derLB] at hw
  | .right mcount lacount _ => cases mcount <;> cases lacount <;> first | exact h _ hw | simp [derLB] at hw

theorem der_helper (a : α) (k : Lang α) : ∀ w, der a k w → ∃ w', k w' ∧ ∀ l : Lang α, l w' → der a l w := by
  intro w hw
  match w with
  | .left _ _ _ => simp [der] at hw
  | .middle mcount _ _ => cases mcount <;> first | exact ⟨_, hw, fun _ h => h⟩ | simp [der] at hw
  | .right mcount lacount _ => cases mcount <;> cases lacount <;> first | exact ⟨_, hw, fun _ h => h⟩ | simp [der] at hw

theorem der_star_base (a : α) (l base : Lang α) : der a (star l base) ≐ star (derLA a l) ((der a base) ∪ ((der a l) • star (derLB a l) (derLB a base))) := by
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
        have hv' := (derLB_star a l base v).mp (derLB_mono a (fun x hx => hx ▸ hstar) v hv)
        exact star_help.inUnit _ (Or.inr ⟨u, v, hu', hv', huv⟩)
      · exact star_help.inConcat u v w (derLA_mono a (fun x hx => hx ▸ hl) u hu) (ih v (fun _ h => der_mono a (fun x hx => hx ▸ h) v hv)) huv
  · intro h
    have hsub : ∀ v, (l • star l base) v → star l base v :=
      fun v ⟨x, y, hx, hy, hxy⟩ => star_help.inConcat x y v hx hy hxy
    induction h with
    | inUnit w hx =>
      rcases hx with hb | ⟨u, v, hu, hv, huv⟩
      · exact der_mono a (fun v hv => star_help.inUnit v hv) w hb
      · have hv' := (derLB_star a l base v).mpr hv
        exact der_mono a hsub w ((DerLaws.der_concat a l (star l base) w).mpr (Or.inl ⟨u, v, hu, hv', huv⟩))
    | inConcat u v w hu _ huv ih =>
      exact der_mono a hsub w ((DerLaws.der_concat a l (star l base) w).mpr (Or.inr ⟨u, v, hu, ih, huv⟩))

theorem concat_mono {k k' l l' : Lang α} (hk : ∀ v, k v → k' v) (hl : ∀ v, l v → l' v) : ∀ w, (k • l) w → (k' • l') w := by
  intro _ ⟨x, y, hx, hy, hxy⟩; exact ⟨x, y, hk x hx, hl y hy, hxy⟩

theorem star_unit_concat (base l : Lang α) : star l base ≐ star l I • base := by
  intro w
  constructor
  · intro h
    induction h with
    | inUnit w hb => exact concat_mono (fun v hv => star_help.inUnit v hv) (fun _ h => h) w ((AlgebraicLaws.concat_left_identity base w).mpr hb)
    | inConcat u v w hu _ huv ih =>
      have h1 : (l • (star l I • base)) w := ⟨u, v, hu, ih, huv⟩
      exact concat_mono (fun x ⟨p, q, hp, hq, hpq⟩ => star_help.inConcat p q x hp hq hpq) (fun _ h => h) w ((AlgebraicLaws.concat_assoc l (star l I) base w).mp h1)
  · intro ⟨u, v, hu, hv, huv⟩
    suffices key : ∀ u, star l I u → ∀ w, ((· = u) • base) w → star l base w from
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

theorem der_star (a : α) (l base : Lang α) : der a (star l base) ≐ star (derLA a l) I • ((der a base) ∪ ((der a l) • star (derLB a l) (derLB a base))) := by
  intro w; exact (der_star_base a l base w).trans (star_unit_concat _ _ w)

theorem der_lb (a : α) (l : Lang α) : der a (◁ l) ≐ ∅  := by
  intro w
  match w with
  | .left _ _ _ => simp [der, empty]
  | .middle mcount _ _ => cases mcount <;> simp [der, lookbehind, empty]
  | .right mcount lacount _ => cases mcount <;> cases lacount <;> simp [der, lookbehind, empty]

theorem der_la (a : α) (l : Lang α) : der a (▷ l) ≐ ∅  := by
  intro w
  match w with
  | .left _ _ _ => simp [der, empty]
  | .middle mcount _ _ => cases mcount <;> simp [der, empty, lookahead]
  | .right mcount lacount _ => cases mcount <;> cases lacount <;> simp [der, lookahead, empty]

theorem der_matchStep (a : α) (l : Lang α) : der a (↑₂ l) ≐ ↑₂ (der a l) := by
  intro w
  match w with
  | .left _ _ _ => simp [der, matchStep]
  | .middle mcount _ _ => rcases mcount with _ | _ | _ <;> simp [der, matchStep]
  | .right mcount lacount _ => rcases mcount with _ | _ | _ <;> cases lacount <;> simp [der, matchStep]

theorem der_laStep (a : α) (l : Lang α) : der a (↑₃ l) ≐ ∅ := by
  intro w
  match w with
  | .left _ _ _ => simp [der, empty]
  | .middle mcount _ _ => cases mcount <;> simp [der, laStep, empty]
  | .right mcount lacount _ => cases mcount <;> cases lacount <;> simp [der, laStep, empty]

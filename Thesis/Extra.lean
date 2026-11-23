import Thesis.Semantics.kLang.«1_StructuredWords»
import Thesis.Semantics.kLang.«2_Operators»
import Thesis.Semantics.kLang.«3_Derivatives»

-- Results not numbered in the thesis: extra laws and experiments.


open StructuredWords
open Operators

-- ▷(K \ L) = ▷K \ ▷L
theorem la_complement_distribut (k l : Lang α) : ▷ (k - l) ≐ (▷ k - ▷ l) := by
  intro w
  match w with
  | .left lbc lb main la => cases main <;> simp [lookahead, complement]
  | .middle lbc mc (hd, tl) la => simp [lookahead, complement]
  | .right lbc mc lac la => cases mc <;> cases la <;> simp [lookahead, complement]

-- ▷K • ▷L = ▷(K ∩ L)
theorem la_concat_eq_la_inter (k l : Lang α) : ▷ k • ▷ l ≐ ▷ (k ∩ l) := by
  intro w
  match w with
  | .left lbc lb main la =>
    constructor
    . rintro ⟨w₁, w₂, hk, hl, ⟨pref, suff, rfl, rfl, rfl⟩⟩; cases pref <;> cases suff <;> simp [lookahead, intersection] at ⊢ hl hk; exact ⟨hk, hl⟩
    . cases main <;> simp [lookahead, intersection]; intro hk hl; exact ⟨.left lbc lb [] la, .left lbc lb [] la, hk, hl, ⟨[], [], rfl, rfl, by simp; rfl⟩⟩
  | .middle lbc mc main la =>
    constructor
    . rintro ⟨w₁, w₂, hk, hl, ⟨pref, suff, hmain, rfl, rfl⟩ | ⟨mc₁, mc₂, rfl, rfl, rfl⟩⟩
      · cases pref <;> cases suff <;> simp [lookahead] at hk
      · cases main <;> simp [lookahead] at hl
    . cases main <;> simp [lookahead]
  | .right lbc mc lac la =>
    constructor
    . rintro ⟨w₁, w₂, hk, hl, ⟨mc₁, mc₂, rfl, rfl, rfl⟩⟩
      cases mc₁ <;> cases mc₂ <;> cases la <;> simp [intersection, lookahead] at hk hl ⊢ <;> exact ⟨hk, hl⟩
    . cases mc <;> rcases la with _  | ⟨hd, tl⟩ <;> simp [lookahead, intersection] <;> intro hk hl;
      . exact ⟨.right lbc 0 lac [], .right lbc 0 lac [], hk, hl, 0, 0, rfl, by simp, rfl⟩
      . exact ⟨.right lbc 0 lac (hd::tl), .right lbc 0 lac (hd :: tl), hk, hl, 0, 0, rfl, by simp, rfl⟩

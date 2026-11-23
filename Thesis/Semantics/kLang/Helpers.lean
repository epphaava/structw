import Thesis.Semantics.kLang.«1_StructuredWords»
import Thesis.Semantics.kLang.«2_Operators»
import Thesis.Semantics.kLang.«3_Derivatives»
import Thesis.Semantics.Lang.«3_Derivatives»

namespace helpers

open StructuredWords
open kStructuredWords
open kDerivatives
open kOperators
open Operators
open Derivatives


theorem derLB_word_val (w : List α) (l : kLang α n) : (derLB_word w l).1 = derLB_word w l.1 := by
  induction w generalizing n l with
  | nil => rfl
  | cons a tl ih => exact ih _

theorem der_word_val (w : List α) (l : kLang α n) : (der_word w l).1 = der_word w l.1 := by
  induction w generalizing n l with
  | nil => rfl
  | cons a tl ih => exact ih _

  theorem derLA_word_val (w : List α) (l : kLang α n) : (derLA_word w l).1 = derLA_word w l.1 := by
  induction w generalizing n l with
  | nil => rfl
  | cons a tl ih => exact ih _


theorem wc_steps_le {u v w : Word α} (h : wc u v w) :
    u.word_steps ≤ w.word_steps ∧ v.word_steps ≤ w.word_steps := by
  cases w with
  | left => obtain ⟨_, _, _, rfl, rfl⟩ := h; simp [Word.word_steps]
  | middle _ _ _ =>
    rcases h with ⟨_, _, _, rfl, rfl⟩ | ⟨mc₁, mc₂, hmc, rfl, rfl⟩ <;> simp [Word.word_steps] <;> omega
  | right mc lac la =>
    obtain ⟨mc₁, mc₂, hmc, rfl, rfl⟩ := h
    simp [Word.word_steps]; omega

end helpers

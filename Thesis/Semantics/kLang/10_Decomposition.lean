import Thesis.Semantics.kLang.«1_StructuredWords»
import Thesis.Semantics.kLang.«2_Operators»
import Thesis.Semantics.kLang.«3_Derivatives»

open StructuredWords
open kStructuredWords
open kOperators
open kDerivatives

variable {α : Type}

def nlblDisj (l : kLang α n) : kLang α n :=
  ⟨fun w =>
    match w with
    | .right _ _ [] => l w
    | _ => False,
   fun w h => by
    match w with
    | .right _ _ [] => exact l.2 _ h
    | .left .. | .middle .. | .right _ _ (_ :: _) => contradiction⟩

def derLBDisj (l : kLang α n) : kLang α n :=
  ⟨fun w =>
    match w with
    | .left (a, lb) main la => derLB a l (mk_word lb main la)
    | _ => False,
   fun w h => by
    match w with
    | .left .. => simp [word_steps]
    | .middle .. | .right .. => contradiction⟩

def derDisj (l : kLang α n) : kLang α n :=
  ⟨fun w =>
    match w with
    | .middle mcount (a, main) la => der a l (mk_mcount_word mcount.succ main la)
    | _ => False,
   fun w h => by
    match w with
    | .middle _ (a, main) _ =>
      have hb := (der a l).2 _ h
      cases main <;> simp [mk_mcount_word, word_steps] at hb ⊢ <;> omega
    | .left .. | .right .. => contradiction⟩

def derLADisj (l : kLang α n) : kLang α n :=
  ⟨fun w =>
    match w with
    | .right mcount lacount (a :: la) => derLA a l (.right mcount lacount.succ la)
    | _ => False,
   fun w h => by
    match w with
    | .right _ _ (a :: _) => have hb := (derLA a l).2 _ h; simp [word_steps] at hb ⊢; omega
    | .left .. | .middle .. | .right _ _ [] => contradiction⟩

theorem structuredLanguage_decomposition (l : kLang α n) : l ≐ (nlblDisj l) ∪ (derLBDisj l) ∪ (derDisj l) ∪ (derLADisj l) := by
  intro w
  match w with
  | .left (a, []) [] la => simp [kOperators.union, Operators.union, nlblDisj, derLBDisj, derDisj, derLADisj, derLB, Derivatives.derLB, mk_word, mk_mcount_word]
  | .left (a, []) (m :: ms) la => simp [kOperators.union, Operators.union, nlblDisj, derLBDisj, derDisj, derLADisj, derLB, Derivatives.derLB, mk_word, mk_mcount_word, toList]
  | .left (a, x :: xs) main la => simp [kOperators.union, Operators.union, nlblDisj, derLBDisj, derDisj, derLADisj, derLB, Derivatives.derLB, mk_word, toList]
  | .middle mcount (a, []) la => simp [kOperators.union, Operators.union, nlblDisj, derLBDisj, derDisj, derLADisj, der, Derivatives.der, mk_mcount_word]
  | .middle mcount (a, m :: ms) la => simp [kOperators.union, Operators.union, nlblDisj, derLBDisj, derDisj, derLADisj, der, Derivatives.der, mk_mcount_word, toList]
  | .right mcount lacount [] => simp [kOperators.union, Operators.union, nlblDisj, derLBDisj, derDisj, derLADisj]
  | .right mcount lacount (a :: la) => simp [kOperators.union, Operators.union, nlblDisj, derLBDisj, derDisj, derLADisj, derLA, Derivatives.derLA]

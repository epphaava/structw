import Thesis.Semantics.Lang.«1_StructuredWords»
import Thesis.Semantics.Lang.«2_Operators»
import Thesis.Semantics.Lang.«3_Derivatives»

open StructuredWords
open Operators
open Derivatives

variable {α : Type}

def nlblDisj (l : Lang α) : Lang α := λ w =>
  match w with
  | .right _ _ [] => l w
  | _ => False

def derLBDisj (l : Lang α) : Lang α := λ w =>
  match w with
  | .left (a, lb) main la => derLB a l (mk_word lb main la)
  | _ => False

def derDisj (l : Lang α) : Lang α := λ w =>
  match w with
  | .middle mcount (a, main) la => der a l (mk_mcount_word mcount.succ main la)
  | _ => False

def derLADisj (l : Lang α) : Lang α := λ w =>
  match w with
  | .right mcount lacount (a :: la) => derLA a l (.right mcount lacount.succ la)
  | _ => False

theorem structuredLanguage_decomposition (l : Lang α) : l ≐ (nlblDisj l) ∪ (derLBDisj l) ∪ (derDisj l) ∪ (derLADisj l) := by
  intro w
  match w with
  | .left (a, []) [] la => simp [union, nlblDisj, derLBDisj, derDisj, derLADisj, derLB, mk_word, mk_mcount_word]
  | .left (a, []) (m :: ms) la => simp [union, nlblDisj, derLBDisj, derDisj, derLADisj, derLB, mk_word, mk_mcount_word, toList]
  | .left (a, x :: xs) main la => simp [union, nlblDisj, derLBDisj, derDisj, derLADisj, derLB, mk_word, toList]
  | .middle mcount (a, []) la => simp [union, nlblDisj, derLBDisj, derDisj, derLADisj, der, mk_mcount_word]
  | .middle mcount (a, m :: ms) la => simp [union, nlblDisj, derLBDisj, derDisj, derLADisj, der, mk_mcount_word, toList]
  | .right mcount lacount [] => simp [union, nlblDisj, derLBDisj, derDisj, derLADisj]
  | .right mcount lacount (a :: la) => simp [union, nlblDisj, derLBDisj, derDisj, derLADisj, derLA]

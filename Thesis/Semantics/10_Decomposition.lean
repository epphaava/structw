import Thesis.Semantics.«1_StructuredWords»
import Thesis.Semantics.«2_Operators»
import Thesis.Semantics.«3_Derivatives»

open StructuredWords
open Operators

variable {α : Type}

def nlblDisj (l : Lang α) : Lang α := λ w =>
  match w with
  | .right _ _ _ [] => l w
  | _ => False

def derLBDisj (l : Lang α) : Lang α := λ w =>
  match w with
  | .left lbcount (a, lb) main la => derLB a l (mk_word lbcount.succ lb main la)
  | _ => False

def derDisj (l : Lang α) : Lang α := λ w =>
  match w with
  | .middle lbcount mcount (a, main) la => der a l (mk_mcount_word lbcount mcount.succ main la)
  | _ => False

def derLADisj (l : Lang α) : Lang α := λ w =>
  match w with
  | .right lbcount mcount lacount (a :: la) => derLA a l (.right lbcount mcount lacount.succ la)
  | _ => False

theorem structuredLanguage_decomposition (l : Lang α) : l ≐ (nlblDisj l) ∪ (derLBDisj l) ∪ (derDisj l) ∪ (derLADisj l) := by
  intro w
  match w with
  | .left lbcount (a, []) [] la => simp [union, nlblDisj, derLBDisj, derDisj, derLADisj, derLB, mk_word, mk_mcount_word]
  | .left lbcount (a, []) (m :: ms) la => simp [union, nlblDisj, derLBDisj, derDisj, derLADisj, derLB, mk_word, mk_mcount_word, toList]
  | .left lbcount (a, x :: xs) main la => simp [union, nlblDisj, derLBDisj, derDisj, derLADisj, derLB, mk_word, toList]
  | .middle lbcount mcount (a, []) la => simp [union, nlblDisj, derLBDisj, derDisj, derLADisj, der, mk_mcount_word]
  | .middle lbcount mcount (a, m :: ms) la => simp [union, nlblDisj, derLBDisj, derDisj, derLADisj, der, mk_mcount_word, toList]
  | .right lbcount mcount lacount [] => simp [union, nlblDisj, derLBDisj, derDisj, derLADisj]
  | .right lbcount mcount lacount (a :: la) => simp [union, nlblDisj, derLBDisj, derDisj, derLADisj, derLA]

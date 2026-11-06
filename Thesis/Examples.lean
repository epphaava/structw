import Thesis.Syntax.«1_Expressions»
import Thesis.Syntax.«2_Derivatives»
import Thesis.Syntax.«4_DerivativeCorrectHelpers»
import Thesis.Syntax.«5_Nullability»
import Thesis.Syntax.«3_DerivativeCorrectness»
import Thesis.Algorithm

open Algorithm
open SRegex
open StructuredWords
open Operators
open NullabilityLaws
open DerCorrectHelp
open SRegexDerivatives
open SRegexDerivatives
open Nullability
open DerCorrect
open SRegexDerivatives

variable {α : Type} [DecidableEq α]


-- Example 3.2.1

def L_3_2_1 : Lang Char := λ w =>
    w = .left 0 ('a', []) ['b']  ['c', 'd'] ∨
    w = .middle 2 2 ('a', ['b']) ['c']

example : der 'a' L_3_2_1 (.middle 2 3 ('b', []) ['c']) := by
  simp [der, L_3_2_1]; trivial

example (w : Word Char) : ¬ der 'b' L_3_2_1 w := by
  intro h
  rcases w with ⟨⟩ | ⟨lbc, _ | mc, main, la⟩ | ⟨lbc, _ | mc, _ | lac, la⟩ <;>
    simp [der, L_3_2_1, NEList, Prod.mk.injEq] at h

example : derLB 'a' L_3_2_1 ((.middle 1 0 ('b', [])  ['c', 'd'] )) := by
  simp [derLB, L_3_2_1, toList]


-- Example 3.4.1

def K_3_4_1 : Lang Char := λ w => w = Sum.inl (('a', []), ['b', 'c', 'd'])

def L_3_4_1 : Lang Char := λ w => w = Sum.inl (('b', ['c']), ['d'])

example : der 'a' K_3_4_1 (Sum.inr (0, ['b', 'c', 'd'])) := by
  simp [der, K_3_4_1]; trivial

example : derLA_word ['b', 'c'] (der 'a' K_3_4_1) (Sum.inr (2, ['d'])) := by
  simp [derLA_word, derLA, der, K_3_4_1]; trivial

example : der_word ['b', 'c'] L_3_4_1 (Sum.inr (0, ['d'])) := by
  simp [der_word, der, L_3_4_1]; trivial

example : derLA 'd' (der_word ['a', 'b', 'c'] (K_3_4_1 • L_3_4_1)) (Sum.inr (1, [])) := by
  simp [derLA, der_word, der, concat, K_3_4_1, L_3_4_1, wc]
  exists [], 'b', ['c']


-- Example 4.1.1

def r_4_1_1_exact : Expr Char := #'a' • ▷#'b'
def r_4_1_1_prefix : Expr Char := #'a' • ▷(#'b' • T)

example : sem r_4_1_1_exact (Sum.inl (('a', []), ['b'])) := by
  exists (Sum.inl (('a', []), ['b'])); simp [sem, la, symb, wc]; trivial

example : sem r_4_1_1_prefix (Sum.inl (('a', []), ['b', 'c'])) := by
  exists (Sum.inl (('a', []), ['b', 'c'])); simp [sem, la, symb, wc, concat, top];
  constructor
  . exists (Sum.inl (('b', []), ['c'])); simp
    exists (Sum.inl (('c', []), [])); right;
    exists [], 'c', []
  . trivial

example : ¬ sem r_4_1_1_exact (Sum.inl (('a', []), ['b', 'c'])) := by
  intro h
  obtain ⟨x, y, hx, hy, hwc⟩ := h
  match x with
  | Sum.inl ((hd, tl), v) =>
    cases hwc with
    | inl hwc => obtain ⟨_, h, _⟩ := hwc; simp at h
    | inr hwc =>
      cases hwc with
      | inl hwc => obtain ⟨_, _⟩ := hwc; subst y; simp [sem, la, symb] at hy
      | inr hwc => obtain ⟨xs, z, zs, htl, _, _⟩ := hwc; simp at htl
  | Sum.inr (n, v) => cases n <;> simp [sem, symb] at hx


-- Example 4.2.1

def r_4_2_1 : Regex Char := #'a' • ▷#'b'

example : D 'a' (regexToSRegex r_4_2_1) =
    .plus ((I [⟨0, 1, 0⟩] - T [⟨0, 0, 1⟩]) • ▷(#'b' [⟨1, 0, 0⟩] - SRegex.plus (#'b' [⟨0, 1, 0⟩]) (#'b' [⟨0, 0, 1⟩]))) (∅ • ∅) := by
  simp [r_4_2_1, regexToSRegex, D, DLB, DLA, filterD, filterDLB, Steps.lbStep, Steps.mStep, Steps.laStep,
    Steps.lbStepHelp, Steps.mStepHelp, Steps.laStepHelp, Steps.zeroSteps]

example : DLA 'a' (regexToSRegex r_4_2_1) = ∅ • DLA 'a' (regexToSRegex ▷ #'b') := by
  simp [r_4_2_1, regexToSRegex, DLA]

example : sem (D 'a' r_4_2_1) ≐ sem ((ε // ▹ε) • ▷#'b') := by
  intro w
  simp [sem, r_4_2_1, D, union, DLA, concat, empty]

example : sem (DLA 'a' r_4_2_1) ≐ ∅ := by
  intro w
  simp [r_4_2_1, empty]; intro h
  simp [DLA, sem, concat, empty] at h

-- Example 5.3
#eval findAllMatches (α := Char) ((Regex.star (#'a') I • ▷(Regex.star (#'a') I) : Regex Char)) ['a']

import Thesis.Syntax.«1_Expressions»
import Thesis.Syntax.«2_Derivatives»
import Thesis.Syntax.Helpers.«4_DerivativeCorrectness»
import Thesis.Syntax.«5_Nullability»
import Thesis.Syntax.«3_DerivativeCorrectness»
import Thesis.Algorithm

open Algorithm
open SRegex
open StructuredWords
open Operators
open NullabilityLaws
open DerCorrectHelpers
open SRegexDerivatives
open SRegexDerivatives
open Nullability
open NullabilityHelpers
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



-- Example 4.1.1

def r_4_1_1_exact : SRegex Char :=
  regexToSRegex (#'a' • ▷#'b' : Regex Char)

def r_4_1_1_prefix : SRegex Char :=
  regexToSRegex (#'a' • ▷(#'b' • T) : Regex Char)

example : sem r_4_1_1_exact 0 (.middle 0 0 ('a', []) ['b']) := by
  simp [r_4_1_1_exact, regexToSRegex, sem, sem.atom, sem.steps, Steps.zeroSteps, concat, wc, lookahead, union, empty]
  exact ⟨.middle 0 0 ('a', []) ['b'], by simp, .left 0 ('a', []) [] ['b'], by simp, by simp⟩

example : sem r_4_1_1_prefix 0 (.middle 0 0 ('a', []) ['b', 'c']) := by
  simp [r_4_1_1_prefix, regexToSRegex, sem, sem.atom, sem.steps, Steps.zeroSteps,
    concat, wc, lookahead, union, empty, top]
  refine ⟨.middle 0 0 ('a', []) ['b', 'c'], ?_, .left 0 ('a', []) [] ['b', 'c'], ?_, ?_⟩
  · simp [symb]
  · exact ⟨.left 0 ('a', []) ['b'] ['c'], by simp, .left 0 ('a', ['b']) ['c'] [], by simp,
      ['b'], ['c'], by simp⟩
  · simp

example : ¬ sem r_4_1_1_exact 0 (.middle 0 0 ('a', []) ['b', 'c']) := by
  simp [r_4_1_1_exact, regexToSRegex, sem, sem.atom, sem.steps, Steps.zeroSteps,
    concat, wc, lookahead, union, empty]
  intro x hx y hy
  constructor <;> rintro rfl rfl <;> simp at hx hy


-- Example 4.2.1

def r_4_2_1 : Regex Char := #'a' • ▷#'b'

theorem D_4_2_1 : D 'a' (regexToSRegex r_4_2_1) =
    SRegex.plus
      (SRegex.mult
        (SRegex.complement (I [⟨1, 0⟩]) (T [⟨0, 1⟩]))
        (▷(SRegex.complement (#'b' [⟨0, 0⟩]) (SRegex.plus (#'b' [⟨1, 0⟩]) (#'b' [⟨0, 1⟩])))))
      (SRegex.mult ∅ ∅) := by
  simp [r_4_2_1, regexToSRegex, D, DLB, DLA, filterD, filterDLB, Steps.mStep, Steps.laStep,
    Steps.mStepHelp, Steps.laStepHelp, Steps.zeroSteps]

example : DLA 'a' (regexToSRegex r_4_2_1) = ∅ • DLA 'a' (regexToSRegex ▷ #'b') := by
  simp [r_4_2_1, regexToSRegex, DLA]

example (n : Nat) : sem (DLA 'a' (regexToSRegex r_4_2_1)) n ≐ ∅ := by
  intro w
  simp [r_4_2_1, regexToSRegex, DLA, sem, concat, empty]

-- Example 5.3
#eval findAllMatches (α := Char) ((Regex.star (#'a') I • ▷(Regex.star (#'a') I) : Regex Char)) ['a']

-- a* ▷a* kõik matchid m + la ≤ 3
#eval findAllMatches (α := Char) ((Regex.star (#'a') I • ▷(Regex.star (#'a') I) : Regex Char)) ['a', 'a', 'a']

-- (a + b)* b ▷c : "b", "bb", "abb", followed by "c"
#eval findAllMatches (α := Char) ((Regex.star (#'a' + #'b') I • #'b' • ▷#'c' : Regex Char)) ['a', 'b', 'b', 'c']

-- a* ▷(b* c) : the lookahead is "c", "bc" or "bbc"
#eval findAllMatches (α := Char) ((Regex.star (#'a') I • ▷(Regex.star (#'b') (#'c')) : Regex Char)) ['a', 'a', 'b', 'b', 'c']

-- ◁(a + b) c* ▷(a b)
#eval findAllMatches (α := Char) ((◁(#'a' + #'b') • Regex.star (#'c') I • ▷(#'a' • #'b') : Regex Char)) ['b', 'c', 'c', 'a', 'b']


-- ◁a* a* ▷a*
#eval findAllMatches (α := Char) ((◁(Regex.star (#'a') I) • Regex.star (#'a') I • ▷(Regex.star (#'a') I) : Regex Char)) ['a', 'a']

-- ◁a a ▷T
#eval findAllMatches (α := Char) ((◁#'a' • #'a' • ▷T : Regex Char)) ['a', 'a', 'a']

-- ◁b a* ▷c
#eval findAllMatches (α := Char) ((◁#'b' • Regex.star (#'a') I • ▷#'c' : Regex Char)) ['a', 'b', 'a', 'a', 'c']

-- ◁(T b) a* ▷c
#eval findAllMatches (α := Char) ((◁(T • #'b') • Regex.star (#'a') I • ▷#'c' : Regex Char)) ['a', 'b', 'a', 'a', 'c']

-- ◁(T b) a* ▷T
#eval findAllMatches (α := Char) ((◁(T • #'b') • Regex.star (#'a') I • ▷T : Regex Char)) ['b', 'a', 'a']


#eval findAllMatches (α := Char) ((◁(T - (T • #'a')) • #'a' • ▷T : Regex Char)) ['a', 'a', 'b', 'a']

#eval findAllMatches (α := Char) ((◁(Regex.star (#'a') I & (T • #'a')) • #'b' • ▷T : Regex Char)) ['a', 'a', 'b', 'b']

#eval findAllMatches (α := Char) (((Regex.star (#'a' + #'b') I & (T • #'b')) • ▷#'a' : Regex Char)) ['a', 'b', 'b', 'a']

#eval findAllMatches (α := Char) (((T - (T • #'b' • #'b' • T)) • ▷#'a' : Regex Char)) ['a', 'b', 'a', 'b', 'b', 'a']

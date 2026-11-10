import Thesis.Syntax.«2_Derivatives»

-- Temporary check, safe to delete: does unanchored lookbehind give a wrong match?
open SRegex SRegexDerivatives

namespace ScratchLbTest

def compose (s₁ s₂ : Steps) : Option Steps :=
  if s₁.la = s₂.m + s₂.la then some ⟨s₁.m + s₂.m, s₂.la⟩ else none
def concatN (n₁ n₂ : List Steps) : List Steps := n₁.flatMap fun s₁ => n₂.filterMap (compose s₁)
def starStep (nr acc : List Steps) : List Steps := (acc ++ concatN nr acc).eraseDups
def starN (nr : List Steps) : Nat → List Steps → List Steps
  | 0, acc => acc
  | k + 1, acc => starN nr k (starStep nr acc)

def N {α} (r : SRegex α) : List Steps :=
  match r with
  | .empty => []
  | .unit ss => ss
  | .top ss => ss
  | .symbol _ _ => []
  | .plus r₁ r₂ => N r₁ ++ N r₂
  | .intersection r₁ r₂ => (N r₁).filter fun s => (N r₂).contains s
  | .complement r₁ r₂ => (N r₁).filter fun s => !(N r₂).contains s
  | .mult r₁ r₂ => concatN (N r₁) (N r₂)
  | .star r b => starN (N r) (Steps.maxSum (N b) + 1) (N b)
  | .lb r => (N r).map fun s => ⟨0, s.la⟩
  | .la r => (N r).filterMap fun s => if s.la = 0 then some ⟨0, s.m⟩ else none

-- ◁((T • a) − a): "everything before the match is some string ending in `a`, but is not exactly `a`".
def content : Regex Char := .complement (.mult .top (.symbol 'a')) (.symbol 'a')
def r : Regex Char := .lb content

-- On the word "a" there should be no match: the only non-empty prefix is "a", which is excluded.
#eval N (xD ['a'] (regexToSRegex r))
-- Same content, but on "ba": the prefix "ba" ends in `a` and is not "a", so a match at position 2 is right.
#eval N (xD ['b', 'a'] (regexToSRegex r))

open StructuredWords Operators in
/-- The new semantics claims a match on "a" with lookbehind "a" (empty match at position 1).
It gets it by letting the lookbehind content pretend 2 characters were read, not 1. -/
example : sem (DLB 'a' (regexToSRegex r)) (.right 0 0 []) := by
  refine ⟨2, ?_⟩
  simp only [regexToSRegex, r, content, D, DLB, DLA, sem, filterD, filterDLB, Steps.mStep, Steps.laStep,
    Steps.mStepHelp, Steps.laStepHelp, Steps.zeroSteps, complement, union, concat]
  refine ⟨Or.inr ⟨.right 1 1 [], .right 1 0 [], ?_, ?_, 1, 1, rfl, rfl, rfl⟩, ?_⟩
  all_goals simp [sem, sem.atom, sem.steps, Steps.mStepHelp, Steps.laStepHelp, complement, union, unit, top, empty]

end ScratchLbTest

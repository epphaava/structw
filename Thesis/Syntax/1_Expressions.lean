import Thesis.Semantics.«1_StructuredWords»
import Thesis.Semantics.«2_Operators»

namespace SRegex

open StructuredWords
open Operators

-- Definition 4.1.1 (Regular Exprestepsion syntax).
inductive Regex (α : Type) : Type
| empty : Regex α
| unit : Regex α
| top : Regex α
| symbol : α → Regex α
| plus : Regex α → Regex α → Regex α
| intersection : Regex α → Regex α → Regex α
| complement : Regex α → Regex α → Regex α
| mult : Regex α → Regex α → Regex α
| star : Regex α → Regex α → Regex α
| lb : Regex α → Regex α
| la : Regex α → Regex α
deriving Repr, DecidableEq

notation "∅" => Regex.empty
notation "I" => Regex.unit
notation "T" => Regex.top
prefix:max "#" => Regex.symbol
infixr:30 " + " => Regex.plus
infixl:55 " & " => Regex.intersection
infixl:30 " -" => Regex.complement
infixr:60 " • " => Regex.mult
postfix:max "*" => Regex.star
prefix:max "◁" => Regex.lb
prefix:max "▷" => Regex.la


structure Steps where
  m  : Nat := 0
  la : Nat := 0
deriving Repr, DecidableEq

namespace Steps

def zeroSteps : Steps := {}

def addSteps (s₁ s₂ : Steps) : Steps := ⟨s₁.m + s₂.m, s₁.la + s₂.la⟩



def mStepHelp (s : Steps) : Steps := {s with m := s.m.succ}
def mStep (ss : List Steps) : List Steps := ss.map mStepHelp
prefix:max "↑₂" => mStep


def laStepHelp (s : Steps) : Steps := {s with la := s.la.succ}
def laStep (ss : List Steps) : List Steps := ss.map laStepHelp
prefix:max "↑₃" => laStep

def stepsSum (s : Steps) : Nat := .add s.m s.la

def maxSum : List Steps → Nat
  | [] => 0
  | s :: ss => max (Steps.stepsSum s) (maxSum ss)

end Steps



inductive SRegex (α : Type) : Type
| empty : SRegex α
| unit : List Steps → SRegex α
| top : List Steps → SRegex α
| symbol : α → List Steps → SRegex α
| plus : SRegex α → SRegex α → SRegex α
| intersection : SRegex α → SRegex α → SRegex α
| complement : SRegex α → SRegex α → SRegex α
| mult : SRegex α → SRegex α → SRegex α
| star : SRegex α → SRegex α → SRegex α
| lb : SRegex α → SRegex α
| la : SRegex α → SRegex α
--deriving Repr, DecidableEq


notation "∅" => SRegex.empty
notation "I" => SRegex.unit
notation "T" => SRegex.top
prefix:max "#" => SRegex.symbol
infixr:30 " + " => SRegex.plus
infixl:55 " & " => SRegex.intersection
infixl:30 " -" => SRegex.complement
infixr:60 " • " => SRegex.mult
postfix:max "*" => SRegex.star
prefix:max "◁" => SRegex.lb
prefix:max "▷" => SRegex.la

def sem [DecidableEq α] (r : SRegex α) (n : Nat) : Lang α :=
  match r with
  | .empty => ∅
  | .unit ss => atom n ss I
  | .top ss => atom n ss T
  | .symbol a ss => atom n ss #a
  | .plus r₁ r₂ => (sem r₁ n) ∪ (sem r₂ n)
  | .intersection r₁ r₂ => (sem r₁ n) ∩ (sem r₂ n)
  | .complement r₁ r₂ => (sem r₁ n) - (sem r₂ n)
  | .mult r₁ r₂ => (sem r₁ n) • (sem r₂ n)
  | .star r b => Operators.star (sem r n) (sem b n)
  | .lb r => lookbehind (sem r n)
  | .la r => lookahead (sem r n)
  where
    steps (n : Nat) (s : Steps) (l : Lang α) : Lang α := fun w =>
      let k := .sub n (.add s.m s.la)
      match w with
      | .left lbc lb main la =>
          s.m = 0 ∧ s.la = 0 ∧ k ≤ lbc ∧ l (.left (lbc - k) lb main la)
      | .middle lbc mc main la =>
          s.la = 0 ∧ k ≤ lbc ∧ s.m ≤ mc ∧ l (.middle (lbc - k) (mc - s.m) main la)
      | .right lbc mc lac la =>
          k ≤ lbc ∧ s.m ≤ mc ∧ s.la ≤ lac ∧ l (.right (lbc - k) (mc - s.m) (lac - s.la) la)
    atom (n : Nat) : List Steps → Lang α → Lang α
      | [], _ => ∅
      | s :: rest, l => (steps n s l) ∪ (atom n rest l)


def regexToSRegex : Regex α → SRegex α
  | .empty => ∅
  | .unit => I [.zeroSteps]
  | .top => T [.zeroSteps]
  | .symbol a => #a [.zeroSteps]
  | .plus r₁ r₂ => (regexToSRegex r₁) + (regexToSRegex r₂)
  | .intersection r₁ r₂ => (regexToSRegex r₁) & (regexToSRegex r₂)
  | .complement r₁ r₂ => (regexToSRegex r₁) - (regexToSRegex r₂)
  | .mult r₁ r₂ => (regexToSRegex r₁) • (regexToSRegex r₂)
  | .star r b => .star (regexToSRegex r) (regexToSRegex b)
  | .lb r => ◁ (regexToSRegex r)
  | .la r => ▷ (regexToSRegex r)




end SRegex

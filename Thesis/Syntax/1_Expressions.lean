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

/- -- Definition 4.1.2 (Denotational semantics ⟦·⟧).
def sem [DecidableEq α] (r : Regex α) : Lang α :=
  match r with
  | .empty => ∅
  | .unit => I
  | .top => T
  | .symbol x => # x
  | .plus r₁ r₂ => (sem r₁) ∪ (sem r₂)
  | .intersection r₁ r₂ => (sem r₁) ∩ (sem r₂)
  | .complement r₁ r₂ => (sem r₁) - (sem r₂)
  | .mult r₁ r₂ => (sem r₁) • (sem r₂)
  | .star r b => Operators.star (sem r) (sem b)
  | .lb r => lookbehind (sem r)
  | .la r => lookahead (sem r) -/

structure Steps where
  lb : Nat := 0
  m  : Nat := 0
  la : Nat := 0
deriving Repr, DecidableEq

namespace Steps

def zeroSteps : Steps := {}

def addSteps (s₁ s₂ : Steps) : Steps := ⟨s₁.lb + s₂.lb, s₁.m + s₂.m, s₁.la + s₂.la⟩
-- instance : Add Steps := ⟨addSteps⟩

def lbStepHelp (s : Steps) : Steps := {s with lb := s.lb.succ}
def lbStep (ss : List Steps) : List Steps := ss.map lbStepHelp
prefix:max "↑₁" => lbStep


def mStepHelp (s : Steps) : Steps := {s with m := s.m.succ}
def mStep (ss : List Steps) : List Steps := ss.map mStepHelp
prefix:max "↑₂" => mStep


def laStepHelp (s : Steps) : Steps := {s with la := s.la.succ}
def laStep (ss : List Steps) : List Steps := ss.map laStepHelp
prefix:max "↑₃" => laStep

def stepsSum (s : Steps) : Nat := .add (.add s.lb s.m) s.la

def maxSum : List Steps → Nat
  | [] => 0
  | s :: ss => max (Steps.stepsSum s) (maxSum ss)

end Steps

/- namespace Expr

def Expr (α : Type) := List (Regex α × List Steps)

def regexToExpr (r : Regex α) : Expr α := [(r, [.zeroSteps])]

def mapSteps (f : Steps → Steps) (e : Expr α) : Expr α :=
  e.map fun (r, steps) => (r, steps.map f)

def lbStep : Expr α → Expr α := mapSteps Steps.lbStepHelp
prefix:max "↑₁" => lbStep

def mStep : Expr α → Expr α := mapSteps Steps.mStepHelp
prefix:max "↑₂" => mStep

def laStep : Expr α → Expr α := mapSteps Steps.laStepHelp
prefix:max "↑₃" => laStep



end Expr -/


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

def sem [DecidableEq α] (r : SRegex α) : Lang α :=
  match r with
  | .empty => ∅
  | .unit ss => atom ss I
  | .top ss => atom ss T
  | .symbol a ss => atom ss #a
  | .plus r₁ r₂ => (sem r₁) ∪ (sem r₂)
  | .intersection r₁ r₂ => (sem r₁) ∩ (sem r₂)
  | .complement r₁ r₂ => (sem r₁) - (sem r₂)
  | .mult r₁ r₂ => (sem r₁) • (sem r₂)
  | .star r b => Operators.star (sem r) (sem b)
  | .lb r => lookbehind (sem r)
  | .la r => lookahead (sem r)
  where
    steps (s : Steps) (l : Lang α) : Lang α := fun w =>
      match w with
      | .left lbc lb main la =>
          s.m = 0 ∧ s.la = 0 ∧ s.lb ≤ lbc ∧ l (.left (lbc - s.lb) lb main la)
      | .middle lbc mc main la =>
          s.la = 0 ∧ s.lb ≤ lbc ∧ s.m ≤ mc ∧ l (.middle (lbc - s.lb) (mc - s.m) main la)
      | .right lbc mc lac la =>
          s.lb ≤ lbc ∧ s.m ≤ mc ∧ s.la ≤ lac ∧ l (.right (lbc - s.lb) (mc - s.m) (lac - s.la) la)
    atom : List Steps → Lang α → Lang α
      | [], _ => ∅
      | s :: rest, l => (steps s l) ∪ (atom rest l)


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


/-

/-- Apply the counted steps to a language: `↑₁^lb ↑₂^m ↑₃^la l`. -/
def shift (s : Steps) (l : Lang α) : Lang α :=
  Nat.repeat lbStep s.lb (Nat.repeat matchStep s.m (Nat.repeat laStep s.la l))

def shiftAll (steps : List Steps) (l : Lang α) : Lang α :=
  match steps with
  | [] => ∅
  | s :: rest => shift s l ∪ shiftAll rest l



abbrev Expr (α : Type) := List (Regex α × List Steps)


def insert [DecidableEq α] (r : Regex α) (steps : List Steps) : Expr α → Expr α
  | [] => [(r, steps)]
  | (r', ts) :: rest =>
    if r' = r then (r', ts ++ steps) :: rest else (r', ts) :: insert r steps rest

/-- Union of two stepped exprestepsions, keeping each regular exprestepsion once. -/
def merge [DecidableEq α] (e₁ e₂ : Expr α) : Expr α :=
  e₁.foldr (fun (r, steps) acc => insert r steps acc) e₂

def sem [DecidableEq α] : Expr α → Lang α
  | [] => ∅
  | (r, steps) :: rest => shiftAll steps (Regex.sem r) ∪ sem rest

end Expr

def sem [DecidableEq α] : SRegex α → Lang α
  | .empty => ∅
  | .unit steps => atom steps Operators.unit
  | .top steps => atom steps Operators.top
  | .symbol x steps => atom steps (symb x)
  | .plus r₁ r₂ => (sem r₁) ∪ (sem r₂)
  | .intersection r₁ r₂ => (sem r₁) ∩ (sem r₂)
  | .complement r₁ r₂ => (sem r₁) - (sem r₂)
  | .mult r₁ r₂ => (sem r₁) • (sem r₂)
  | .star r b => Operators.star (sem r) (sem b)
  | .lb r => lookbehind (sem r)
  | .la r => lookahead (sem r)
where
  steps (s : Steps) (l : Lang α) : Lang α := Nat.repeat Operators.lbStep s.lb (Nat.repeat Operators.matchStep s.m (Nat.repeat Operators.laStep s.la l))
  later (s : Steps) : Lang α :=
    if s.lb > 0 then ↑₂ T ∪ ↑₃ T
    else if s.m > 0 then ↑₃ T
    else ∅
  atom : List Steps → Lang α → Lang α
  | [], _ => Operators.empty
  | s :: rest, l => Operators.union (steps s (Operators.complement l (later s))) (atom rest l)

end SRegex

theorem shift_zero {α : Type} (l : Lang α) : shift Steps.zero l = l := rfl

theorem shiftAll_append {α : Type} (steps ts : List Steps) (l : Lang α) (w : Word α) : shiftAll (steps ++ ts) l w ↔ shiftAll steps l w ∨ shiftAll ts l w := by
  induction steps with
  | nil => simp [shiftAll, empty]
  | cons s rest ih => simp [shiftAll, union] at *; rw [ih]; exact or_assoc.symm

variable {α : Type} [DecidableEq α]

theorem Expr.sem_toExpr (r : Regex α) : Expr.sem (Expr.toExpr r) ≐ Regex.sem r := by
  intro w
  simp [toExpr, sem, shiftAll, shift_zero, union, empty]

theorem Expr.sem_append (e₁ e₂ : Expr α) : Expr.sem (e₁ ++ e₂) ≐ Expr.sem e₁ ∪ Expr.sem e₂ := by
  intro w
  induction e₁ with
  | nil => simp [sem, union, empty]
  | cons p rest ih => simp [sem, union] at *; rw [ih]; exact or_assoc.symm

theorem Expr.sem_insert (r : Regex α) (steps : List Steps) (e : Expr α) : sem (insert r steps e) ≐ shiftAll steps (Regex.sem r) ∪ Expr.sem e := by
  intro w
  induction e with
  | nil => simp [Expr.insert, Expr.sem, union, empty]
  | cons p rest ih =>
    obtain ⟨r', ts⟩ := p
    by_cases h : r' = r
    · subst h
      simp [insert, sem, union] at *; rw [shiftAll_append]
      constructor
      · rintro ((h1 | h2) | h3) <;> simp_all
      · rintro (h1 | h2 | h3) <;> simp_all
    · simp [insert, if_neg h, sem, union] at *; rw [ih]
      constructor
      · rintro (h1 | h2 | h3) <;> simp_all
      · rintro (h1 | h2 | h3) <;> simp_all

theorem Expr.sem_merge (e₁ e₂ : Expr α) : sem (merge e₁ e₂) ≐ sem e₁ ∪ sem e₂ := by
  intro w
  induction e₁ with
  | nil => simp [merge, sem, union, empty]
  | cons p rest ih =>
    obtain ⟨r, steps⟩ := p
    simp [merge, List.foldr_cons] at *
    rw [Expr.sem_insert]
    simp [sem, union] at *
    rw [ih]; exact or_assoc.symm -/


end SRegex

namespace StructuredWords

-- Structured words ----------------------------------


def NEList (α : Type) := α × List α
def toList (l : NEList α) := l.fst :: l.snd

-- Definition 3.1.1 (Structured words).

inductive Word (α : Type) where
  | left  (lbCount : Nat) (lb : NEList α) (main : List α) (la : List α)
  | middle (lbCount : Nat) (matchCount : Nat) (main : NEList α) (la : List α)
  | right (lbCount : Nat) (matchCount : Nat) (laCount : Nat) (la : List α)

def Word.word_to_list {α} : Word α → List α
  | .left _ lb main la => toList lb ++ main ++ la
  | .middle _ _ main la => toList main ++ la
  | .right _ _ _ la => la


def mk_mcount_word : Nat → Nat → List α → List α → Word α
  | m, n, [], la => .right m n 0 la
  | m, n, x :: xs, la => .middle m n (x, xs) la

def mk_word : Nat → List α → List α → List α → Word α
  | lbcount, [], main, la => mk_mcount_word lbcount 0 main la
  | lbcount, x :: xs, main, la => .left lbcount (x, xs) main la

export Word (word_to_list)


-- Languages over structured words --------------------------

def Lang (α : Type) : Type := Word α → Prop


-- Subset and equality relations on Lang -------------------

def subset (l₁ l₂ : Lang α) := ∀ (u : Word α), l₁ u → l₂ u
infix:25 " ⊆ " => subset

def subsetAll {α} (Ls : List (Lang α)) (L : Lang α) : Prop :=
  ∀ l ∈ Ls, l ⊆ L
infix:25 " ⊆ " => subsetAll

def LEq (k l : Lang α) :=
 ∀ u, k u ↔ l u
infixl:50 " ≐ " => LEq

end StructuredWords

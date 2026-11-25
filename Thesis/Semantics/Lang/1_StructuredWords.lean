namespace StructuredWords

-- Structured words ----------------------------------


def NEList (α : Type) := α × List α
def toList (l : NEList α) := l.fst :: l.snd

-- Definition 3.1.1 (Structured words).

inductive Word (α : Type) where
  | left (lb : NEList α) (main : List α) (la : List α)
  | middle (matchCount : Nat) (main : NEList α) (la : List α)
  | right (matchCount : Nat) (laCount : Nat) (la : List α)

def Word.word_to_list {α} : Word α → List α
  | .left lb main la => toList lb ++ main ++ la
  | .middle _ main la => toList main ++ la
  | .right _ _ la => la

def Word.word_steps : Word α → Nat
  | .left _ _ _ => 0
  | .middle mc _ _ => mc
  | .right mc lac _ => mc + lac

def Word.final_counts : Word α → Nat × Nat
  | .left _ main la => (main.length, la.length)
  | .middle mc main la => (mc + (toList main).length, la.length)
  | .right mc lac la => (mc, lac + la.length)

def is_split (w : List α) (mc lac : Nat) (u : Word α) : Prop :=
  u.word_to_list = w ∧ u.final_counts = (mc, lac)

def mk_mcount_word : Nat → List α → List α → Word α
  | n, [], la => .right n 0 la
  | n, x :: xs, la => .middle n (x, xs) la

def mk_word : List α → List α → List α → Word α
  | [], main, la => mk_mcount_word 0 main la
  | x :: xs, main, la => .left (x, xs) main la

export Word (word_to_list word_steps final_counts)


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

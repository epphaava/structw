namespace StructuredWords

-- Structured words ----------------------------------


def NEList (α : Type) := α × List α
def toList (l : NEList α) := l.fst :: l.snd

-- Definition 3.1.1 (Structured words).


def Word (α : Type) :=
  NEList α × List α × List α ⊕
  Nat × NEList α × List α ⊕
  Nat × Nat × List α

def Word.word_to_list {α} : Word α → List α := λ w =>
  match w with
  | Sum.inl (xs, ys, zs) => toList xs ++ ys ++ zs
  | Sum.inr w =>
    match w with
    | Sum.inl (_, ys, zs) => toList ys ++ zs
    | Sum.inr (_, _, zs) => zs

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

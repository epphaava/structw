import Thesis.Syntax.«1_Expressions»
import Thesis.Syntax.«2_Derivatives»

/-! Nullability of stepped regular expressions, and the list of all matches.

`N r lbc mc lac` decides whether `⟦r⟧` is nullable at the counts
`(lbc, mc, lac)`. After reading a word of length `n`, the matches are the
triples with `lbc + mc + lac = n`, i.e. the pairs of positions `(i, j)` with
`0 ≤ i ≤ j ≤ n`: lookbehind `w[0..i]`, match `w[i..j]`, lookahead `w[j..n]`.
`allMatches r n` lists exactly those pairs, each once. -/

namespace Nullability

open Regex

-- Atoms -------------------------------------------------------------------

/-- What `later s` rules out, on the counts left after removing `s`'s steps:
after a lookbehind step, any match or lookahead; after a match step, any
lookahead. -/
def laterN (s : Steps) (mc lac : Nat) : Bool :=
  if s.lb > 0 then mc ≥ 1 || lac ≥ 1
  else if s.m > 0 then lac ≥ 1
  else false

/-- An atom with base nullability `base` and triples `ss` is nullable at
`(lbc, mc, lac)` if some triple fits inside the counts and the base is
nullable at what is left. -/
def atomN (base : Nat → Nat → Nat → Bool) (ss : List Steps) (lbc mc lac : Nat) : Bool :=
  ss.any fun s =>
    s.lb ≤ lbc && s.m ≤ mc && s.la ≤ lac &&
    base (lbc - s.lb) (mc - s.m) (lac - s.la) && !laterN s (mc - s.m) (lac - s.la)

-- Nullability -------------------------------------------------------------

def NStar (fr fb : Nat → Nat → Nat → Bool) (lbc mc lac : Nat) : Bool :=
  fb lbc mc lac || (List.range mc).attach.any fun ⟨k, _⟩ =>
    fr lbc (k + 1) ((mc - (k + 1)) + lac) && NStar fr fb (lbc + (k + 1)) (mc - (k + 1)) lac
termination_by mc
decreasing_by rename_i hk; have := List.mem_range.mp hk; omega

/-- `⟦r⟧` is nullable at `(lbc, mc, lac)`. -/
def N {α} (r : SRegex α) (lbc mc lac : Nat) : Bool :=
  match r with
  | .empty => false
  | .unit ss => atomN (fun _ mc _ => mc == 0) ss lbc mc lac
  | .top ss => atomN (fun _ _ _ => true) ss lbc mc lac
  | .symbol _ _ => false
  | .plus r₁ r₂ => N r₁ lbc mc lac || N r₂ lbc mc lac
  | .intersection r₁ r₂ => N r₁ lbc mc lac && N r₂ lbc mc lac
  | .complement r₁ r₂ => N r₁ lbc mc lac && !N r₂ lbc mc lac
  | .mult r₁ r₂ => (List.range (mc + 1)).any fun mc₁ =>
      N r₁ lbc mc₁ ((mc - mc₁) + lac) && N r₂ (lbc + mc₁) (mc - mc₁) lac
  | .star r b => NStar (N r) (N b) lbc mc lac
  | .lb r => mc == 0 && N r 0 lbc lac
  | .la r => mc == 0 && N r lbc lac 0

-- All matches -------------------------------------------------------------

/-- All pairs `(i, j)` with `i ≤ j ≤ n`, each once. -/
def pairs (n : Nat) : List (Nat × Nat) :=
  (List.range (n + 1)).flatMap fun (i : Nat) =>
    (List.range ((n + 1) - i)).map fun (d : Nat) => (i, i + d)

/-- All matches of `r` in a word of length `n`: the pairs `(i, j)` where `r` is
nullable at `(i, j - i, n - j)`. -/
def allMatches {α} (r : SRegex α) (n : Nat) : List (Nat × Nat) :=
  (pairs n).filter fun (i, j) => N r i (j - i) (n - j)

/-- The same result as triples `(lbc, mc, lac)`. -/
def matchTriples {α} (r : SRegex α) (n : Nat) : List (Nat × Nat × Nat) :=
  (allMatches r n).map fun (i, j) => (i, j - i, n - j)

theorem mem_pairs (n i j : Nat) : (i, j) ∈ pairs n ↔ i ≤ j ∧ j ≤ n := by
  simp only [pairs, List.mem_flatMap, List.mem_range, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨i', hi', d, hd, rfl, rfl⟩; omega
  · rintro ⟨hij, hjn⟩; exact ⟨i, by omega, j - i, by omega, rfl, by omega⟩

theorem pairs_nodup (n : Nat) : (pairs n).Nodup := by
  unfold pairs List.Nodup
  rw [List.pairwise_flatMap]
  constructor
  · intro i _
    refine List.Pairwise.map _ ?_ List.nodup_range
    intro d₁ d₂ h e
    simp only [Prod.mk.injEq] at e
    exact h (by omega)
  · refine List.Pairwise.imp ?_ List.nodup_range
    intro i₁ i₂ hne x hx y hy e
    simp only [List.mem_map] at hx hy
    obtain ⟨d₁, _, rfl⟩ := hx
    obtain ⟨d₂, _, rfl⟩ := hy
    simp only [Prod.mk.injEq] at e
    exact hne e.1

/-- `allMatches` has no repetition. -/
theorem allMatches_nodup {α} (r : SRegex α) (n : Nat) : (allMatches r n).Nodup :=
  List.Pairwise.filter _ (pairs_nodup n)

/-- `allMatches` contains exactly the nullable pairs. -/
theorem mem_allMatches {α} (r : SRegex α) (n i j : Nat) :
    (i, j) ∈ allMatches r n ↔ i ≤ j ∧ j ≤ n ∧ N r i (j - i) (n - j) = true := by
  simp only [allMatches, List.mem_filter, mem_pairs, and_assoc]

end Nullability

import Thesis.SyntaxOld.Expressions
import Thesis.SyntaxOld.Nullability
import Thesis.Semantics.«9_NullabilityLaws»
import Thesis.Semantics.«1_StructuredWords»

namespace NullabilityCorrect

open Expr
open NullabilityLaws
open Operators
open StructuredWords

-- Theorem 4.3.1 — Correctness of nullability
theorem nullability_correct₁ [DecidableEq α] (r : Expr α) (lbc mc lac : Nat) : (N r lbc mc lac ↔ nullable (sem r) lbc mc lac) := by
  induction r generalizing lbc mc lac with
  | empty => simp [nullable, sem, empty, N]
  | unit => simp [nullable, sem, unit, N]
  | top => simp [nullable, sem, top, N]
  | symbol _ => simp [nullable, sem, symb, N]
  | plus r₁ r₂ ih₁ ih₂ =>
    if hr₁ : N r₁ lbc mc lac then
      have := (ih₁ lbc mc lac).mp hr₁; simp [nullable] at this
      simp [N, hr₁, nullable, sem, union, this]
    else
      if hr₂ : N r₂ lbc mc lac then
        have := (ih₂ lbc mc lac).mp hr₂; simp [nullable] at this
        simp [N, hr₂, nullable, sem, union, this]
      else
        simp [N, hr₁, hr₂, nullable, sem, union];
        exact ⟨mt (ih₁ lbc mc lac).mpr hr₁, mt (ih₂ lbc mc lac).mpr hr₂⟩
  | intersection r₁ r₂ ih₁ ih₂ =>
    if hr₁ : N r₁ lbc mc lac then
      if hr₂ : N r₂ lbc mc lac then
        simp [N, hr₁, hr₂, nullable, sem, intersection]
        exact ⟨(ih₁ lbc mc lac).mp hr₁, (ih₂ lbc mc lac).mp hr₂⟩
      else
        have := mt (ih₂ lbc mc lac).mpr hr₂; simp [nullable] at this
        simp [N, hr₂, nullable, sem, intersection, this]
    else
      have := mt (ih₁ lbc mc lac).mpr hr₁; simp [nullable] at this
      simp [N, hr₁, nullable, sem, intersection, this]
  | complement r₁ r₂ ih₁ ih₂ =>
    if hr₁ : N r₁ lbc mc lac then
      if hr₂ : N r₂ lbc mc lac then
        have := (ih₂ lbc mc lac).mp hr₂; simp [nullable] at this
        simp [N, hr₂, nullable, sem, complement, this]
      else
        simp [N, hr₁, hr₂, nullable, sem, complement]
        exact ⟨(ih₁ lbc mc lac).mp hr₁, mt (ih₂ lbc mc lac).mpr hr₂⟩
    else
      have := mt (ih₁ lbc mc lac).mpr hr₁; simp [nullable] at this
      simp [N, hr₁, nullable, sem, complement, this]
  | mult r₁ r₂ ih₁ ih₂ =>
    constructor
    . simp [N]; intro mc' hmc' hr₁ hr₂
      simp [nullable, sem]
      have hl₁ := (ih₁ lbc mc' (.add (.sub mc mc') lac)).mp hr₁
      have hl₂ := (ih₂ (.add lbc mc') (.sub mc mc') lac).mp hr₂; simp [nullable] at hl₁ hl₂
      exact ⟨.right lbc mc' (.sub mc mc' + lac) [], .right (.add lbc mc') (.sub mc mc') lac [], hl₁, hl₂, mc', .sub mc mc', by rw [Nat.sub_eq]; omega, rfl, rfl⟩
    . rintro ⟨w₁, w₂, hl₁, hl₂, mc₁, mc₂, rfl, rfl, rfl⟩; simp [N]
      have hr₁ := (ih₁ lbc mc₁ (mc₂ + lac)).mpr hl₁
      have hr₂ := (ih₂ (lbc + mc₁) mc₂ lac).mpr hl₂
      exact ⟨mc₁, by omega, by simp; exact hr₁, by simp; exact hr₂⟩
  | star r b ihᵣ ih =>
    simp only [N, sem]
    constructor
    . intro h
      induction mc using Nat.strongRecOn generalizing lbc with
      | _ mc ihm =>
        rw [NStar, Bool.or_eq_true] at h
        rcases h with h | h
        · exact .inUnit _ ((ih lbc mc lac).mp h)
        · rw [List.any_eq_true] at h
          obtain ⟨⟨k, hk⟩, _, h⟩ := h
          have hk := List.mem_range.mp hk
          simp only [Bool.and_eq_true] at h; obtain ⟨hr, hstar⟩ := h
          have hl := (ihᵣ lbc (k + 1) ((mc - (k + 1)) + lac)).mp hr
          have hs := ihm (mc - (k + 1)) (by omega) (lbc + (k + 1)) hstar
          exact star_help.inConcat _ _ _ hl hs ⟨k + 1, mc - (k + 1), by omega, rfl, rfl⟩
    . intro h
      unfold nullable star at h
      generalize hw : Word.right lbc mc lac [] = w at h
      induction h generalizing lbc mc with
      | inUnit _ hb => subst hw; rw [NStar, (ih lbc mc lac).mpr hb]; rfl
      | inConcat w₁ w₂ _ hl _ hwc ihs =>
        subst hw; obtain ⟨mc₁, mc₂, rfl, h₁, h₂⟩ := hwc; subst h₁
        have hstar := ihs (lbc + mc₁) mc₂ h₂.symm
        cases mc₁ with
        | zero => simpa using hstar
        | succ k =>
          rw [NStar, Bool.or_eq_true, List.any_eq_true]; right
          refine ⟨⟨k, List.mem_range.mpr (by omega)⟩, List.mem_attach _ _, ?_⟩
          simp only [Nat.add_sub_cancel_left, Bool.and_eq_true]
          exact ⟨(ihᵣ lbc (k + 1) (mc₂ + lac)).mpr hl, hstar⟩
  | lb r ih =>
    cases mc with
    | zero => simp only [N, nullable, sem, lookbehind]; simpa using ih 0 lbc lac
    | succ mc => simp [N, nullable, sem, lookbehind]
  | la r ih =>
    cases mc with
    | zero => simp only [N, nullable, sem, lookahead]; simpa using ih lbc lac 0
    | succ mc => simp [N, nullable, sem, lookahead]
  | lbStep r ih =>
    cases lbc with
    | zero => simp [N, nullable, sem, lbStep]
    | succ lbc => simp only [N, nullable, sem, lbStep]; exact ih lbc mc lac
  | mStep r ih =>
    cases mc with
    | zero => simp [N, nullable, sem, matchStep]
    | succ mc => simp only [N, nullable, sem, matchStep]; exact ih lbc mc lac
  | laStep r ih =>
    cases lac with
    | zero => simp [N, nullable, sem, laStep]
    | succ lac => simp only [N, nullable, sem, laStep]; exact ih lbc mc lac



theorem Tbl.build_get (n : Nat) (f : Nat → Nat → Nat → Bool) (lbc mc lac : Nat) : (Tbl.build n f).get lbc mc lac = (f lbc mc lac && decide (((lbc + mc : Nat) + lac : Nat) ≤ n)) := by
  unfold Tbl.get Tbl.build
  by_cases h : ((lbc + mc : Nat) + lac : Nat) ≤ n
  · have h1 : lbc < n + 1 := by omega
    have h2 : lac < n + 1 - lbc := by omega
    have h3 : mc < n + 1 - (lbc + lac : Nat) := by omega
    simp [h1, h2, h3, h]
  · simp [Array.getElem?_range, h]
    by_cases h1 : lbc < n + 1 <;> simp [h1]
    by_cases h2 : lac < n + 1 - lbc <;> simp [h2]
    have h3 : ¬ mc < n + 1 - (lbc + lac : Nat) := by omega
    simp [h3]

def starStep (fr fb : Nat → Nat → Nat → Bool) (s lac : Nat) (d : Array Bool) (mc : Nat) : Array Bool :=
  d.push (fb (s - mc) mc lac || (List.range mc).any fun k => fr (s - mc) (k + 1) ((mc - (k + 1)) + lac) && d.getD (mc - (k + 1)) false)

theorem starDiag_eq (fr fb : Nat → Nat → Nat → Bool) (s lac : Nat) : starDiag fr fb s lac = (List.range (s + 1)).foldl (starStep fr fb s lac) #[] := rfl

theorem starStep_fold (fr fb : Nat → Nat → Nat → Bool) (s lac m : Nat) (hm : m ≤ s + 1) :
    ((List.range m).foldl (starStep fr fb s lac) #[]).size = m ∧ ∀ j < m, ((List.range m).foldl (starStep fr fb s lac) #[])[j]? = some (NStar fr fb (s - j) j lac) := by
  induction m with
  | zero => simp
  | succ m ih =>
    obtain ⟨hsz, hget⟩ := ih (by omega)
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    generalize List.foldl (starStep fr fb s lac) #[] (List.range m) = d at hsz hget ⊢
    unfold starStep
    refine ⟨by simp [hsz], fun j hj => ?_⟩
    rw [Array.getElem?_push]
    by_cases hjm : j = m
    · subst hjm
      rw [if_pos hsz.symm, NStar]
      congr 1
      congr 1
      apply Bool.eq_iff_iff.mpr
      simp only [List.any_eq_true, List.mem_range, List.mem_attach, true_and, Bool.and_eq_true,
        Subtype.exists]
      have key : ∀ k : Nat, k < j → d.getD (j - (k + 1)) false = NStar fr fb ((s - j) + (k + 1)) (j - (k + 1)) lac := by
        intro k hk
        have he : (s - (j - (k + 1)) : Nat) = ((s - j) + (k + 1) : Nat) := by omega
        rw [Array.getD_eq_getD_getElem?, hget (j - (k + 1)) (by omega), Option.getD_some, he]
      constructor
      · rintro ⟨k, hk, h1, h2⟩; exact ⟨k, hk, h1, by rw [← key k hk]; exact h2⟩
      · rintro ⟨k, hk, h1, h2⟩; exact ⟨k, hk, h1, by rw [key k hk]; exact h2⟩
    · rw [if_neg (by omega)]
      exact hget j (by omega)

theorem starDiag_get (fr fb : Nat → Nat → Nat → Bool) (s lac mc : Nat) (h : mc ≤ s) :
    (starDiag fr fb s lac)[mc]? = some (NStar fr fb (s - mc) mc lac) := by
  rw [starDiag_eq]; exact (starStep_fold fr fb s lac (s + 1) (Nat.le_refl _)).2 mc (by omega)


theorem NStar_congr (fr fb gr gb : Nat → Nat → Nat → Bool) (n : Nat)
    (hr : ∀ a b c, ((a + b : Nat) + c : Nat) ≤ n → fr a b c = gr a b c)
    (hb : ∀ a b c, ((a + b : Nat) + c : Nat) ≤ n → fb a b c = gb a b c) :
    ∀ mc lbc lac, ((lbc + mc : Nat) + lac : Nat) ≤ n → NStar fr fb lbc mc lac = NStar gr gb lbc mc lac := by
  intro mc
  induction mc using Nat.strongRecOn with
  | _ mc ih =>
    intro lbc lac h
    rw [NStar, NStar, hb _ _ _ h]
    congr 1
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_eq_true, List.mem_attach, true_and, Bool.and_eq_true, Subtype.exists,
      List.mem_range]
    constructor
    · rintro ⟨k, hk, h1, h2⟩
      exact ⟨k, hk, by rw [← hr _ _ _ (by omega)]; exact h1,
        by rw [← ih _ (by omega) _ _ (by omega)]; exact h2⟩
    · rintro ⟨k, hk, h1, h2⟩
      exact ⟨k, hk, by rw [hr _ _ _ (by omega)]; exact h1,
        by rw [ih _ (by omega) _ _ (by omega)]; exact h2⟩

theorem nullability_correct₂ [DecidableEq α] (r : Expr α) (n : Nat) : ∀ lbc mc lac, ((lbc + mc : Nat) + lac : Nat) ≤ n → (NT r n).get lbc mc lac = N r lbc mc lac := by
  induction r with
  | empty => intro lbc mc lac h; simp [NT, N, Tbl.build_get]
  | unit => intro lbc mc lac h; simp [NT, N, Tbl.build_get, h]
  | top => intro lbc mc lac h; simp [NT, N, Tbl.build_get, h]
  | symbol _ => intro lbc mc lac h; simp [NT, N, Tbl.build_get]
  | plus r₁ r₂ ih₁ ih₂ => intro lbc mc lac h; simp [NT, N, Tbl.build_get, h, ih₁ _ _ _ h, ih₂ _ _ _ h]
  | intersection r₁ r₂ ih₁ ih₂ => intro lbc mc lac h; simp [NT, N, Tbl.build_get, h, ih₁ _ _ _ h, ih₂ _ _ _ h]
  | complement r₁ r₂ ih₁ ih₂ => intro lbc mc lac h; simp [NT, N, Tbl.build_get, h, ih₁ _ _ _ h, ih₂ _ _ _ h]
  | mult r₁ r₂ ih₁ ih₂ =>
    intro lbc mc lac h
    simp [NT, N, Tbl.build_get, h]; apply Bool.eq_iff_iff.mpr; simp [List.mem_range]
    constructor
    · intro ⟨k, hk, h1, h2⟩; exact ⟨k, hk, by rw [← ih₁ _ _ _ (by omega)]; exact h1, by rw [← ih₂ _ _ _ (by omega)]; exact h2⟩
    · intro ⟨k, hk, h1, h2⟩; exact ⟨k, hk, by rw [ih₁ _ _ _ (by omega)]; exact h1, by rw [ih₂ _ _ _ (by omega)]; exact h2⟩
  | star r b ihr ihb =>
    intro lbc mc lac h
    simp [NT, N, Tbl.build_get, h]
    have h1 : lac < n + 1 := by omega
    have h2 : (lbc + mc : Nat) < n + 1 - lac := by omega
    simp [h1, h2, starDiag_get _ _ _ _ _ (Nat.le_add_left mc lbc)]
    exact NStar_congr _ _ _ _ n ihr ihb mc lbc lac h
  | lb r ih =>
    intro lbc mc lac h
    cases mc with
    | zero =>
      have h' : (lbc + lac : Nat) ≤ n := by omega
      have hi := ih 0 lbc lac (by omega)
      simp [NT, N, Tbl.build_get, h', hi]
    | succ mc => simp [NT, N, Tbl.build_get]
  | la r ih =>
    intro lbc mc lac h
    cases mc with
    | zero =>
      have h' : (lbc + lac : Nat) ≤ n := by omega
      have hi := ih lbc lac 0 (by omega)
      simp [NT, N, Tbl.build_get, h', hi]
    | succ mc => simp [NT, N, Tbl.build_get]
  | lbStep r ih =>
    intro lbc mc lac h
    cases lbc with
    | zero => simp [NT, N, Tbl.build_get]
    | succ lbc =>
      have hi := ih lbc mc lac (by omega)
      simp [NT, N, Tbl.build_get, h, hi]
  | mStep r ih =>
    intro lbc mc lac h
    cases mc with
    | zero => simp [NT, N, Tbl.build_get]
    | succ mc =>
      have hi := ih lbc mc lac (by omega)
      simp [NT, N, Tbl.build_get, h, hi]
  | laStep r ih =>
    intro lbc mc lac h
    cases lac with
    | zero => simp [NT, N, Tbl.build_get]
    | succ lac =>
      have hi := ih lbc mc lac (by omega)
      simp [NT, N, Tbl.build_get, h, hi]

import Thesis.Syntax.Expressions
import Thesis.Semantics.NullabilityLaws

namespace Semilinear

open Expr StructuredWords Operators NullabilityLaws

/-! ## Representation -/

inductive Gen : List (Nat × Nat) → Nat → Nat → Prop
  | nil : Gen [] 0 0
  | cons {ps x y} (p : Nat × Nat) (c : Nat) :
      Gen ps x y → Gen (p :: ps) (c * p.1 + x) (c * p.2 + y)

/-- A linear set `base + ℕ·p₁ + … + ℕ·pₖ` of pairs `(mc, lac)`. -/
structure Linear where
  base : Nat × Nat
  periods : List (Nat × Nat)
deriving Repr

def Linear.Mem (L : Linear) (mc lac : Nat) : Prop :=
  ∃ x y, Gen L.periods x y ∧ mc = L.base.1 + x ∧ lac = L.base.2 + y

/-- A semilinear set: a finite union of linear sets. -/
abbrev SL := List Linear

def SL.Mem (S : SL) (mc lac : Nat) : Prop :=
  ∃ L ∈ S, L.Mem mc lac

/-! ## `Gen` lemmas -/

theorem gen_nil_iff : Gen [] x y ↔ x = 0 ∧ y = 0 := by
  constructor
  · intro h; cases h; exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩; exact .nil

theorem gen_cons_iff :
    Gen (p :: ps) x y ↔ ∃ c x' y', Gen ps x' y' ∧ x = c * p.1 + x' ∧ y = c * p.2 + y' := by
  constructor
  · intro h; cases h with
    | cons _ c h => exact ⟨c, _, _, h, rfl, rfl⟩
  · rintro ⟨c, x', y', h, rfl, rfl⟩; exact .cons p c h

theorem gen_zero : ∀ ps, Gen ps 0 0
  | [] => .nil
  | p :: ps => by simpa using Gen.cons p 0 (gen_zero ps)

/-- Keeping only the periods on the `lac = 0` axis and moving them onto the `mc = 0` axis
    is exactly the coordinate swap that lookahead performs. -/
theorem gen_la (ps : List (Nat × Nat)) (a b : Nat) :
    Gen ((ps.filter (·.2 == 0)).map fun p => (0, p.1)) a b ↔ a = 0 ∧ Gen ps b 0 := by
  induction ps generalizing a b with
  | nil => simp [gen_nil_iff]
  | cons p ps ih =>
    by_cases hp : p.2 = 0
    · simp only [List.filter_cons, hp, beq_self_eq_true, ite_true, List.map_cons, gen_cons_iff,
        ih, Nat.mul_zero, Nat.zero_add]
      constructor
      · rintro ⟨c, x', y', ⟨rfl, hg⟩, rfl, rfl⟩
        exact ⟨rfl, c, y', 0, hg, rfl, rfl⟩
      · rintro ⟨rfl, c, x', y', hg, rfl, hy⟩
        have : y' = 0 := by omega
        subst this
        exact ⟨c, 0, x', ⟨rfl, hg⟩, rfl, rfl⟩
    · have hpb : (p.2 == 0) = false := by simpa using hp
      simp only [List.filter_cons, hpb, Bool.false_eq_true, ite_false, ih, gen_cons_iff]
      constructor
      · rintro ⟨rfl, hg⟩
        exact ⟨rfl, 0, b, 0, hg, by simp, by simp⟩
      · rintro ⟨rfl, c, x', y', hg, rfl, hy⟩
        have hc : c * p.2 = 0 := by omega
        have hc : c = 0 := (Nat.mul_eq_zero.mp hc).resolve_right hp
        subst hc
        have : y' = 0 := by omega
        subst this
        exact ⟨rfl, by simpa using hg⟩

/-! ## Easy operations -/

def empty : SL := []

def unit : SL := [⟨(0, 0), [(0, 1)]⟩]

def top : SL := [⟨(0, 0), [(1, 0), (0, 1)]⟩]

def union (S R : SL) : SL := S ++ R

/-- Least relation closed under the star rule
    (`nullable_n_m_star`, read as an inductive definition). -/
inductive StarRel (r b : Nat → Nat → Prop) : Nat → Nat → Prop
  | base : b mc lac → StarRel r b mc lac
  | step : r mc₁ (mc₂ + lac) → StarRel r b mc₂ lac → StarRel r b (mc₁ + mc₂) lac

-- TODO: intersection of linear sets = solving `b₁ + P₁c₁ = b₂ + P₂c₂` over ℕ
-- (minimal solutions / Hilbert basis).
def inter (S R : SL) : SL := S.filter (λ p => )

-- TODO: semilinear complement construction.
def diff (S R : SL) : SL := sorry

-- TODO: relation composition; an intersection followed by a projection.
def concat (S R : SL) : SL := sorry

-- TODO: closed form of `R* ∘ B`. Open whether this stays semilinear for the relations
-- that `Expr` can produce (see the note at the end of the file).
def star (R B : SL) : SL := sorry

def la (S : SL) : SL :=
  S.filterMap fun L =>
    if L.base.2 = 0 then
      some ⟨(0, L.base.1), (L.periods.filter (·.2 == 0)).map fun p => (0, p.1)⟩
    else none

def lb (S : SL) : SL :=
  if S.any (·.base.2 == 0) then [⟨(0, 0), []⟩] else []

def mStep (S : SL) : SL := S.map fun L => { L with base := (L.base.1 + 1, L.base.2) }

def laStep (S : SL) : SL := S.map fun L => { L with base := (L.base.1, L.base.2 + 1) }



/-! ## Specifications of the easy operations -/

theorem mem_empty : ¬ empty.Mem a b := by
  simp [empty, SL.Mem]

theorem mem_unit : unit.Mem a b ↔ a = 0 := by
  simp only [unit, SL.Mem, List.mem_singleton, exists_eq_left, Linear.Mem, gen_cons_iff,
    gen_nil_iff]
  constructor
  · rintro ⟨x, y, ⟨c, x', y', ⟨rfl, rfl⟩, rfl, rfl⟩, rfl, rfl⟩; simp
  · rintro rfl; exact ⟨0, b, ⟨b, 0, 0, ⟨rfl, rfl⟩, by simp, by simp⟩, by simp, by simp⟩

theorem mem_top : top.Mem a b := by
  refine ⟨_, List.mem_singleton_self _, a, b, ?_, by simp, by simp⟩
  simpa using Gen.cons (1, 0) a (Gen.cons (0, 1) b .nil)

theorem mem_union : (union S R).Mem a b ↔ S.Mem a b ∨ R.Mem a b := by
  simp only [union, SL.Mem, List.mem_append]
  constructor
  · rintro ⟨L, hL | hL, h⟩
    · exact .inl ⟨L, hL, h⟩
    · exact .inr ⟨L, hL, h⟩
  · rintro (⟨L, hL, h⟩ | ⟨L, hL, h⟩)
    · exact ⟨L, .inl hL, h⟩
    · exact ⟨L, .inr hL, h⟩

theorem mem_mStep_zero : ¬ (mStep S).Mem 0 b := by
  simp only [mStep, SL.Mem, List.mem_map, Linear.Mem]
  rintro ⟨_, ⟨L, _, rfl⟩, x, y, _, h, _⟩
  simp at h; omega

theorem mem_mStep_succ : (mStep S).Mem (a + 1) b ↔ S.Mem a b := by
  simp only [mStep, SL.Mem, List.mem_map, Linear.Mem]
  constructor
  · rintro ⟨_, ⟨L, hL, rfl⟩, x, y, hg, ha, hb⟩
    exact ⟨L, hL, x, y, hg, by simp at ha; omega, hb⟩
  · rintro ⟨L, hL, x, y, hg, ha, hb⟩
    exact ⟨_, ⟨L, hL, rfl⟩, x, y, hg, by simp; omega, hb⟩

theorem mem_laStep_zero : ¬ (laStep S).Mem a 0 := by
  simp only [laStep, SL.Mem, List.mem_map, Linear.Mem]
  rintro ⟨_, ⟨L, _, rfl⟩, x, y, _, _, h⟩
  simp at h; omega

theorem mem_laStep_succ : (laStep S).Mem a (b + 1) ↔ S.Mem a b := by
  simp only [laStep, SL.Mem, List.mem_map, Linear.Mem]
  constructor
  · rintro ⟨_, ⟨L, hL, rfl⟩, x, y, hg, ha, hb⟩
    exact ⟨L, hL, x, y, hg, ha, by simp at hb; omega⟩
  · rintro ⟨L, hL, x, y, hg, ha, hb⟩
    exact ⟨_, ⟨L, hL, rfl⟩, x, y, hg, ha, by simp; omega⟩

theorem linear_mem_row_zero (L : Linear) (m : Nat) :
    L.Mem m 0 ↔ L.base.2 = 0 ∧ ∃ x, Gen L.periods x 0 ∧ m = L.base.1 + x := by
  constructor
  · rintro ⟨x, y, hg, hm, hy⟩
    have h1 : L.base.2 = 0 := by omega
    have h2 : y = 0 := by omega
    subst h2
    exact ⟨h1, x, hg, hm⟩
  · rintro ⟨h, x, hg, hm⟩
    exact ⟨x, 0, hg, hm, by omega⟩

theorem mem_la : (la S).Mem a b ↔ a = 0 ∧ S.Mem b 0 := by
  simp only [la, SL.Mem, List.mem_filterMap]
  constructor
  · rintro ⟨_, ⟨L, hL, hsome⟩, x, y, hg, ha, hb⟩
    by_cases h0 : L.base.2 = 0
    · simp only [h0, ite_true, Option.some.injEq] at hsome
      subst hsome
      obtain ⟨rfl, hg'⟩ := (gen_la _ _ _).mp hg
      simp only at ha hb
      exact ⟨by omega, L, hL, (linear_mem_row_zero L b).mpr ⟨h0, y, hg', by omega⟩⟩
    · simp [h0] at hsome
  · rintro ⟨rfl, L, hL, hm⟩
    obtain ⟨h0, x, hg, rfl⟩ := (linear_mem_row_zero L b).mp hm
    refine ⟨_, ⟨L, hL, by simp [h0]; rfl⟩, 0, x, (gen_la _ _ _).mpr ⟨rfl, hg⟩, rfl, rfl⟩

theorem mem_lb : (lb S).Mem a b ↔ a = 0 ∧ b = 0 ∧ ∃ m, S.Mem m 0 := by
  have key : (S.any (·.base.2 == 0) = true) ↔ ∃ m, S.Mem m 0 := by
    simp only [List.any_eq_true, beq_iff_eq, SL.Mem]
    constructor
    · rintro ⟨L, hL, h0⟩
      exact ⟨L.base.1, L, hL, (linear_mem_row_zero L _).mpr ⟨h0, 0, gen_zero _, rfl⟩⟩
    · rintro ⟨m, L, hL, hm⟩
      exact ⟨L, hL, ((linear_mem_row_zero L m).mp hm).1⟩
  unfold lb
  split
  · rename_i h
    simp only [SL.Mem, List.mem_singleton, exists_eq_left, Linear.Mem, gen_nil_iff]
    constructor
    · rintro ⟨x, y, ⟨rfl, rfl⟩, rfl, rfl⟩; exact ⟨rfl, rfl, key.mp h⟩
    · rintro ⟨rfl, rfl, _⟩; exact ⟨0, 0, ⟨rfl, rfl⟩, rfl, rfl⟩
  · rename_i h
    constructor
    · rintro ⟨_, hL, _⟩; simp at hL
    · rintro ⟨_, _, hm⟩; exact absurd (key.mpr hm) h

/-! ## Hard operations (specified only) -/



theorem mem_inter : (inter S R).Mem a b ↔ S.Mem a b ∧ R.Mem a b := sorry

theorem mem_diff : (diff S R).Mem a b ↔ S.Mem a b ∧ ¬ R.Mem a b := sorry

theorem mem_concat : (concat S R).Mem a b ↔
    ∃ mc₁ mc₂, a = mc₁ + mc₂ ∧ S.Mem mc₁ (mc₂ + b) ∧ R.Mem mc₂ b := sorry

theorem mem_star : (star R B).Mem a b ↔ StarRel R.Mem B.Mem a b := sorry


def NSym : Expr α → SL
  | .empty => empty
  | .unit => unit
  | .top => top
  | .symbol _ => empty
  | .plus r₁ r₂ => union (NSym r₁) (NSym r₂)
  | .intersection r₁ r₂ => inter (NSym r₁) (NSym r₂)
  | .complement r₁ r₂ => diff (NSym r₁) (NSym r₂)
  | .mult r₁ r₂ => concat (NSym r₁) (NSym r₂)
  | .star r b => star (NSym r) (NSym b)
  | .lb r => lb (NSym r)
  | .la r => la (NSym r)
  | .mStep r => mStep (NSym r)
  | .laStep r => laStep (NSym r)

theorem nullable_n_m_star_iff (l base : Lang α) (mc lac : Nat) :
    nullable_n_m (Operators.star base l) mc lac ↔
      StarRel (nullable_n_m l) (nullable_n_m base) mc lac := by
  constructor
  · intro h
    unfold nullable_n_m Operators.star at h
    generalize hw : Word.right mc lac [] = w at h
    induction h generalizing mc with
    | inUnit _ hb => subst hw; exact .base hb
    | inConcat w₁ w₂ _ hl _ hwc ih =>
      subst hw
      obtain ⟨mc₁, mc₂, rfl, rfl, rfl⟩ := hwc
      exact .step hl (ih mc₂ rfl)
  · intro h
    induction h with
    | base hb => exact .inUnit _ hb
    | step hl _ ih => exact .inConcat _ _ _ hl ih ⟨_, _, rfl, rfl, rfl⟩

theorem NSym_correct [DecidableEq α] (r : Expr α) :
    ∀ mc lac, (NSym r).Mem mc lac ↔ nullable_n_m (sem r) mc lac := by
  induction r with
  | empty => intro _ _; simp [NSym, sem, mem_empty, nullable_n_m_empty]
  | unit => intro _ _; simp [NSym, sem, mem_unit, nullable_n_m, Operators.unit]
  | top => intro _ _; simp [NSym, sem, mem_top, nullable_n_m_top]
  | symbol x => intro _ _; simp [NSym, sem, mem_empty, nullable_n_m_symb]
  | plus r₁ r₂ ih₁ ih₂ =>
    intro _ _; simp [NSym, sem, mem_union, nullable_n_m_union, ih₁, ih₂]
  | intersection r₁ r₂ ih₁ ih₂ =>
    intro _ _; simp [NSym, sem, mem_inter, nullable_n_m_intersection, ih₁, ih₂]
  | complement r₁ r₂ ih₁ ih₂ =>
    intro _ _; simp [NSym, sem, mem_diff, nullable_n_m_diff, ih₁, ih₂]
  | mult r₁ r₂ ih₁ ih₂ =>
    intro _ _; simp [NSym, sem, mem_concat, nullable_n_m_concat, ih₁, ih₂]
  | star r b ih₁ ih₂ =>
    intro mc lac
    have h₁ : (NSym r).Mem = nullable_n_m (sem r) := funext fun _ => funext fun _ => propext (ih₁ _ _)
    have h₂ : (NSym b).Mem = nullable_n_m (sem b) := funext fun _ => funext fun _ => propext (ih₂ _ _)
    simp only [NSym, sem, mem_star, h₁, h₂, nullable_n_m_star_iff]
  | lb r ih =>
    intro _ _; simp [NSym, sem, mem_lb, nullable_n_m_lookbehind, ih]
  | la r ih =>
    intro _ _; simp [NSym, sem, mem_la, nullable_n_m_lookahead, ih]
  | mStep r ih =>
    intro mc _
    cases mc with
    | zero => simp [NSym, sem, mem_mStep_zero, nullable_n_m, matchStep]
    | succ mc => simp [NSym, sem, mem_mStep_succ, nullable_n_m_matchStep, ih]
  | laStep r ih =>
    intro _ lac
    cases lac with
    | zero => simp [NSym, sem, mem_laStep_zero, nullable_n_m, LAStep]
    | succ lac => simp [NSym, sem, mem_laStep_succ, nullable_n_m_LAStep, ih]

end Semilinear

import Thesis.Semantics.StructuredWords
import Thesis.Semantics.Operators
import Thesis.Semantics.Derivatives

namespace DerLaws

open StructuredWords
open Operators

-- Proposition 3.4.1 (Derivative laws for structured languages).

-- ======== DER ==========
theorem der_empty (a : α) : der a ∅ ≐ ∅ := by
  intro w
  match w with
  | Sum.inl (xs, ys, zs) => simp [der, empty]
  | Sum.inr (Sum.inl (n, (y, ys), zs)) => cases n <;> simp [der, empty]
  | Sum.inr (Sum.inr (n, m, zs)) => cases n <;> cases m <;> simp [der, empty]

theorem der_unit (a : α) : der a I ≐ ∅ := by
  intro w
  match w with
  | Sum.inl (xs, ys, zs) => simp [der, empty]
  | Sum.inr (Sum.inl (n, (y, ys), zs)) => cases n <;> simp [der, unit, empty]
  | Sum.inr (Sum.inr (n, m, zs)) => cases n <;> cases m <;> simp [der, unit, empty]

theorem der_top (a : α): (der a T) ≐ (matchStep T // LAStep T) := by
  intro w
  match w with
  | Sum.inl (xs, ys, zs) => simp [der, complement, matchStep]
  | Sum.inr (Sum.inl (n, (y, ys), zs)) => cases n <;> simp [der, matchStep, LAStep, complement, top]
  | Sum.inr (Sum.inr (n, m, zs)) => cases n <;> cases m <;> simp [der, matchStep, LAStep, complement, top]


theorem der_symb_match (a b: α) (h : a = b) : der b (#a) ≐ (matchStep I // LAStep I) := by
  intro w
  match w with
  | Sum.inl (xs, ys, zs) => simp [der, complement, LAStep, matchStep]
  | Sum.inr (Sum.inl (n, (y, ys), zs)) => cases n <;> simp [der, matchStep, LAStep, complement, symb, unit]
  | Sum.inr (Sum.inr (n, m, zs)) => cases n <;> cases m <;> simp [der, symb, complement, matchStep, unit, LAStep, h]

theorem der_symb_no_match (a b: α) (h : ¬ (a = b)) : der b (#a) ≐ ∅ := by
  intro w
  match w with
  | Sum.inl (xs, ys, zs) => simp [der, empty]
  | Sum.inr (Sum.inl (n, (y, ys), zs)) => cases n <;> simp [der, symb, empty]
  | Sum.inr (Sum.inr (n, m, zs)) => cases n <;> cases m <;> simp [der, symb, empty, h]

theorem der_union (a : α) (k l : Lang α): der a (k ∪ l) ≐ (der a k) ∪ (der a l) := by
  intro w
  match w with
  | Sum.inl (xs, ys, zs) => simp [der, union]
  | Sum.inr (Sum.inl (n, (y, ys), zs)) => cases n <;> simp [der, union]
  | Sum.inr (Sum.inr (n, m, zs)) => cases n <;> cases m <;> simp [der, union]

theorem der_intersection (a : α) (k l : Lang α): der a (k ∩ l) ≐ (der a k) ∩ (der a l) := by
  intro w
  match w with
  | Sum.inl (xs, ys, zs) => simp [der, intersection]
  | Sum.inr (Sum.inl (n, (y, ys), zs)) => cases n <;> simp [der, intersection]
  | Sum.inr (Sum.inr (n, m, zs)) => cases n <;> cases m <;> simp [der, intersection]

theorem der_complement (a : α) (k l : Lang α): der a (k // l) ≐ ((der a k) // (der a l)) := by
  intro w
  match w with
  | Sum.inl (xs, ys, zs) => simp [der, complement]
  | Sum.inr (Sum.inl (n, (y, ys), zs)) => cases n <;> simp [der, complement]
  | Sum.inr (Sum.inr (n, m, zs)) => cases n <;> cases m <;> simp [der, complement]

theorem der_concat (a : α) (k l : Lang α) :
  der a (concat k l) ≐  ((der a k) • (derLB a l)) ∪ ((derLA a k) • (der a l)) := by
  intro w
  match w with
  | Sum.inl ((x, xs), ys, zs) =>
    constructor
    . intro h; simp [der] at h
    . intro h
      cases h with
      | inl h => obtain ⟨w₁, _, hk, _, ⟨_, _, _, _, _⟩⟩ := h; subst w₁; simp [der] at hk
      | inr h => obtain ⟨w₁, _, hk, _, ⟨_, _, _, _, _⟩⟩ := h; subst w₁; simp [derLA] at hk
  | Sum.inr (Sum.inl (n, (y, ys), zs)) =>
    constructor
    . intro h
      cases n with
      | zero => simp [der] at h
      | succ n =>
        obtain ⟨w₁, w₂, hk, hl, pref, suff, hys, h⟩ := h
        cases h with
        | inl h =>
          obtain ⟨_, _, _⟩ := h; subst w₁; left
          cases pref with
          | nil =>
            simp at hys; subst suff; exact ⟨Sum.inr (Sum.inr (n.succ, 0, y :: ys ++ zs)), Sum.inr (Sum.inl (0, (y, ys), zs)), hk, hl, [], ys, rfl, Or.inr ⟨n.succ, 0, 0, rfl, rfl, rfl⟩⟩
          | cons u us =>
            simp at hys; rw [hys.1.symm, hys.2.symm]; exact ⟨Sum.inr (Sum.inl (.succ n, (u, us), suff ++ zs)), Sum.inl ((u, us), suff, zs), hk, hl, us, suff, rfl, Or.inl ⟨ rfl, rfl⟩⟩
        | inr h =>
          obtain ⟨n₁, n₂, m₁, hn, _, _⟩ := h; subst w₁ w₂ n; right
          exact ⟨Sum.inr (Sum.inr (n₁, m₁.succ, y :: ys ++ zs)), Sum.inr (Sum.inl (n₂.succ, (y, ys), zs)), hk, hl, [], ys, rfl, Or.inr ⟨n₁, n₂.succ, m₁.succ, rfl, rfl, rfl⟩⟩
    . intro h
      cases n with
      | zero =>
        cases h with
        | inl h =>
          obtain ⟨w₁, _, hk, _, _, _, _, h⟩ := h;
          cases h with
          | inl h => obtain ⟨_, _⟩ := h; subst w₁; simp [der] at hk
          | inr h => obtain ⟨_, _, _, hn, _, _⟩ := h; subst w₁; simp at hn; simp [hn, der] at hk
        | inr h =>
          obtain ⟨w₁, w₂, hk, hl, pref, suff, hys, h⟩ := h
          cases h with
          | inl h => obtain ⟨_, _⟩ := h; subst w₁; simp [derLA] at hk
          | inr h => obtain ⟨_, _, _, hn, _, _⟩ := h; subst w₂; simp at hn; simp [hn, der] at hl
      | succ n =>
        cases h with
        | inl h =>
          obtain ⟨w₁, w₂, hk, hl, pref, suff, hys, h⟩ := h
          cases h with
          | inl h =>
            obtain ⟨_, _⟩ := h; subst w₁ w₂ ys; exact ⟨Sum.inr (Sum.inl (n, (a, y :: pref), suff ++ zs)), Sum.inl ((a, y :: pref), suff, zs), hk, hl, y :: pref, suff, rfl, Or.inl ⟨rfl, rfl⟩⟩
          | inr h =>
            obtain ⟨n₁, n₂, m₁, hn, _, _⟩ := h; subst w₁ w₂;
            cases m₁ with
            | zero =>
              cases n₁ with
              | zero => simp [der] at hk
              | succ n₁ =>
                cases n₂ with
                | zero => simp at hn; subst n₁; exact ⟨Sum.inr (Sum.inl (n, (a, []), y :: (ys ++ zs))), Sum.inl ((a, []), y :: ys, zs), hk, hl, [], y :: ys, rfl, Or.inl ⟨rfl, rfl⟩⟩
                | succ n₂ => simp [derLB] at hl
            | succ m₁ => simp [der] at hk
        | inr h =>
          obtain ⟨w₁, w₂, hk, hl, pref, suff, hys, h⟩ := h;
          cases h with
          | inl h => simp [h, derLA] at hk
          | inr h =>
            obtain ⟨n₁, n₂, m₁, hn, _, _⟩ := h; subst w₁ w₂
            cases m₁ with
            | zero => simp [derLA] at hk
            | succ m₁ =>
              cases n₁ with
              | zero =>
                cases n₂ with
                | zero => simp [der] at hl
                | succ n₂ => simp at hn; subst n₂; exact ⟨Sum.inr (Sum.inr (0, m₁, a :: y :: ys ++ zs)), Sum.inr (Sum.inl (n, (a, y :: ys), zs)), hk, hl, y :: ys, [], by simp, Or.inr ⟨0, n, m₁, by simp, rfl, rfl⟩⟩
              | succ n₁ =>
                cases n₂ with
                | zero => simp [der] at hl
                | succ n₂ =>
                  refine ⟨Sum.inr (Sum.inr (n₁ + 1, m₁, a :: y :: ys ++ zs)), Sum.inr (Sum.inl (n₂, (a, y :: ys), zs)), hk, hl, y :: pref, suff, by simp [hys], Or.inr ⟨n₁.succ, n₂, m₁, ?_,rfl, rfl⟩⟩
                  sorry
  | Sum.inr (Sum.inr (n, m, zs)) =>
    cases m with
    | zero =>
      constructor
      . intro h
        cases n with
        | zero => simp [der] at h
        | succ n =>
          obtain ⟨w₁, w₂, hk, hl, pref, suff, hys, h⟩ := h; simp at hys; obtain ⟨_, _⟩ := hys; subst pref suff
          cases h with
          | inl h => obtain ⟨_, _⟩ := h ; subst w₁ w₂; left; exact ⟨Sum.inr (Sum.inr (n.succ, 0, [] ++ zs)), Sum.inr (Sum.inr (0, 0, zs)), hk, hl, n.succ, 0, 0, rfl, rfl, rfl⟩
          | inr h =>
            obtain ⟨n₁, n₂, m₁, hn, _, _⟩ := h; subst w₁ w₂ n; right; exact ⟨Sum.inr (Sum.inr (n₁, m₁.succ, zs)), Sum.inr (Sum.inr (n₂.succ, 0, zs)), hk, hl, n₁, n₂.succ, m₁.succ, rfl, by simp, rfl⟩
      . intro h
        cases n with
        | zero =>
          cases h with
          | inl h => obtain ⟨w₁, _, hk, _, n₁, _, _, hn, _, _⟩ := h; simp at hn; obtain ⟨_, _⟩ := hn; subst w₁ n₁; simp [der] at hk
          | inr h =>
            obtain ⟨w₁, w₂, hk, hl, n₁, n₂, m₁, hn, _, _⟩ := h; simp at hn; obtain ⟨_, _⟩ := hn; subst w₁ w₂ n₁ n₂;
            cases m₁ with
            | zero => simp [derLA] at hk
            | succ m₁ => simp [der] at hl
        | succ n =>
          cases h with
          | inl h =>
            obtain ⟨w₁, w₂, hk, hl, n₁, n₂, m₁, hn, _, _⟩ := h; subst w₁ w₂;
            cases m₁ with
            | zero =>
              cases n₁ with
              | zero => simp [der] at hk
              | succ n₁ =>
                cases n₂ with
                | zero => simp at hn; subst n₁; exact ⟨Sum.inr (Sum.inl (n, (a, []), zs)), Sum.inl ((a, []), [], zs), hk, hl, [], [], rfl, Or.inl ⟨rfl, rfl⟩⟩
                | succ n₂ => simp [derLB] at hl
            | succ m₁ => simp [der] at hk
          | inr h =>
            obtain ⟨w₁, w₂, hk, hl, n₁, n₂, m₁, hn, _, _⟩ := h; subst w₁ w₂;
            cases m₁ with
            | zero => simp [derLA] at hk
            | succ m₁ =>
              cases n₂ with
              | zero => simp [der] at hl
              | succ n₂ =>
                refine ⟨Sum.inr (Sum.inr (n₁, m₁, a :: zs)), Sum.inr (Sum.inl (n₂, (a, []), zs)), by simp [derLA] at hk; exact hk, hl, [], [], rfl, Or.inr ⟨n₁, n₂, m₁, ?_, rfl, rfl⟩⟩
                sorry
    | succ m =>
      constructor
      . simp [der]
      . intro h
        cases h with
        | inl h => obtain ⟨w₁, _, hk, _, _, _, _, _, _, _⟩ := h; subst w₁; simp [Nat.add_comm, der] at hk
        | inr h => obtain ⟨_, w₂, _, hl, _, _, _, _, _, _⟩ := h; subst w₂; simp [der] at hl
/-
theorem der_star (a : α) (l : Lang α) : der a (l*) ≐ (der a l) • (l*) := by
  intro w
  match w with
  | Sum.inl ((hd, tl), v) =>
    constructor
    · simp [der]
      intro h
      suffices ∀ w1, star_help l w1 →
          ∀ hd' tl' v', w1 = Sum.inl ((a, hd' :: tl'), v') →
            concat (der a l) (star l) (Sum.inl ((hd', tl'), v')) by
        cases h with
        | inConcat x y w hx hy hc =>
          exact this _ (star_help.inConcat x y _ hx hy hc) hd tl v rfl
      intro w1 h1
      induction h1 with
      | inUnit _ _ => intro _ _ _ hw; nomatch hw
      | inConcat x y w hx hy hc ih =>
        intro hd' tl' v' hw
        subst hw
        cases hc with
        | inl hc =>
          obtain ⟨_, _, y_sub⟩ := hc
          exact ih hd' tl' v' y_sub
        | inr hc =>
          cases hc with
          | inl hc =>
            obtain ⟨x_eq, y_eq⟩ := hc
            subst x_eq
            exact ⟨Sum.inl ((hd', tl'), v'), Sum.inr (0, v'), hx, star_help.inUnit 0 v',
              Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
          | inr hc =>
            obtain ⟨xs, z, zs, htl, x_sub, y_sub⟩ := hc
            cases xs with
            | nil =>
              simp at htl; obtain ⟨hz, hzs⟩ := htl
              rw [hz, hzs] at x_sub y_sub
              refine ⟨Sum.inr (0, hd' :: tl' ++ v'), y, (by rw [x_sub] at hx; exact hx), hy, Or.inl ⟨0, rfl, y_sub⟩⟩
            | cons xhd xtl =>
              simp at htl; obtain ⟨hhd', htl'⟩ := htl
              refine ⟨Sum.inl ((hd', xtl), z :: zs ++ v'), y, (by rw [x_sub, hhd'] at hx; exact hx), hy, Or.inr (Or.inr ⟨xtl, z, zs, htl', rfl, y_sub⟩)⟩
    · simp [der]
      intro h
      obtain ⟨x, y, hx, hy, hc⟩ := h
      cases hc with
      | inl hc =>
        obtain ⟨n, x_sub, y_sub⟩ := hc
        cases n with
        | succ n => simp [x_sub, der] at hx
        | zero =>
          exact star_help.inConcat (l := l) (Sum.inl ((a, []), hd :: tl ++ v)) y (Sum.inl ((a, hd :: tl), v)) (by rw [x_sub] at hx; exact hx) hy (Or.inr (Or.inr ⟨[], hd, tl, rfl, rfl, y_sub⟩))
      | inr hc =>
        cases hc with
        | inl hc =>
          obtain ⟨x_sub, y_sub⟩ := hc
          exact star_help.inConcat (l := l) (Sum.inl ((a, hd :: tl), v)) y (Sum.inl ((a, hd :: tl), v)) (by rw [x_sub] at hx; exact hx) hy (Or.inr (Or.inl ⟨rfl, y_sub⟩))
        | inr hc =>
          obtain ⟨xs, z, zs, htl, x_sub, y_sub⟩ := hc
          cases xs with
          | nil =>
            subst htl
            exact star_help.inConcat (l := l) (Sum.inl ((a, [hd]), z :: zs ++ v)) y (Sum.inl ((a, hd :: z :: zs), v)) (by rw [x_sub] at hx; exact hx) hy (Or.inr (Or.inr ⟨[hd], z, zs, rfl, rfl, y_sub⟩))
          | cons xhd xtl =>
            subst htl
            exact star_help.inConcat (l := l) (Sum.inl ((a, hd :: xhd :: xtl), z :: zs ++ v)) y (Sum.inl ((a, hd :: xhd :: xtl ++ z :: zs), v)) (by rw [x_sub] at hx; exact hx) hy (Or.inr (Or.inr ⟨hd :: xhd :: xtl, z, zs, rfl, rfl, y_sub⟩))
  | Sum.inr (n, v) =>
    cases n with
    | zero =>
      constructor
      · simp [der]
        intro h
        suffices ∀ w' (h' : star_help l w'), w' = Sum.inl ((a, []), v) → concat (der a l) (star l) (Sum.inr (0, v)) by
          exact this _ h rfl
        intro w' h' w'_sub
        induction h' with
        | inUnit n y => cases w'_sub
        | inConcat x y w hx hy hc ih =>
          subst w'_sub
          cases hc with
          | inl hc =>
            obtain ⟨_, _, y_eq⟩ := hc
            exact ih y_eq
          | inr hc =>
            cases hc with
            | inl hc =>
              obtain ⟨x_sub, _⟩ := hc
              exact ⟨Sum.inr (0, v), Sum.inr (0, v), (by rw [x_sub] at hx; exact hx), star_help.inUnit 0 v, ⟨0, rfl, rfl⟩⟩
            | inr hc =>
              obtain ⟨xs, _, _, htl, _, _⟩ := hc
              cases xs <;> simp at htl
      · intro h
        obtain ⟨x, y, hx, hy, ⟨n', x_sub, y_sub⟩⟩ := h
        subst x_sub y_sub
        cases n' with
        | zero => exact star_help.inConcat (l := l) (Sum.inl ((a, []), v)) (Sum.inr (0, v)) (Sum.inl ((a, []), v)) hx hy (Or.inr (Or.inl ⟨rfl, rfl⟩))
        | succ k => simp [der] at hx
    | succ n =>
      simp [der]
      intro h
      obtain ⟨x, _, hx, _, ⟨_, x_sub, _⟩⟩ := h
      rw [x_sub] at hx; simp [der] at hx

 -/

theorem der_lb (a : α) (l : Lang α) : der a (lb l) ≐ ∅  := by
  intro w
  match w with
  | Sum.inl (xs, ys, zs) => simp [der, empty]
  | Sum.inr (Sum.inl (n, (y, ys), zs)) => cases n <;> simp [der, lb, empty]
  | Sum.inr (Sum.inr (n, m, zs)) => cases n <;> cases m <;> simp [der, lb, empty]

theorem der_la (a : α) (l : Lang α) : der a (la l) ≐ ∅  := by
  intro w
  match w with
  | Sum.inl (xs, ys, zs) => simp [der, empty]
  | Sum.inr (Sum.inl (n, (y, ys), zs)) => cases n <;> simp [der, la, empty]
  | Sum.inr (Sum.inr (n, m, zs)) => cases n <;> cases m <;> simp [der, la, empty]

theorem der_matchStep (a : α) (l : Lang α) : der a (matchStep l) ≐ matchStep (der a l) := by
  intro w
  match w with
  | Sum.inl (xs, ys, zs) => simp [der, matchStep]
  | Sum.inr (Sum.inl (n, (y, ys), zs)) =>
    cases n with
    | zero => simp [der, matchStep]
    | succ n => cases n <;> simp [der, matchStep]
  | Sum.inr (Sum.inr (n, m, zs)) =>
    cases n with
    | zero => simp [der, matchStep]
    | succ n => cases n <;> cases m <;> simp [der, matchStep]

theorem der_LAStep (a : α) (l : Lang α) : der a (LAStep l) ≐ ∅ := by
  intro w
  match w with
  | Sum.inl (xs, ys, zs) => simp [der, empty]
  | Sum.inr (Sum.inl (n, (y, ys), zs)) => cases n <;> simp [der, LAStep, empty]
  | Sum.inr (Sum.inr (n, m, zs)) => cases n <;> cases m <;> simp [der, LAStep, empty]


-- ========= DERLA ============
theorem derLA_empty (a : α) : derLA a ∅ ≐ ∅ := by
  intro w
  cases w with
  | inl w => cases w with | mk u v => cases u with | mk hd tl => simp [derLA, empty]
  | inr w =>
    match w with
    | Sum.inl (_, _, _) => simp [derLA, empty]
    | Sum.inr (n, m, zs) => cases m <;> simp [derLA, empty]

theorem derLA_unit (a : α) : derLA a I ≐ LAStep I := by
  intro w
  cases w with
  | inl w => cases w with | mk u v => cases u with | mk hd tl => simp [LAStep, derLA]
  | inr w =>
    match w with
    | Sum.inl (_, _, _) => simp [derLA, LAStep]
    | Sum.inr (n, m, zs) => cases m <;> simp [derLA, LAStep, unit]

theorem derLA_top (a : α) : derLA a T ≐ LAStep T := by
  intro w
  cases w with
  | inl w => cases w with | mk u v => cases u with | mk hd tl => simp [derLA, LAStep]
  | inr w =>
    match w with
    | Sum.inl (_, _, _) => simp [derLA, LAStep]
    | Sum.inr (n, m, zs) => cases m <;> simp [derLA, LAStep, top]

theorem derLA_symb (a b : α) : derLA b (#a) ≐ ∅ := by
  intro w
  cases w with
  | inl w => cases w with | mk u v => cases u with | mk hd tl => simp [empty, derLA]
  | inr w =>
    match w with
    | Sum.inl (_, _, _) => simp [derLA, empty]
    | Sum.inr (n, m, zs) => cases m <;> simp [derLA, empty, symb]

theorem derLA_union (a : α) (k l : Lang α) : derLA a (k ∪ l) ≐ derLA a k ∪ derLA a l := by
  intro w
  cases w with
  | inl w => cases w with | mk u v => cases u with | mk hd tl => simp [union, derLA]
  | inr w =>
    match w with
    | Sum.inl (_, _, _) => simp [union, derLA]
    | Sum.inr (n, m, zs) => cases m <;> simp [union, derLA]

theorem derLA_intersection (a : α) (k l : Lang α): derLA a (k ∩ l) ≐ (derLA a k) ∩ (derLA a l) := by
  intro w
  cases w with
  | inl w => cases w with | mk u v => cases u with | mk hd tl => simp [derLA, intersection]
  | inr w =>
    match w with
    | Sum.inl (_, _, _) => simp [derLA, intersection]
    | Sum.inr (n, m, zs) => cases m <;> simp [derLA, intersection]

theorem derLA_complement (a : α) (k l : Lang α): derLA a (k // l) ≐ ((derLA a k) // (derLA a l)) := by
  intro w
  cases w with
  | inl w => cases w with | mk u v => cases u with | mk hd tl => simp [derLA, complement]
  | inr w =>
    match w with
    | Sum.inl (_, _, _) => simp [derLA, complement]
    | Sum.inr (n, m, zs) => cases m <;> simp [derLA, complement]

theorem derLA_concat (a : α) (k l : Lang α) : derLA a (k • l) ≐ derLA a k • derLA a l := by
  intro w
  match w with
  | Sum.inl ((x, xs), ys, zs) =>
    constructor
    . intro h; simp [derLA] at h
    . intro h; obtain ⟨w₁, _, hk, _, _, _, _, _, _⟩ := h; subst w₁; simp [derLA] at hk
  | Sum.inr (Sum.inl (n, (y, ys), zs)) =>
    constructor
    . intro h; simp [derLA] at h
    . intro h; obtain ⟨w₁, w₂, hk, hl, _, _, _, h⟩ := h;
      cases h with
      | inl h => obtain ⟨_, _⟩ := h; subst w₁; simp [derLA] at hk
      | inr h => obtain ⟨_, _, _, _, _, _⟩ := h; subst w₂; simp [derLA] at hl
  | Sum.inr (Sum.inr (n, m, zs)) =>
    constructor
    . intro h
      cases m with
      | zero => simp [derLA] at h
      | succ m =>
        obtain ⟨w₁, w₂, hk, hl, n₁, n₂, m₁, _, _, _⟩ := h; subst w₁ w₂ n
        refine ⟨Sum.inr (Sum.inr (n₁, (m + m₁).succ , zs)), Sum.inr (Sum.inr (n₂, m.succ, zs)), hk, hl, n₁, n₂, m₁, rfl, ?_, rfl⟩
        sorry
    . intro h
      obtain ⟨w₁, w₂, hk, hl, n₁, n₂, m₁', _, _, _⟩ := h; subst w₁ w₂ n
      cases m with
      | zero => simp [derLA] at hl
      | succ m =>
        refine ⟨Sum.inr (Sum.inr (n₁, m + m₁', a :: zs)), Sum.inr (Sum.inr (n₂, m, a :: zs)), ?_, hl, n₁, n₂, m₁', rfl, rfl, rfl⟩
        sorry
/-
theorem derLA_star (a : α) (l : Lang α) : derLA a (l*) ≐ ▹I ∪ derLA a l := by
  intro w
  match w with
  | Sum.inl w => simp [derLA, union, step]
  | Sum.inr (n, v) =>
    cases n with
    | zero => simp [derLA, union, step]
    | succ n =>
      constructor
      · intro h
        left
        refine ⟨n, rfl, ?_⟩
        trivial
      · intro _
        exact star_help.inUnit (l := l) n (a :: v)
 -/

theorem derLA_la (a : α) (l : Lang α) : derLA a (la l) ≐ la (der a l) := by
  intro w
  cases w with
  | inl w =>
    cases w with | mk u v =>
      cases u with | mk hd tl => simp [derLA, la]
  | inr w =>
    match w with
    | Sum.inl (_, _, _) => simp [derLA, la]
    | Sum.inr (n, m, zs) =>
      cases m with
      | zero =>  cases n <;> cases zs <;> simp [derLA, la, der]
      | succ m => cases n <;> cases zs <;> simp [derLA, la, der]

theorem derLA_matchStep (a : α) (l : Lang α) : derLA a (matchStep l) ≐ matchStep (derLA a l) := by
  intro w
  cases w with
  | inl w =>
    cases w with | mk u v =>
      cases u with | mk hd tl => simp [matchStep, derLA]
  | inr w =>
    match w with
    | Sum.inl (n, ys, zs) => cases n <;> simp [derLA, matchStep]
    | Sum.inr (n, m, zs) => cases m <;> cases n <;> cases zs <;> simp [derLA, matchStep]

theorem derLA_LAStep (a : α) (l : Lang α) : derLA a (LAStep l) ≐ LAStep (derLA a l) := by
  intro w
  cases w with
  | inl w =>
    cases w with | mk u v =>
      cases u with | mk hd tl => simp [derLA, LAStep]
  | inr w =>
    match w with
    | Sum.inl (n, ys, zs) => cases n <;> simp [derLA, LAStep]
    | Sum.inr (n, m, zs) =>
      cases m with
      | zero => cases n <;> cases zs <;> simp [derLA,LAStep]
      | succ m => cases m <;> cases n <;> cases zs <;> simp [derLA,LAStep]

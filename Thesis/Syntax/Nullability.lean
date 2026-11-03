import Thesis.Syntax.Expressions
import Thesis.Semantics.«2_Operators»

open Expr

def NStar (fr fb : Nat → Nat → Nat → Bool) (lbc mc lac : Nat) : Bool :=
  fb lbc mc lac || (List.range mc).attach.any fun ⟨k, _⟩ =>
    fr lbc (k + 1) ((mc - (k + 1)) + lac) && NStar fr fb (lbc + (k + 1)) (mc - (k + 1)) lac
termination_by mc
decreasing_by rename_i hk; have := List.mem_range.mp hk; omega

def N {α} (r : Expr α) (lbc mc lac : Nat) : Bool :=
  match r with
  | .empty => false
  | .unit => mc == 0
  | .top => true
  | .symbol _ => false
  | .plus r₁ r₂ => N r₁ lbc mc lac || N r₂ lbc mc lac
  | .intersection r₁ r₂ => N r₁ lbc mc lac && N r₂ lbc mc lac
  | .complement r₁ r₂ => N r₁ lbc mc lac && !N r₂ lbc mc lac
  | .mult r₁ r₂ => (List.range (mc + 1)).any fun mc₁ =>
      N r₁ lbc mc₁ ((mc - mc₁) + lac) && N r₂ (lbc + mc₁) (mc - mc₁) lac
  | .star r b => NStar (N r) (N b) lbc mc lac
  | .lb r => mc == 0 && N r 0 lbc lac
  | .la r => mc == 0 && N r lbc lac 0
  | .lbStep r => match lbc with | 0 => false | lbc + 1 => N r lbc mc lac
  | .mStep r => match mc with | 0 => false | mc + 1 => N r lbc mc lac
  | .laStep r => match lac with | 0 => false | lac + 1 => N r lbc mc lac


abbrev Tbl := Array (Array (Array Bool))

def Tbl.get (t : Tbl) (lbc mc lac : Nat) : Bool :=
  (t[lbc]? >>= (·[lac]?) >>= (·[mc]?)).getD false

instance : Membership (Nat × Nat × Nat) Tbl where
  mem t p := t.get p.1 p.2.1 p.2.2 = true

def Tbl.build (n : Nat) (f : Nat → Nat → Nat → Bool) : Tbl :=
  (Array.range (n + 1)).map fun lbc =>
    (Array.range ((n + 1) - lbc)).map fun lac =>
      (Array.range (Nat.sub (n + 1) (lbc + lac))).map fun mc => f lbc mc lac


def starDiag (fr fb : Nat → Nat → Nat → Bool) (s lac : Nat) : Array Bool :=
  (List.range (s + 1)).foldl (init := #[]) fun d mc =>
    let lbc := s - mc
    d.push (fb lbc mc lac || (List.range mc).any fun k =>
      fr lbc (k + 1) ((mc - (k + 1)) + lac) && d.getD (mc - (k + 1)) false)

def NT (r : Expr α) (n : Nat) : Tbl :=
  match r with
  | .empty => Tbl.build n fun _ _ _ => false
  | .unit => Tbl.build n fun _ mc _ => mc == 0
  | .top => Tbl.build n fun _ _ _ => true
  | .symbol _ => Tbl.build n fun _ _ _ => false
  | .plus r₁ r₂ =>
    let t₁ := NT r₁ n; let t₂ := NT r₂ n
    Tbl.build n fun lbc mc lac => t₁.get lbc mc lac || t₂.get lbc mc lac
  | .intersection r₁ r₂ =>
    let t₁ := NT r₁ n; let t₂ := NT r₂ n
    Tbl.build n fun lbc mc lac => t₁.get lbc mc lac && t₂.get lbc mc lac
  | .complement r₁ r₂ =>
    let t₁ := NT r₁ n; let t₂ := NT r₂ n
    Tbl.build n fun lbc mc lac => t₁.get lbc mc lac && !t₂.get lbc mc lac
  | .mult r₁ r₂ =>
    let t₁ := NT r₁ n; let t₂ := NT r₂ n
    Tbl.build n fun lbc mc lac => (List.range (mc + 1)).any fun mc₁ =>
      t₁.get lbc mc₁ ((mc - mc₁) + lac) && t₂.get (lbc + mc₁) (mc - mc₁) lac
  | .star r b =>
    let tr := NT r n; let tb := NT b n
    let diags := (Array.range (n + 1)).map fun lac =>
      (Array.range ((n + 1) - lac)).map fun s => starDiag tr.get tb.get s lac
    Tbl.build n fun lbc mc lac => ((diags[lac]? >>= (·[lbc + mc]?)) >>= (·[mc]?)).getD false
  | .lb r => let t := NT r n; Tbl.build n fun lbc mc lac => mc == 0 && t.get 0 lbc lac
  | .la r => let t := NT r n; Tbl.build n fun lbc mc lac => mc == 0 && t.get lbc lac 0
  | .lbStep r => let t := NT r n; Tbl.build n fun lbc mc lac => match lbc with | 0 => false | lbc + 1 => t.get lbc mc lac
  | .mStep r => let t := NT r n; Tbl.build n fun lbc mc lac => match mc with | 0 => false | mc + 1 => t.get lbc mc lac
  | .laStep r => let t := NT r n; Tbl.build n fun lbc mc lac => match lac with | 0 => false | lac + 1 => t.get lbc mc lac

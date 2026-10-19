import Thesis.Syntax.Expressions
import Thesis.Semantics.«2_Operators»

open Expr


def NStar (fr fb : Nat → Nat → Bool) (mc lac : Nat) : Bool :=
  fb mc lac || (List.range mc).attach.any fun ⟨k, hk⟩ => fr (k + 1) ((mc - (k + 1)) + lac) && NStar fr fb (mc - (k + 1)) lac
--termination_by mc
decreasing_by have := List.mem_range.mp hk; omega

def N {α} (r : Expr α) (n : Nat) (mc lac : Nat) : Bool :=
  match r with
  | .empty => false
  | .unit => mc == 0
  | .top => true
  | .symbol _ => false
  | .plus r₁ r₂ => N r₁ n mc lac || N r₂ n mc lac
  | .intersection r₁ r₂ => N r₁ n mc lac && N r₂ n mc lac
  | .complement r₁ r₂ => N r₁ n mc lac && !N r₂ n mc lac
  | .mult r₁ r₂ => (List.range (mc + 1)).any fun mc₁ => N r₁ n mc₁ ((mc - mc₁) + lac) && N r₂ n (mc - mc₁) lac
  | .star r b => NStar (N r n) (N b n) mc lac
  | .lb r => mc == 0 && lac == 0 && (List.range (n + 1)).any fun m => N r n m 0
  | .la r => mc == 0 && N r n lac 0
  | .mStep r => match mc with | 0 => false | mc + 1 => N r n mc lac
  | .laStep r => match lac with | 0 => false | lac + 1 => N r n mc lac


abbrev Tbl := Array (Array Bool)

def Tbl.get (t : Tbl) (mc lac : Nat) : Bool := (t[lac]? >>= (·[mc]?)).getD false

def Tbl.build (n : Nat) (f : Nat → Nat → Bool) : Tbl :=
  (Array.range (n + 1)).map fun lac => (Array.range ((n + 1) - lac)).map fun mc => f mc lac


def starCol (fr fb : Nat → Nat → Bool) (L lac : Nat) : Array Bool :=
  (List.range ((L + 1) - lac)).foldl (init := #[]) fun s mc =>
    s.push (fb mc lac || (List.range mc).any fun k =>
      fr (k + 1) ((mc - (k + 1)) + lac) && s.getD (mc - (k + 1)) false)

def NT (r : Expr α) (n : Nat) : Tbl :=
  match r with
  | .empty => Tbl.build n fun _ _ => false
  | .unit => Tbl.build n fun mc _ => mc == 0
  | .top => Tbl.build n fun _ _ => true
  | .symbol _ => Tbl.build n fun _ _ => false
  | .plus r₁ r₂ => Tbl.build n fun mc lac => (NT r₁ n).get mc lac || (NT r₂ n).get mc lac
  | .intersection r₁ r₂ => Tbl.build n fun mc lac => (NT r₁ n).get mc lac && (NT r₂ n).get mc lac
  | .complement r₁ r₂ => Tbl.build n fun mc lac => (NT r₁ n).get mc lac && !(NT r₂ n).get mc lac
  | .mult r₁ r₂ => Tbl.build n fun mc lac => (List.range (mc + 1)).any fun mc₁ => (NT r₁ n).get mc₁ ((mc - mc₁) + lac) && (NT r₂ n).get (mc - mc₁) lac
  | .star r b => (Array.range (n + 1)).map fun lac => starCol (NT r n).get (NT b n).get n lac
  | .lb r => Tbl.build n fun mc lac => mc == 0 && lac == 0 && (List.range (n + 1)).any fun m => (NT r n).get m 0
  | .la r => Tbl.build n fun mc lac => mc == 0 && (NT r n).get lac 0
  | .mStep r => Tbl.build n fun mc lac => match mc with | 0 => false | mc + 1 => (NT r n).get mc lac
  | .laStep r => Tbl.build n fun mc lac => match lac with | 0 => false | lac + 1 => (NT r n).get mc lac

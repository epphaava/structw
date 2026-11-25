import Thesis.Syntax.«1_Expressions»

namespace SRegexDerivatives

open SRegex StructuredWords kStructuredWords kOperators


mutual

def D [DecidableEq α] (a : α) : SRegex α → SRegex α
  | .empty | .unit _ | .lb _ | .la _ => ∅
  | .top ss => T ↑₂ss
  | .symbol b ss => if a = b then I ↑₂ss else ∅
  | .plus r₁ r₂ => (D a r₁) + (D a r₂)
  | .intersection r₁ r₂ => (D a r₁) & (D a r₂)
  | .complement r₁ r₂ => (D a r₁) - (D a r₂)
  | .mult r₁ r₂ => ((D a r₁) • (DLB a r₂)) + ((DLA a r₁) • (D a r₂))
  | .star r b => SRegex.star (DLA a r) ((D a b) + ((D a r) • (SRegex.star (DLB a r) (DLB a b))))

def DLB [DecidableEq α] (a : α) : SRegex α → SRegex α
  | .empty => ∅
  | .unit ss => I ↑₁ss
  | .top ss => T ↑₁ss
  | .symbol b ss => #b ↑₁ss
  | .plus r₁ r₂ => (DLB a r₁) + (DLB a r₂)
  | .intersection r₁ r₂ => (DLB a r₁) & (DLB a r₂)
  | .complement r₁ r₂ => (DLB a r₁) - (DLB a r₂)
  | .mult r₁ r₂ => (DLB a r₁) • (DLB a r₂)
  | .star r b => SRegex.star (DLB a r) (DLB a b)
  | .lb r => ◁ (D a r)
  | .la r => ▷ (DLB a r)

def DLA [DecidableEq α] (a : α) : SRegex α → SRegex α
  | .empty | .symbol _ _=> ∅
  | .unit ss => I ↑₃ss
  | .top ss => T ↑₃ss
  | .plus r₁ r₂ => (DLA a r₁) + (DLA a r₂)
  | .intersection r₁ r₂ => (DLA a r₁) & (DLA a r₂)
  | .complement r₁ r₂ => (DLA a r₁) - (DLA a r₂)
  | .mult r₁ r₂ => (DLA a r₁) • (DLA a r₂)
  | .star r b => SRegex.star (DLA a r) (DLA a b)
  | .lb r => ◁(DLA a r)
  | .la r => ▷(D a r)

end

def D_word [DecidableEq α] (w : List α) (r : SRegex α) : SRegex α :=
  match w with
  | [] => r
  | a :: tl => D_word tl (D a r)

def DLB_word [DecidableEq α] (w : List α) (r : SRegex α) : SRegex α :=
  match w with
  | [] => r
  | a :: tl => DLB_word tl (DLB a r)

-- Definition 4.2.2 — Iterated lookahead derivative
def DLA_word [DecidableEq α] (w : List α) (r : SRegex α) : SRegex α :=
  match w with
  | [] => r
  | a :: tl => DLA_word tl (DLA a r)

-- Definition 4.2.4 — Iterated existential derivative
def xD [DecidableEq α] (w : List α) (r : SRegex α) : SRegex α :=
  match w with
  | [] => r
  | hd :: tl => xD tl (.plus (.plus (DLB hd r) (D hd r)) (DLA hd r))


end SRegexDerivatives

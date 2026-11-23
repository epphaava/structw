import Thesis.Semantics.Lang.«1_StructuredWords»

namespace kStructuredWords

open StructuredWords

def kLang (α : Type) (k : Nat) : Type := { l : Lang α // ∀ w, l w → w.word_steps ≤ k }

instance : CoeFun (kLang α k) (fun _ => Word α → Prop) := ⟨Subtype.val⟩

-- Equality on kLang, comparing the underlying languages.

def kLEq (k : kLang α n) (l : kLang α m) := LEq k.1 l.1
infixl:50 " ≐ " => kLEq

end kStructuredWords

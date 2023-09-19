import Mathlib.Init.ZeroOne
import Mathlib.Algebra.Regular.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image

universe u
variable (α : Type u)

abbrev NonZero [Zero α] := Subtype (λx : α ↦ x ≠ 0)
abbrev NonZero.ne_zero [Zero α] (s : NonZero α) : s.val ≠ 0 := s.property

variable {α}
namespace NonZero

instance nonZeroCoe [Zero α] : Coe (NonZero α) α where
  coe a := a.val
instance [Zero α] (a : NonZero α) : NeZero a.val where
  out := a.ne_zero
instance coeNonZero (a : α) [Zero α] [i : NeZero a] : CoeDep α a (NonZero α) where
  coe := ⟨a, i.out⟩

@[simp]
lemma non_zero_prop [Zero α] (a : NonZero α) : a.val ≠ 0 := a.ne_zero

instance decidableEq [i : DecidableEq α] [Zero α] : DecidableEq (NonZero α) :=
  λa b => match i a b with
  | isFalse h => isFalse (by
    intro h'
    rw [h'] at h
    contradiction)
  | isTrue h => isTrue (by ext; assumption)

end NonZero

namespace Finset

def nonZero [DecidableEq α] [Zero α] (s : Finset α) : Finset (NonZero α) :=
  (s.subtype λe => e ≠ 0).image λe => ⟨e.val, e.property⟩

end Finset
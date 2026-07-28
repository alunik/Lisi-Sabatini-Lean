module

public import Mathlib.Data.ZMod.Basic

/-!
# The two-dimensional vector space over `F₃`

This neutral alias is shared by uniform two-core arguments and isolated
finite equality cases.
-/

@[expose] public section

namespace LisiSabatini

abbrev F3Plane :=
  Fin 2 → ZMod 3

end LisiSabatini

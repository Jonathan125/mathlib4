/-
Copyright (c) 2026 Jonathan Konig. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Konig
-/
import Mathlib.CategoryTheory.AlgebraicTheories.AC_LT.ACtoLT
import Mathlib.CategoryTheory.AlgebraicTheories.AC_LT.LTtoAC

/-!
# Unit

## Main definitions

* `FooBar`

## Main statements

* `fooBar_unique`

## Notation



## Implementation details



## References

* [F. Bar, *Quuxes*][bibkey]

## Tags

Foobars, barfoos
-/

namespace CategoryTheory

namespace AlgebraicTheories

namespace AC_LT

universe u

protected def counit : LTtoAC.func.{u, u, u} ⋙ ACtoLT.func.{u} ≅ 𝟭 LawvereTheory.{u, u, u} where
  hom := sorry
  inv := sorry

end AC_LT

end AlgebraicTheories

end CategoryTheory

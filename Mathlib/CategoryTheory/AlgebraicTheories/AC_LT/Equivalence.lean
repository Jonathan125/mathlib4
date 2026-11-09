/-
Copyright (c) 2026 Jonathan Konig. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Konig
-/
import Mathlib.CategoryTheory.AlgebraicTheories.AC_LT.Unit
import Mathlib.CategoryTheory.AlgebraicTheories.AC_LT.Counit

/-!
# Equivalence

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

protected def equivalence : AbstractClone.{u} ≌ LawvereTheory.{u, u, u} where
  functor := ACtoLT.func
  inverse := LTtoAC.func
  unitIso := AC_LT.unit
  counitIso := AC_LT.counit
  functor_unitIso_comp A :=
    LawvereTheory.Hom.ext <| Functor.ext (LawvereTheory.Hom.comp_obj _ _) <|
    fun _ _ _ ↦ LTtoAC.coproduct_iso_inv_inj _ _ _ <| (LTtoAC.coproduct_iso_hom_inv_id _ _).trans <|
    funext <| fun _ ↦ funext <| fun _ ↦ Eq.symm <| (A.projection _ _).trans <|
    (A.projection _ _).trans <| A.identity _

end AC_LT

end AlgebraicTheories

end CategoryTheory

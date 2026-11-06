/-
Copyright (c) 2026 Jonathan Konig. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Konig
-/
import Mathlib.CategoryTheory.FintypeCat
import Mathlib.CategoryTheory.Functor.BijectionOnObjects
import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
-- import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq

/-!
# Lawvere

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

universe v u

class LawvereStruct {T : Type u} [Category.{v} T] (F : FintypeCat.Skeleton ⥤ T)
    extends F.BijectionOnObjects where
  initial : Limits.IsInitial (F.obj (FintypeCat.Skeleton.mk 0))
  -- pushouts (m n : FintypeCat.Skeleton) : Limits.IsPush


end AlgebraicTheories

end CategoryTheory

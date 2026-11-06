/-
Copyright (c) 2026 Jonathan Konig. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Konig
-/
import Mathlib.CategoryTheory.Functor.Basic

/-!
# BijectionOnObjects

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

namespace Functor

universe v₁ v₂ u₁ u₂

class BijectionOnObjects {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D)
    where
  objInv : D → C
  left_inv : Function.LeftInverse objInv F.obj
  right_inv : Function.RightInverse objInv F.obj

end Functor

end CategoryTheory

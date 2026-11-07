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

namespace BijectionOnObjects

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D)
  [BijectionOnObjects F]

@[simp]
protected theorem left_inv_app (X : C) : objInv F (F.obj X) = X :=
  left_inv _

@[simp]
protected theorem right_inv_app (Y : D) : F.obj (objInv F Y) = Y :=
  right_inv _

protected theorem obj_conj (X : C) (Y : D) : F.obj X = Y ↔ X = objInv F Y :=
  ⟨fun h ↦ by simp [← h], fun h ↦ by simp [h]⟩

protected theorem obj_inv_conj (Y : D) (X : C) : objInv F Y = X ↔ Y = F.obj X :=
  ⟨fun h ↦ by simp [← h], fun h ↦ by simp [h]⟩

end BijectionOnObjects

end Functor

end CategoryTheory

/-
Copyright (c) 2026 Jonathan Konig. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Konig
-/
import Mathlib.CategoryTheory.FintypeCat
import Mathlib.CategoryTheory.Functor.BijectionOnObjects
import Mathlib.CategoryTheory.Limits.IndexCategory.Basic


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

universe v₂ u₁ u₂


class LawvereStruct {T : Type u₂} [Category.{v₂} T] (F : FintypeCat.Skeleton.{u₁} ⥤ T) :
    Type (max u₁ u₂ v₂) extends F.BijectionOnObjects where
  initial_to (n : FintypeCat.Skeleton.{u₁}) : F.obj (FintypeCat.Skeleton.mk 0) ⟶ F.obj n

  coproduct_desc {m n k : FintypeCat.Skeleton.{u₁}} (f : F.obj m ⟶ F.obj k)
      (g : F.obj n ⟶ F.obj k) : F.obj (m + n) ⟶ F.obj k

  initial_uniq {n : FintypeCat.Skeleton.{u₁}} (f : F.obj (FintypeCat.Skeleton.mk 0) ⟶ F.obj n) :
    f = initial_to n := by cat_disch

  coproduct_fac_left {m n k : FintypeCat.Skeleton.{u₁}} (f : F.obj m ⟶ F.obj k)
      (g : F.obj n ⟶ F.obj k) :
      F.map (FintypeCat.Skeleton.to_initial_segment m n) ≫ coproduct_desc f g = f := by cat_disch

  coproduct_fac_right {m n k : FintypeCat.Skeleton.{u₁}} (f : F.obj m ⟶ F.obj k)
      (g : F.obj n ⟶ F.obj k) :
      F.map (FintypeCat.Skeleton.to_concluding_segment m n) ≫ coproduct_desc f g = g := by cat_disch

  coproduct_uniq {m n k : FintypeCat.Skeleton.{u₁}} (f : F.obj m ⟶ F.obj k)
      (g : F.obj n ⟶ F.obj k) (h : F.obj (m + n) ⟶ F.obj k) :
      F.map (FintypeCat.Skeleton.to_initial_segment m n) ≫ h = f →
      F.map (FintypeCat.Skeleton.to_concluding_segment m n) ≫ h = g → h = coproduct_desc f g :=
    by cat_disch

namespace LawvereStruct

protected instance subsingleton {T : Type u₂} [Category.{v₂} T]
    (F : FintypeCat.Skeleton.{u₁} ⥤ T) : Subsingleton (LawvereStruct F) where
  allEq A B := by
    match A, B with
    | @LawvereStruct.mk _ _ _ toBijectionOnObjects initial_to _ _ coproduct_fac_left
      coproduct_fac_right _, @LawvereStruct.mk _ _ _ toBijectionOnObjects' initial_to' _
      initial_uniq' _ _ coproduct_uniq' =>
    obtain rfl : toBijectionOnObjects = toBijectionOnObjects' := Subsingleton.elim _ _
    obtain rfl : initial_to = initial_to' := funext <| fun n ↦ initial_uniq' _
    congr
    funext m n k f g
    exact coproduct_uniq' _ _ _ (coproduct_fac_left _ _) (coproduct_fac_right _ _)

end LawvereStruct

structure LawvereTheory : Type (max u₁ (u₂ + 1) (v₂ + 1)) where
  {T : Type u₂}
  [cat : Category.{v₂} T]
  (F : FintypeCat.Skeleton.{u₁} ⥤ T)
  [struct : LawvereStruct F]

attribute [instance] LawvereTheory.cat LawvereTheory.struct

namespace LawvereTheory

/--
In Mathlib, Functor composition depends on the Classical.choice axiom.
We are unable to define a morphism of Lawvere theories without introducing the axiom of choice.
-/
protected structure Hom (A B : LawvereTheory.{v₂, u₁, u₂}) where
  G : A.T ⥤ B.T
  comm : A.F ⋙ G = B.F := by cat_disch

attribute [simp] LawvereTheory.Hom.comm

namespace Hom

@[simp]
protected theorem comm_assoc {A B : LawvereTheory.{v₂, u₁, u₂}} (f : LawvereTheory.Hom A B)
    {T : Type u₂} [Category.{v₂} T] (H : B.T ⥤ T) : A.F ⋙ f.G ⋙ H = B.F ⋙ H :=
  by simp [-LawvereTheory.Hom.comm, <-f.comm] ; rfl

protected def id (A : LawvereTheory.{v₂, u₁, u₂}) : LawvereTheory.Hom A A where
  G := 𝟭 A.T

protected def comp {A B C : LawvereTheory.{v₂, u₁, u₂}} (f : LawvereTheory.Hom A B)
    (g : LawvereTheory.Hom B C) : LawvereTheory.Hom A C where
  G := f.G ⋙ g.G

end Hom

protected instance Cat : Category.{max u₂ v₂} LawvereTheory.{v₂, u₁, u₂} where
  Hom := LawvereTheory.Hom
  id := LawvereTheory.Hom.id
  comp := LawvereTheory.Hom.comp

end LawvereTheory

end AlgebraicTheories

end CategoryTheory

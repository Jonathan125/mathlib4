/-
Copyright (c) 2026 Jonathan Konig. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Konig
-/
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.CategoryTheory.AlgebraicTheories.Clone
import Mathlib.CategoryTheory.AlgebraicTheories.Lawvere

/-!
# ACtoLT

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


universe u

namespace ACtoLT


protected def obj_T (_ : AbstractClone.{u}) : Type u := ULift.{u} ℕ

namespace obj_T

protected def mk (A : AbstractClone.{u}) : ℕ → ACtoLT.obj_T A := ULift.up

protected def len (A : AbstractClone.{u}) : ACtoLT.obj_T A → ℕ := ULift.down

end obj_T


protected instance Cat (A : AbstractClone.{u}) : SmallCategory.{u} (ACtoLT.obj_T A) where
  Hom X Y := Fin X.len → A.c Y.len
  id X := A.υ
  comp f g := fun i ↦ A.μ (f i) g

namespace Cat

protected theorem hom_comp_app {A : AbstractClone.{u}} {X Y Z : ACtoLT.obj_T A} (f : X ⟶ Y)
    (g : Y ⟶ Z) (i : Fin X.len) : (f ≫ g) i = A.μ (f i) g :=
  rfl

protected theorem hcongr_eqToHom_app {A : AbstractClone.{u}} {X Y : ACtoLT.obj_T A} (h : X = Y)
    (i : Fin X.len) : eqToHom h i ≍ A.υ i :=
  by obtain rfl : X = Y := h ; rfl

-- (fun x ↦ { down := (f { down := i }).down }) = (fun x ↦ { down := i }) ≫ f

end Cat

protected def obj_F (A : AbstractClone.{u}) : FintypeCat.Skeleton.{u} ⥤ ACtoLT.obj_T A where
  obj := id
  map f := fun i ↦ A.υ (f ⟨i⟩).down
  map_comp f g :=
    funext <| fun i ↦ Eq.symm <| (ACtoLT.Cat.hom_comp_app _ _ i).trans <| A.projection _ _


protected instance F_struct (A : AbstractClone.{u}) : LawvereStruct.{u, u, u} (ACtoLT.obj_F A) where
  objInv := id
  initial_to _ := fun i ↦ i.elim0
  coproduct_desc f g := Fin.append f g
  initial_uniq _ := funext <| fun i ↦ i.elim0
  coproduct_fac_left f g := funext <| fun i ↦ (ACtoLT.Cat.hom_comp_app _ _ i).trans <|
    (A.projection _ _).trans <| Fin.append_left _ _ _
  coproduct_fac_right f g := funext <| fun i ↦ (ACtoLT.Cat.hom_comp_app _ _ i).trans <|
    (A.projection _ _).trans <| Fin.append_right _ _ _
  coproduct_uniq f g h hl hr := Fin.append_castAdd_natAdd.symm.trans <| congr_arg₂ _
    (Eq.symm <| hl.symm.trans <| funext <| fun i ↦ (ACtoLT.Cat.hom_comp_app _ _ i).trans <|
    A.projection _ _) <| Eq.symm <| hr.symm.trans <| funext <| fun i ↦
    (ACtoLT.Cat.hom_comp_app _ _ i).trans <| A.projection _ _


protected def obj (A : AbstractClone.{u}) : LawvereTheory.{u, u, u} where
  F := ACtoLT.obj_F A

protected def map_hom {A B : AbstractClone.{u}} (f : A ⟶ B) : ACtoLT.obj_T A ⥤ ACtoLT.obj_T B where
  obj := id
  map g := fun i ↦ f.hom (g i)
  map_id _ := funext <| fun _ ↦ f.υ_comm _
  map_comp _ _ := funext <| fun _ ↦ f.μ_comm _ _

protected theorem map_comm {A B : AbstractClone.{u}} (f : A ⟶ B) :
    ACtoLT.obj_F A ⋙ ACtoLT.map_hom f = ACtoLT.obj_F B :=
  Functor.ext (fun _ ↦ rfl) <| fun _ _ _ ↦ funext <| fun _ ↦ (f.υ_comm _).trans <| Eq.symm <|
    (B.projection _ _).trans <| B.projection _ _

protected def map {A B : AbstractClone.{u}} (f : A ⟶ B) : ACtoLT.obj A ⟶ ACtoLT.obj B where
  G := ACtoLT.map_hom f
  comm := ACtoLT.map_comm f

protected def func : AbstractClone.{u} ⥤ LawvereTheory.{u, u, u} where
  obj := ACtoLT.obj
  map := ACtoLT.map

end ACtoLT

end AlgebraicTheories

end CategoryTheory

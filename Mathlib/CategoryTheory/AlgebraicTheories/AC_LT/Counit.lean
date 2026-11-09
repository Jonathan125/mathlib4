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

protected def counit_hom_app_func (A : LawvereTheory.{u}) : ACtoLT.obj_T (LTtoAC.obj A.F) ⥤ A.T
    where
  obj n := A.F.obj n
  map f := LTtoAC.coproduct_iso_hom _ f
  map_id _ := LTtoAC.coproduct_iso_inv_inj _ _ _ <| (LTtoAC.coproduct_iso_hom_inv_id _ _).trans <|
    funext <| fun _ ↦ Eq.symm <| Category.comp_id _
  map_comp _ _ := LTtoAC.coproduct_iso_inv_inj _ _ _ <|
    (LTtoAC.coproduct_iso_hom_inv_id _ _).trans <| funext <| fun i ↦
    (ACtoLT.Cat.hom_comp_app _ _ _).trans <| Eq.symm <| (Category.assoc _ _ _).symm.trans <|
    congr_fun (LTtoAC.coproduct_iso_hom_inv_id A.F _) i =≫ _

protected def counit_hom_app (A : LawvereTheory.{u}) : ACtoLT.obj (LTtoAC.obj A.F) ⟶ A where
  G := AC_LT.counit_hom_app_func A
  comm := sorry

protected def counit_hom : LTtoAC.func.{u, u, u} ⋙ ACtoLT.func.{u} ⟶ 𝟭 LawvereTheory.{u, u, u}
    where
  app A := AC_LT.counit_hom_app A
  naturality _ _ f := sorry


protected def counit_inv_app_func (A : LawvereTheory.{u}) : A.T ⥤ ACtoLT.obj_T (LTtoAC.obj A.F)
    where
  obj n := A.bijectionOnObjects.objInv n
  map f := LTtoAC.coproduct_iso_inv A.F (eqToHom (A.bijectionOnObjects.right_inv _) ≫ f ≫
    eqToHom (A.bijectionOnObjects.right_inv _).symm)
  map_id _ := funext <| fun _ ↦ (_ ≫= _ ≫= Category.id_comp _).trans <|
    (_ ≫= eqToHom_trans _ _).trans <| Category.comp_id _
  map_comp _ g := funext <| fun _ ↦ Eq.symm <| (ACtoLT.Cat.hom_comp_app _ _ _).trans <| (_ ≫=
    LTtoAC.coproduct_iso_inv_hom_id A.F (eqToHom (A.bijectionOnObjects.right_inv _) ≫ g ≫
    eqToHom (A.bijectionOnObjects.right_inv _).symm)).trans <| (Category.assoc _ _ _).trans <|
    whisker_eq _ <| (Category.assoc _ _ _).trans <| whisker_eq _ <| (Category.assoc _ _ _).trans <|
    (_ ≫= eqToHom_trans_assoc _ _ _).trans <| (_ ≫= eqToHom_refl _ _ =≫ _).trans <|
    (_ ≫= Category.id_comp _).trans <| Eq.symm <| Category.assoc _ _ _

protected def counit_inv_app (A : LawvereTheory.{u}) : A ⟶ ACtoLT.obj (LTtoAC.obj A.F) where
  G := AC_LT.counit_inv_app_func A
  comm := sorry

protected def counit_inv : 𝟭 LawvereTheory.{u, u, u} ⟶ LTtoAC.func.{u, u, u} ⋙ ACtoLT.func.{u}
    where
  app A := AC_LT.counit_inv_app A
  naturality _ _ f := sorry


protected def counit : LTtoAC.func.{u, u, u} ⋙ ACtoLT.func.{u} ≅ 𝟭 LawvereTheory.{u, u, u} where
  hom := AC_LT.counit_hom
  inv := AC_LT.counit_inv
  hom_inv_id := sorry
  inv_hom_id := sorry

end AC_LT

end AlgebraicTheories

end CategoryTheory

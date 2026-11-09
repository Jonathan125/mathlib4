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
  obj := A.F.obj
  map := LTtoAC.coproduct_iso_hom _
  map_id _ :=
    LTtoAC.coproduct_iso_inv_inj _ _ _ <| (LTtoAC.coproduct_iso_hom_inv_id _ _).trans <| funext <|
    fun _ ↦ Eq.symm <| Category.comp_id _
  map_comp _ _ :=
    LTtoAC.coproduct_iso_inv_inj _ _ _ <| (LTtoAC.coproduct_iso_hom_inv_id _ _).trans <| funext <|
    fun i ↦ Eq.symm <| (Category.assoc _ _ _).symm.trans <|
    congr_fun (LTtoAC.coproduct_iso_hom_inv_id A.F _) i =≫ _

protected def counit_hom_app (A : LawvereTheory.{u}) : ACtoLT.obj (LTtoAC.obj A.F) ⟶ A where
  G := AC_LT.counit_hom_app_func A
  comm :=
    Functor.ext (fun X ↦ Functor.comp_obj _ _ X) <| fun _ _ _ ↦ (Functor.comp_map _ _ _).trans <|
    LTtoAC.coproduct_iso_inv_inj _ _ _ <| (LTtoAC.coproduct_iso_hom_inv_id _ _).trans <| funext <|
    fun _ ↦ (congr_arg A.F.map (FintypeCat.Skeleton.const_comp _ _)).trans <|
    (A.F.map_comp _ _).trans <| whisker_eq _ <| Eq.symm <| (Category.id_comp _).trans <|
    Category.comp_id _

protected def counit_hom : LTtoAC.func.{u, u, u} ⋙ ACtoLT.func.{u} ⟶ 𝟭 LawvereTheory.{u, u, u}
    where
  app := AC_LT.counit_hom_app
  naturality _ _ _ :=
    (Functor.comp_map _ _ _ =≫ _).trans <| Eq.symm <| (_ ≫= Functor.id_map _).trans <|
    LawvereTheory.Hom.ext <| Functor.ext (fun _ ↦ Eq.symm <| LawvereTheory.Hom.obj_comm _ _) <|
    fun _ _ _ ↦ Eq.symm <| (eqToHom_comp_iff _ _ _).mpr <| (comp_eqToHom_iff _ _ _).mpr <|
    LTtoAC.coproduct_iso_inv_inj _ _ _ <| (LTtoAC.coproduct_iso_hom_inv_id _ _).trans <| funext <|
    fun _ ↦ Eq.symm <| (_ ≫= Category.assoc _ _ _).trans <|
    (LawvereTheory.Hom.hom_comm _ _ =≫ _).trans <| (Category.assoc _ _ _).trans <| whisker_eq _ <|
    (Category.assoc _ _ _).trans <| (_ ≫= eqToHom_trans_assoc _ _ _).trans <|
    (_ ≫= Category.id_comp _).trans <| (Category.assoc _ _ _).symm.trans <| (eq_whisker · _) <|
    (Functor.map_comp _ _ _).symm.trans <| congr_arg _ <|
    congr_fun (LTtoAC.coproduct_iso_hom_inv_id _ _) _


protected def counit_inv_app_func (A : LawvereTheory.{u}) : A.T ⥤ ACtoLT.obj_T (LTtoAC.obj A.F)
    where
  obj n := A.bijectionOnObjects.objInv n
  map f :=
    LTtoAC.coproduct_iso_inv A.F (eqToHom (A.bijectionOnObjects.right_inv _) ≫ f ≫
    eqToHom (A.bijectionOnObjects.right_inv _).symm)
  map_id _ :=
    funext <| fun _ ↦ (_ ≫= _ ≫= Category.id_comp _).trans <| (_ ≫= eqToHom_trans _ _).trans <|
    Category.comp_id _
  map_comp _ _ :=
    funext <| fun _ ↦ Eq.symm <| (_ ≫= LTtoAC.coproduct_iso_inv_hom_id A.F (eqToHom
    (A.bijectionOnObjects.right_inv _) ≫ _ ≫ eqToHom _)).trans <| (Category.assoc _ _ _).trans <|
    whisker_eq _ <| (Category.assoc _ _ _).trans <| whisker_eq _ <| (Category.assoc _ _ _).trans <|
    (_ ≫= eqToHom_trans_assoc _ _ _).trans <| (_ ≫= Category.id_comp _).trans <| Eq.symm <|
    Category.assoc _ _ _

protected def counit_inv_app (A : LawvereTheory.{u}) : A ⟶ ACtoLT.obj (LTtoAC.obj A.F) where
  G := AC_LT.counit_inv_app_func A
  comm :=
    Functor.ext (fun X ↦ (Functor.comp_obj _ _ X).trans <|
    Functor.BijectionOnObjects.left_inv_app A.F X) <| fun _ _ _ ↦ (Functor.comp_map _ _ _).trans <|
    Eq.symm <| (eqToHom_comp_iff _ _ _).mpr <| (comp_eqToHom_iff _ _ _).mpr <| funext <| fun _ ↦
    Eq.symm <| (ACtoLT.Cat.hom_comp_app _ _ _).trans <|
    (congr_arg (fun x ↦ x ≫ _) (ACtoLT.Cat.hom_comp_app _ _ _ )).trans <|
    ((_ ≫= LTtoAC.coproduct_iso_inv_hom_id _ _) =≫ _).trans <| Eq.symm <| (congr_arg A.F.map
    (FintypeCat.Skeleton.const_comp _ _)).trans <| (A.F.map_comp _ _).trans <| Eq.symm <|
    ((_ ≫= (Category.assoc _ _ _).symm) =≫ _).trans <| ((Category.assoc _ _ _).symm =≫ _).trans <|
    (Category.assoc _ _ _).trans <| ((Category.assoc _ _ _).symm =≫ _).trans <|
    (Category.assoc _ _ _).trans <| congr_arg₂ _ (HEq.eq <| (comp_eqToHom_heq _ _).trans <|
    ACtoLT.Cat.hcongr_eqToHom_app _ _) <| Eq.symm <| (Category.comp_id _).symm.trans <|
    whisker_eq _ <| (eqToHom_comp_iff (A.bijectionOnObjects.right_inv _) _ _).mp <|
    (Category.comp_id _).trans <| Eq.symm <| LTtoAC.coproduct_iso_inv_inj _ _ _ <|
    (LTtoAC.coproduct_iso_hom_inv_id _ _).trans <| funext <| fun _ ↦ (comp_eqToHom_iff
    (A.bijectionOnObjects.right_inv _).symm _ _).mp <| HEq.eq <| (comp_eqToHom_heq _ _).trans <|
    ACtoLT.Cat.hcongr_eqToHom_app _ _

protected theorem coproducts_iso_hom_comm_eqToHom (A : LawvereTheory.{u, u, u})
    {X Y : (ACtoLT.obj (LTtoAC.obj A.F)).T} (f : X ⟶ Y) :
    LTtoAC.coproduct_iso_hom A.F f ≫ eqToHom (A.bijectionOnObjects.right_inv _).symm =
    LTtoAC.coproduct_iso_hom A.F (f ≫ eqToHom (A.bijectionOnObjects.left_inv _).symm) := by
  apply HEq.eq
  apply (comp_eqToHom_heq _ _).trans
  congr
  · exact Eq.symm <| A.bijectionOnObjects.left_inv _
  · exact HEq.symm <| comp_eqToHom_heq _ _

protected theorem counit_hom_inv_id (A : LawvereTheory.{u}) :
    AC_LT.counit_hom_app A ≫ AC_LT.counit_inv_app A = 𝟙 _ :=
  LawvereTheory.Hom.ext <| Functor.ext A.bijectionOnObjects.left_inv <| fun _ _ _ ↦ Eq.symm <|
  funext <| fun _ ↦ (ACtoLT.Cat.hom_comp_app _ _ _).trans <| Eq.symm <|
  (Category.assoc _ _ _).symm.trans <| congr_arg₂ _ ((comp_eqToHom_iff _ _ _).mpr <| Eq.symm <|
  HEq.eq <| (comp_eqToHom_heq _ _).trans <| ACtoLT.Cat.hcongr_eqToHom_app _ _) <|
  AC_LT.coproducts_iso_hom_comm_eqToHom _ _

protected theorem counit_inv_hom_id (A : LawvereTheory.{u}) :
    AC_LT.counit_inv_app A ≫ AC_LT.counit_hom_app A = 𝟙 _ :=
  LawvereTheory.Hom.ext <| Functor.ext A.bijectionOnObjects.right_inv <|
  fun _ _ _ ↦ LTtoAC.coproduct_iso_inv_hom_id _ _


protected def counit_inv : 𝟭 LawvereTheory.{u, u, u} ⟶ LTtoAC.func.{u, u, u} ⋙ ACtoLT.func.{u}
    where
  app := AC_LT.counit_inv_app
  naturality _ _ :=
    NatTrans.naturality_inv' AC_LT.counit_hom AC_LT.counit_inv_app AC_LT.counit_hom_inv_id
    AC_LT.counit_inv_hom_id


protected def counit : LTtoAC.func.{u, u, u} ⋙ ACtoLT.func.{u} ≅ 𝟭 LawvereTheory.{u, u, u} where
  hom := AC_LT.counit_hom
  inv := AC_LT.counit_inv
  hom_inv_id := NatTrans.ext <| funext <| AC_LT.counit_hom_inv_id
  inv_hom_id := NatTrans.ext <| funext <| AC_LT.counit_inv_hom_id

end AC_LT

end AlgebraicTheories

end CategoryTheory

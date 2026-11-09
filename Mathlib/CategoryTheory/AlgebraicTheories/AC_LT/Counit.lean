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

protected theorem unit_comp {X Y : FintypeCat.Skeleton.{u}} (f : X ⟶ Y) (i : Fin X.len) :
    (fun (_ : ULift.{u} (Fin (FintypeCat.Skeleton.mk.{u} 1).len)) ↦ ⟨(f ⟨i⟩).down⟩)
    = (fun _ ↦ ⟨i⟩) ≫ f := rfl

protected def counit_hom_app_func (A : LawvereTheory.{u}) : ACtoLT.obj_T (LTtoAC.obj A.F) ⥤ A.T
    where
  obj n := A.F.obj n
  map f := LTtoAC.coproduct_iso_hom _ f
  map_id _ := LTtoAC.coproduct_iso_inv_inj _ _ _ <| (LTtoAC.coproduct_iso_hom_inv_id _ _).trans <|
    funext <| fun _ ↦ Eq.symm <| Category.comp_id _
  map_comp _ _ := LTtoAC.coproduct_iso_inv_inj _ _ _ <|
    (LTtoAC.coproduct_iso_hom_inv_id _ _).trans <| funext <| fun i ↦ Eq.symm <|
    (Category.assoc _ _ _).symm.trans <| congr_fun (LTtoAC.coproduct_iso_hom_inv_id A.F _) i =≫ _

protected def counit_hom_app (A : LawvereTheory.{u}) : ACtoLT.obj (LTtoAC.obj A.F) ⟶ A where
  G := AC_LT.counit_hom_app_func A
  comm := Functor.ext (fun X ↦ Functor.comp_obj _ _ X) <| fun _ _ _ ↦
    (Functor.comp_map _ _ _).trans <| LTtoAC.coproduct_iso_inv_inj _ _ _ <|
    (LTtoAC.coproduct_iso_hom_inv_id _ _).trans <| funext <| fun _ ↦
    (congr_arg A.F.map (AC_LT.unit_comp _ _)).trans <| (A.F.map_comp _ _).trans <| whisker_eq _ <|
    Eq.symm <| (Category.id_comp _).trans <| Category.comp_id _

protected def counit_hom : LTtoAC.func.{u, u, u} ⋙ ACtoLT.func.{u} ⟶ 𝟭 LawvereTheory.{u, u, u}
    where
  app A := AC_LT.counit_hom_app A
  naturality _ _ f := (Functor.comp_map _ _ _ =≫ _).trans <| Eq.symm <|
    (_ ≫= Functor.id_map _).trans <| LawvereTheory.Hom.ext <| Functor.ext (fun _ ↦ Eq.symm <|
    LawvereTheory.Hom.obj_comm f _) <| fun _ _ _ ↦ (LawvereTheory.Hom.comp_map _ _ _).trans <|
    Eq.symm <| (_ ≫= LawvereTheory.Hom.comp_map _ _ _ =≫ _).trans <| (eqToHom_comp_iff _ _ _).mpr <|
    (comp_eqToHom_iff _ _ _).mpr <| LTtoAC.coproduct_iso_inv_inj _ _ _ <|
    (LTtoAC.coproduct_iso_hom_inv_id _ _).trans <| funext <| fun i ↦ Eq.symm <|
    (_ ≫= Category.assoc _ _ _).trans <| (LawvereTheory.Hom.hom_comm f _ =≫ _).trans <|
    (Category.assoc _ _ _).trans <| whisker_eq _ <| (Category.assoc _ _ _).trans <|
    (_ ≫= eqToHom_trans_assoc _ _ _).trans <| (_ ≫= Category.id_comp _).trans <|
    (Category.assoc _ _ _).symm.trans <| (fun h ↦ eq_whisker h _) <|
    (Functor.map_comp _ _ _).symm.trans <| congr_arg _ <|
    congr_fun (LTtoAC.coproduct_iso_hom_inv_id _ _) i


protected def counit_inv_app_func (A : LawvereTheory.{u}) : A.T ⥤ ACtoLT.obj_T (LTtoAC.obj A.F)
    where
  obj n := A.bijectionOnObjects.objInv n
  map f := LTtoAC.coproduct_iso_inv A.F (eqToHom (A.bijectionOnObjects.right_inv _) ≫ f ≫
    eqToHom (A.bijectionOnObjects.right_inv _).symm)
  map_id _ := funext <| fun _ ↦ (_ ≫= _ ≫= Category.id_comp _).trans <|
    (_ ≫= eqToHom_trans _ _).trans <| Category.comp_id _
  map_comp _ g := funext <| fun _ ↦ Eq.symm <| (_ ≫= LTtoAC.coproduct_iso_inv_hom_id A.F
    (eqToHom (A.bijectionOnObjects.right_inv _) ≫ g ≫ eqToHom _)).trans <|
    (Category.assoc _ _ _).trans <| whisker_eq _ <| (Category.assoc _ _ _).trans <| whisker_eq _ <|
    (Category.assoc _ _ _).trans <| (_ ≫= eqToHom_trans_assoc _ _ _).trans <|
    (_ ≫= Category.id_comp _).trans <| Eq.symm <| Category.assoc _ _ _

protected def counit_inv_app (A : LawvereTheory.{u}) : A ⟶ ACtoLT.obj (LTtoAC.obj A.F) where
  G := AC_LT.counit_inv_app_func A
  comm := Functor.ext (fun X ↦ (Functor.comp_obj _ _ X).trans <|
    Functor.BijectionOnObjects.left_inv_app A.F X) <| fun _ _ _ ↦ (Functor.comp_map _ _ _).trans <|
    Eq.symm <| (eqToHom_comp_iff _ _ _).mpr <| (comp_eqToHom_iff _ _ _).mpr <| funext <| fun _ ↦
    Eq.symm <| (ACtoLT.Cat.hom_comp_app _ _ _).trans <|
    (congr_arg (fun x ↦ x ≫ _) (ACtoLT.Cat.hom_comp_app _ _ _ )).trans <|
    ((_ ≫= LTtoAC.coproduct_iso_inv_hom_id _ _) =≫ _).trans <| Eq.symm <|
    (congr_arg A.F.map (AC_LT.unit_comp _ _)).trans <| (A.F.map_comp _ _).trans <| Eq.symm <|
    ((_ ≫= (Category.assoc _ _ _).symm) =≫ _).trans <| ((Category.assoc _ _ _).symm =≫ _).trans <|
    (Category.assoc _ _ _).trans <| ((Category.assoc _ _ _).symm =≫ _).trans <|
    (Category.assoc _ _ _).trans <| congr_arg₂ _ (HEq.eq <| (comp_eqToHom_heq _ _).trans <|
    ACtoLT.Cat.hcongr_eqToHom_app _ _) <| Eq.symm <| (Category.comp_id _).symm.trans <|
    whisker_eq _ <| (eqToHom_comp_iff (A.bijectionOnObjects.right_inv _) _ _).mp <|
    (Category.comp_id _).trans <| Eq.symm <| LTtoAC.coproduct_iso_inv_inj _ _ _ <|
    (LTtoAC.coproduct_iso_hom_inv_id _ _).trans <| funext <| fun _ ↦ (comp_eqToHom_iff
    (A.bijectionOnObjects.right_inv _).symm _ _).mp <| HEq.eq <| (comp_eqToHom_heq _ _).trans <|
    ACtoLT.Cat.hcongr_eqToHom_app _ _


protected def counit_inv : 𝟭 LawvereTheory.{u, u, u} ⟶ LTtoAC.func.{u, u, u} ⋙ ACtoLT.func.{u}
    where
  app A := AC_LT.counit_inv_app A

  -- Prove the isomorphism first, then use that to prove naturality (do in generality for
  -- of functors isomorphism. Nat trans one way, and a collection of apps the other ways that is
  -- the inverse)
  naturality _ _ f := sorry


protected def counit : LTtoAC.func.{u, u, u} ⋙ ACtoLT.func.{u} ≅ 𝟭 LawvereTheory.{u, u, u} where
  hom := AC_LT.counit_hom
  inv := AC_LT.counit_inv
  hom_inv_id := by sorry
  inv_hom_id := sorry

end AC_LT

end AlgebraicTheories

end CategoryTheory

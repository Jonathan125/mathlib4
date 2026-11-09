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

protected def unit_hom_app (A : AbstractClone.{u}) : A ⟶ LTtoAC.obj (ACtoLT.obj A).F where
  hom x := fun _ ↦ x
  μ_comm x ys :=
    funext <| fun _ ↦ Eq.symm <| congr_arg (fun ys ↦ A.μ x ys) <|
    LTtoAC.coproduct_iso_inv_inj (ACtoLT.obj_F _) _ _ <|
    (LTtoAC.coproduct_iso_hom_inv_id _ _).trans <| funext₂ <| fun _ _ ↦ Eq.symm <| A.projection _ _

protected def unit_hom : 𝟭 AbstractClone.{u} ⟶ ACtoLT.func.{u} ⋙ LTtoAC.func.{u, u, u} where
  app A := AC_LT.unit_hom_app A
  naturality _ B _ :=
    AbstractClone.Hom.ext <| funext₂ <| fun _ _ ↦ (AbstractClone.Hom.comp_app _ _ _).trans <|
    (congr_arg _ (congr_fun (congr_fun (congr_arg _ (Functor.id_map _)) _) _)).trans <| Eq.symm <|
    funext <| fun _ ↦ (B.projection _ _).trans <| B.identity _


protected def unit_inv_app (A : AbstractClone.{u}) : LTtoAC.obj (ACtoLT.obj A).F ⟶ A where
  hom x := x ⟨0, Nat.zero_lt_one⟩
  μ_comm _ _ :=
    (ACtoLT.Cat.hom_comp_app _ _ _).trans <| congr_arg _ <|
    LTtoAC.coproduct_iso_inv_inj (ACtoLT.obj_F A) _ _ <|
    (LTtoAC.coproduct_iso_hom_inv_id _ _).trans <| funext₂ <| fun _ j ↦ Eq.symm <|
    (A.projection _ _).trans <| congr_arg _ <| Fin.eq_of_val_eq <| Eq.symm <|
    Nat.lt_one_iff.mp j.isLt

protected def unit_inv : ACtoLT.func.{u} ⋙ LTtoAC.func.{u, u, u} ⟶ 𝟭 AbstractClone.{u} where
  app A := AC_LT.unit_inv_app A
  naturality _ B _ :=
    AbstractClone.Hom.ext <| funext₂ <| fun _ _ ↦ (B.projection _ _).trans <| B.identity _


protected def unit : 𝟭 AbstractClone.{u} ≅ ACtoLT.func.{u} ⋙ LTtoAC.func.{u, u, u} where
  hom := AC_LT.unit_hom
  inv := AC_LT.unit_inv
  inv_hom_id :=
    NatTrans.ext <| funext <| fun _ ↦ AbstractClone.Hom.ext <| funext₂ <| fun _ X ↦ funext <|
    fun j ↦ congr_arg X <| Fin.eq_of_val_eq <| Eq.symm <| Nat.lt_one_iff.mp j.isLt

end AC_LT

end AlgebraicTheories

end CategoryTheory

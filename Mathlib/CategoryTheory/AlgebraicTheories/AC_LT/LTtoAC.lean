/-
Copyright (c) 2026 Jonathan Konig. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Konig
-/
import Mathlib.CategoryTheory.AlgebraicTheories.Clone
import Mathlib.CategoryTheory.AlgebraicTheories.Lawvere

/-!
# LTtoAC

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

namespace LTtoAC


protected def coproduct_iso_hom_aux {T : Type u₂} [Category.{v₂} T]
    (F : FintypeCat.Skeleton.{u₁} ⥤ T) [LawvereStruct F] {m : ℕ} {n : FintypeCat.Skeleton.{u₁}}
    (fs : Fin m → (F.obj (FintypeCat.Skeleton.mk.{u₁} 1) ⟶ F.obj n)) : F.obj ⟨m⟩ ⟶ F.obj n :=
  match m with
  | 0 => LawvereStruct.initial_to _
  | _ + 1 => LawvereStruct.coproduct_desc (LTtoAC.coproduct_iso_hom_aux F (fs ∘ Fin.castSucc)) <|
    fs <| Fin.last _

protected def coproduct_iso_hom {T : Type u₂} [Category.{v₂} T] (F : FintypeCat.Skeleton.{u₁} ⥤ T)
    [LawvereStruct F] {m n : FintypeCat.Skeleton.{u₁}}
    (fs : Fin m.len → (F.obj (FintypeCat.Skeleton.mk.{u₁} 1) ⟶ F.obj n)) : F.obj m ⟶ F.obj n :=
  LTtoAC.coproduct_iso_hom_aux F fs


protected def coproduct_iso_inv {T : Type u₂} [Category.{v₂} T] (F : FintypeCat.Skeleton.{u₁} ⥤ T)
    [LawvereStruct F] {m n : FintypeCat.Skeleton.{u₁}} (f : F.obj m ⟶ F.obj n) :
    Fin m.len → (F.obj (FintypeCat.Skeleton.mk 1) ⟶ F.obj n) :=
  fun i ↦ F.map (fun _ ↦ ⟨i⟩) ≫ f


protected theorem coproduct_iso_hom_inv_id_aux {T : Type u₂} [Category.{v₂} T]
    (F : FintypeCat.Skeleton.{u₁} ⥤ T) [LawvereStruct F] {m : ℕ} {n : FintypeCat.Skeleton.{u₁}}
    (fs : Fin m → (F.obj (FintypeCat.Skeleton.mk.{u₁} 1) ⟶ F.obj n)) :
    LTtoAC.coproduct_iso_inv F (LTtoAC.coproduct_iso_hom F fs) = fs := by
  funext i
  induction m with
  | zero => exact i.elim0
  | succ m ih =>
    if hi : i.val < m then
      exact (eq_whisker (Eq.symm (F.map_comp _ _).symm) _).trans <| (Category.assoc _ _ _).trans <|
        (whisker_eq _ (LawvereStruct.coproduct_fac_left _ _)).trans <| ih (fs ∘ Fin.castSucc)
        ⟨i.val, hi⟩
    else
      replace hi := Fin.eq_last_of_not_lt hi
      subst hi
      exact Eq.symm <|
        (LawvereStruct.coproduct_fac_right (LTtoAC.coproduct_iso_hom_aux F (fs ∘ Fin.castSucc))
        (fs (Fin.last m))).symm.trans <| eq_whisker (congr_arg _ <| funext <| fun ⟨i⟩ ↦
        ULift.up_inj.mpr <| Fin.eq_of_val_eq <| (Nat.add_right_inj.mpr
        (Nat.lt_one_iff.mp i.isLt)).trans <| Nat.add_zero m) _

protected theorem coproduct_iso_hom_inv_id {T : Type u₂} [Category.{v₂} T]
    (F : FintypeCat.Skeleton.{u₁} ⥤ T) [LawvereStruct F] {m n : FintypeCat.Skeleton.{u₁}}
    (fs : Fin m.len → (F.obj (FintypeCat.Skeleton.mk.{u₁} 1) ⟶ F.obj n)) :
    LTtoAC.coproduct_iso_inv F (LTtoAC.coproduct_iso_hom F fs) = fs :=
  LTtoAC.coproduct_iso_hom_inv_id_aux _ _


protected theorem coproduct_iso_inv_hom_id_aux {T : Type u₂} [Category.{v₂} T]
    (F : FintypeCat.Skeleton.{u₁} ⥤ T) [LawvereStruct F] {m : ℕ} {n : FintypeCat.Skeleton.{u₁}}
    (f : F.obj ⟨m⟩ ⟶ F.obj n) : LTtoAC.coproduct_iso_hom F (LTtoAC.coproduct_iso_inv F f) = f := by
  induction m with
  | zero => exact (LawvereStruct.initial_uniq _).trans (LawvereStruct.initial_uniq _).symm
  | succ m ih =>
    simp only [LTtoAC.coproduct_iso_hom, LTtoAC.coproduct_iso_hom_aux]
    apply Eq.symm
    apply (LawvereStruct.coproduct_uniq (F.map (FintypeCat.Skeleton.to_initial_segment _ _) ≫ f)
      (F.map (FintypeCat.Skeleton.to_concluding_segment _ _) ≫ f) f rfl rfl).trans
    congr
    · apply (ih (F.map (FintypeCat.Skeleton.to_initial_segment _ _) ≫ f)).symm.trans
      apply congr_arg
      funext i
      exact (Category.assoc _ _ _).symm.trans <| eq_whisker (F.map_comp _ _).symm _
    · funext ⟨i⟩
      exact ULift.up_inj.mpr <| Fin.eq_of_val_eq <|
        (Nat.add_right_inj.mpr (Nat.lt_one_iff.mp i.isLt)).trans (Nat.add_zero m)


protected theorem coproduct_iso_inv_hom_id {T : Type u₂} [Category.{v₂} T]
    (F : FintypeCat.Skeleton.{u₁} ⥤ T) [LawvereStruct F] {m n : FintypeCat.Skeleton.{u₁}}
    (f : F.obj m ⟶ F.obj n) : LTtoAC.coproduct_iso_hom F (LTtoAC.coproduct_iso_inv F f) = f :=
  LTtoAC.coproduct_iso_inv_hom_id_aux _ _

end LTtoAC

end AlgebraicTheories

end CategoryTheory

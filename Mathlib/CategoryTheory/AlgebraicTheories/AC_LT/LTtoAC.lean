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


universe v₁ v₂ u₁ u₂

theorem whisker_heq {C : Type u₂} [Category.{v₂} C] {W X Y Z : C} (f : W ⟶ X)
    (g : X ⟶ Y) (h : X ⟶ Z) : Y = Z → g ≍ h → f ≫ g ≍ f ≫ h := by
  intro h'
  obtain rfl : Y = Z := h'
  intro h'
  exact Eq.heq <| whisker_eq _ h'.eq

@[simp]
theorem map_eqToHom {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D)
    {X Y : C} (h : X = Y) : F.map (eqToHom h) = eqToHom (congr_arg F.obj h) := by
  obtain rfl : X = Y := h
  exact F.map_id _


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


protected theorem coproduct_iso_inv_inj {T : Type u₂} [Category.{v₂} T]
    (F : FintypeCat.Skeleton.{u₁} ⥤ T) [LawvereStruct F] {m n : FintypeCat.Skeleton.{u₁}}
    (f g : F.obj m ⟶ F.obj n) : LTtoAC.coproduct_iso_inv F f = LTtoAC.coproduct_iso_inv F g →
    f = g :=
  fun h ↦ (LTtoAC.coproduct_iso_inv_hom_id _ _).symm.trans <| (congr_arg _ h).trans <|
    LTtoAC.coproduct_iso_inv_hom_id F _


protected def obj {T : Type u₂} [Category.{v₂} T] (F : FintypeCat.Skeleton.{u₁} ⥤ T)
    [LawvereStruct F] : AbstractClone.{v₂} where
  c n := F.obj (FintypeCat.Skeleton.mk.{u₁} 1) ⟶ F.obj (FintypeCat.Skeleton.mk.{u₁} n)
  υ i := F.map (fun _ ↦ ⟨i⟩)
  μ f gs := f ≫ LTtoAC.coproduct_iso_hom F gs
  projection i fs := congr_fun (LTtoAC.coproduct_iso_hom_inv_id F fs) i
  identity {n} f := Eq.symm <| (Category.comp_id f).symm.trans <| whisker_eq _ <|
    (LTtoAC.coproduct_iso_inv_hom_id F _).symm.trans <| congr_arg _ <| funext <|
    fun _ ↦ Category.comp_id _
  associativity f gs hs := by
    apply (Category.assoc _ _ _).trans
    apply whisker_eq
    apply LTtoAC.coproduct_iso_inv_inj
    apply Eq.symm
    apply (LTtoAC.coproduct_iso_hom_inv_id _ _).trans
    funext i
    apply (eq_whisker (congr_fun (LTtoAC.coproduct_iso_hom_inv_id F gs) i).symm _).trans
    simp only [LTtoAC.coproduct_iso_inv, Category.assoc]
    rfl


protected theorem map_hom_comm_iso {A B : LawvereTheory.{v₂, u₁, u₂}} (f : A ⟶ B) {m n : ℕ}
    (hs : Fin m → (LTtoAC.obj A.F).c n) : LTtoAC.coproduct_iso_hom B.F
    (fun i ↦ eqToHom (f.obj_comm _) ≫ f.G.map (hs i) ≫ eqToHom (f.obj_comm _).symm) =
    eqToHom (f.obj_comm _) ≫ f.G.map (LTtoAC.coproduct_iso_hom A.F hs) ≫
    eqToHom (f.obj_comm _).symm := by
  induction m with
  | zero => exact (LawvereStruct.initial_uniq _).symm
  | succ m ih =>
    simp only [LTtoAC.coproduct_iso_hom, LTtoAC.coproduct_iso_hom_aux]
    apply Eq.symm
    apply LawvereStruct.coproduct_uniq
    · apply (eq_whisker (f.hom_comm _) _).trans
      simp only [← Functor.map_comp_assoc, Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
        Category.id_comp]
      exact (_ ≫= congr_arg f.G.map (LawvereStruct.coproduct_fac_left
        (LTtoAC.coproduct_iso_hom_aux A.F (hs ∘ Fin.castSucc)) (hs (Fin.last m))) =≫ _).trans <|
        Eq.symm <| ih _
    · apply (eq_whisker (f.hom_comm _) _).trans
      simp only [← Functor.map_comp_assoc, Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
        Category.id_comp]
      exact _ ≫= congr_arg f.G.map (LawvereStruct.coproduct_fac_right
        (LTtoAC.coproduct_iso_hom_aux A.F (hs ∘ Fin.castSucc)) (hs (Fin.last m))) =≫ _


protected def map {A B : LawvereTheory.{v₂, u₁, u₂}} (f : A ⟶ B) :
    LTtoAC.obj A.F ⟶ LTtoAC.obj B.F where
  hom g := eqToHom (f.obj_comm _) ≫ f.G.map g ≫ eqToHom (f.obj_comm _).symm
  υ_comm _ := Eq.symm <| f.hom_comm _
  μ_comm g hs := HEq.eq <| (eqToHom_comp_heq _ _).trans <| (comp_eqToHom_heq _ _).trans <|
    (f.G.map_comp g _).heq.trans <| HEq.symm <| (Category.assoc _ _ _).heq.trans <|
    (eqToHom_comp_heq _ _).trans <| (Category.assoc _ _ _).heq.trans <| whisker_heq
    (f.G.map g) _ _ (f.obj_comm _) <| (eqToHom_comp_heq _ _).trans <|
    (conj_eqToHom_iff_heq _ _ (f.obj_comm _) (f.obj_comm _)).mp <|
    LTtoAC.map_hom_comm_iso f hs


def LT_func_AC : LawvereTheory.{v₂, u₁, u₂} ⥤ AbstractClone.{v₂} where
  obj A := LTtoAC.obj A.F
  map f := LTtoAC.map f
  map_id A := AbstractClone.Hom.ext <| funext <| fun _ ↦ funext <| fun f ↦ Eq.symm <|
    (AbstractClone.Hom.id_app _ _).trans <| Eq.symm <| (eqToHom_comp_iff (LawvereTheory.Hom.obj_comm
    (𝟙 A) _).symm _ _).mpr <| (comp_eqToHom_iff (LawvereTheory.Hom.obj_comm (𝟙 A) _) _ _).mpr <|
    Eq.symm <| (Category.assoc _ _ _).trans <| Eq.symm <| (LawvereTheory.Hom.id_map _ _).trans <|
    (conj_eqToHom_iff_heq f f _ rfl).mpr <| HEq.refl _
  map_comp f g := AbstractClone.Hom.ext <| funext <| fun _ ↦ funext <| fun _ ↦
    (_ ≫= LawvereTheory.Hom.comp_map f g _ =≫ _).trans <| by simp [LTtoAC.map] ; rfl


end LTtoAC

end AlgebraicTheories

end CategoryTheory

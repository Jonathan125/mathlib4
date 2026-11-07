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


protected def T (_ : AbstractClone.{u}) : Type u := ULift.{u} ℕ

namespace T

protected def mk (A : AbstractClone.{u}) : ℕ → ACtoLT.T A := ULift.up

protected def len (A : AbstractClone.{u}) : ACtoLT.T A → ℕ := ULift.down

end T


@[reducible]
protected instance Cat (A : AbstractClone.{u}) : SmallCategory.{u} (ACtoLT.T A) where
  Hom X Y := Fin X.len → A.c Y.len
  id X := A.υ
  comp f g := fun i ↦ A.μ (f i) g

namespace Cat

protected theorem hom_comp_app {A : AbstractClone.{u}} {X Y Z : ACtoLT.T A} (f : X ⟶ Y) (g : Y ⟶ Z)
    (i : Fin X.len) : (f ≫ g) i = A.μ (f i) g :=
  rfl


end Cat

protected def F (A : AbstractClone.{u}) : FintypeCat.Skeleton.{u} ⥤ ACtoLT.T A where
  obj := id
  map f := fun i ↦ A.υ (f ⟨i⟩).down
  map_comp f g :=
    funext <| fun i ↦ Eq.symm <| (ACtoLT.Cat.hom_comp_app _ _ i).trans <| A.projection _ _


protected instance F_struct (A : AbstractClone.{u}) : LawvereStruct.{u, u, u} (ACtoLT.F A) where
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
  F := ACtoLT.F A

end ACtoLT


-- @[reducible]
-- def F : 𝔸ℂ.{u} ⥤ 𝕃𝕋.{u, u} where
--   obj := F_obj
--   map {C₁ C₂ : 𝔸ℂ} (f : C₁ ⟶ C₂) := {
--     F := {
--       obj (n : 𝔽') := n
--       map {m n : 𝔽'} (g : tuple m.down (C₁.c n.down)) :=
--         tuple.mk λ i ↦ f.c_hom n.down (g.proj i)

--       map_id (n : 𝔽') := by
--         simp
--         apply tuple.ext
--         intro i
--         unfold CategoryStruct.id Category.toCategoryStruct F_obj F_cat
--         simp
--         rw [f.υ_hom]

--       map_comp
--         {m n k : 𝔽'}
--         (g : tuple m.down (C₁.c n.down))
--         (h : tuple n.down (C₁.c k.down))
--       := by
--         simp
--         apply tuple.ext
--         intro i
--         unfold comp Category.toCategoryStruct F_obj F_cat
--         simp
--         rw [f.μ_hom]
--     }

--     struct_comm := by
--       apply Functor.hext
--       . intro n
--         simp
--         rfl
--       . intro m n g
--         simp
--         apply tuple.ext
--         intro i
--         unfold F_obj
--         simp
--         unfold 𝕃𝕋.struct F_law_struct F_struct F_prestruct
--         simp
--         rw [f.υ_hom]
--   }

--   map_id (C : 𝔸ℂ) := by
--     simp
--     apply 𝕃𝕋_hom.ext
--     apply Functor.hext
--     . intro m
--       rfl
--     . intro m n f
--       simp

--   map_comp {C₁ C₂ C₃ : 𝔸ℂ} (f : C₁ ⟶ C₂) (g : C₂ ⟶ C₃) := by
--     simp
--     apply 𝕃𝕋_hom.ext
--     simp
--     apply Functor.hext
--     . intro m
--       rfl
--     . intro m n f
--       simp

end AlgebraicTheories

end CategoryTheory

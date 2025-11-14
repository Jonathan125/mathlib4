import Mathlib.CategoryTheory.Closed.Cartesian
import Mathlib.CategoryTheory.IndexCategory.Exponentials


namespace CategoryTheory

namespace IndexCategory

open Limits


namespace Terminal

def terminal : IsTerminal one where
  lift s := to_one s.pt
  uniq _ _ _ := to_one_ext _ _

instance hasInitial : HasTerminal IndexCategory := terminal.hasTerminal

end Terminal


namespace BinaryProducts

def binary_fan (m n : IndexCategory) : BinaryFan m n := BinaryFan.mk π₁ π₂

def binary_product {m n : IndexCategory} : IsLimit (binary_fan m n) :=
  BinaryFan.isLimitMk (fun s ↦ pair_hom s.fst s.snd)
    (fun _ ↦ pair_comp_π₁ _ _) (fun _ ↦ pair_comp_π₂ _ _) (fun _ _ ↦ pair_uniq)

instance hasLimitPair {m n : IndexCategory} : HasLimit (pair m n) :=
  HasLimit.mk ⟨_, binary_product⟩

instance hasBinaryProducts : HasBinaryProducts IndexCategory :=
  hasBinaryProducts_of_hasLimit_pair IndexCategory

end BinaryProducts


namespace Monoidal

open CartesianMonoidalCategory Terminal BinaryProducts

instance cartesianMonoidal : CartesianMonoidalCategory IndexCategory :=
  ofChosenFiniteProducts (LimitCone.mk _ terminal) (fun _ _ ↦ LimitCone.mk _ binary_product)

end Monoidal


section Closed

open MonoidalCategory BinaryProducts Exponentials

def unit {m : IndexCategory} : 𝟭 IndexCategory ⟶ tensorLeft m ⋙ expFunc m where
  app n := cur swap
  naturality n k f := by
    simp [expFunc]
    apply cur_ext
    simp [comp_prod_id, -comp_prod_comp]
    exact swap_nat _ _

def counit {m : IndexCategory} : expFunc m ⋙ tensorLeft m ⟶ 𝟭 IndexCategory where
  app n := swap ≫ eval
  naturality n k f := by
    simp [expFunc]
    apply (swap_nat_assoc _ _ _).trans
    simp

instance exponentiable {m : IndexCategory} : Exponentiable m where
  rightAdj := expFunc m
  adj := {
    unit := unit
    counit := counit
    left_triangle_components n := by
      simp [unit, counit]
      apply (swap_nat_assoc _ _ _).trans
      simp
      rfl
    right_triangle_components n := by
      simp [unit, counit, expFunc]
      apply cur_ext
      simp [comp_prod_id, -comp_prod_comp, -comp_prod_comp_assoc]
  }

instance closed : CartesianClosed IndexCategory :=
  CartesianClosed.mk IndexCategory (fun _ ↦ exponentiable)

end Closed

end IndexCategory

end CategoryTheory

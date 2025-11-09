import Mathlib.CategoryTheory.Closed.Cartesian
import Mathlib.CategoryTheory.IndexCategory.Exponentials


namespace CategoryTheory

namespace IndexCategory

open 𝔽 Limits


section Terminal

def terminal : IsTerminal one where
  lift s := to_one s.pt
  uniq _ _ _ := one_ext _ _

instance hasInitial : HasTerminal 𝔽 := terminal.hasTerminal

end Terminal


section BinaryProducts

open BinaryFan HasLimit

def binary_fan (m n : 𝔽) : BinaryFan m n := mk π₁ π₂

def binary_product {m n : 𝔽} : IsLimit (binary_fan m n) :=
  isLimitMk (fun s ↦ pair_hom s.fst s.snd)
    (fun _ ↦ pair_comp_π₁ _ _) (fun _ ↦ pair_comp_π₂ _ _) (fun _ ↦ pair_hom_ext _ _)

instance hasLimitPair {m n : 𝔽} : HasLimit (pair m n) :=
  mk ⟨_, binary_product⟩

instance hasBinaryProducts : HasBinaryProducts 𝔽 :=
  hasBinaryProducts_of_hasLimit_pair 𝔽

end BinaryProducts


section Monoidal

open CartesianMonoidalCategory

instance cartesianMonoidal : CartesianMonoidalCategory 𝔽 := ofChosenFiniteProducts
  (LimitCone.mk _ terminal) (fun _ _ ↦ LimitCone.mk _ binary_product)

end Monoidal


section Closed

open MonoidalCategory

def unit {m : 𝔽} : 𝟭 𝔽 ⟶ tensorLeft m ⋙ expFunc m where
  app n := cur swap
  naturality n k f := by
    simp [expFunc]
    apply cur_ext
    rw [comp_prod_id, Category.assoc, cur_id_comp_eval]
    rw [comp_prod_id, Category.assoc, cur_id_comp_eval]
    rw [<-Category.assoc, cur_id_comp_eval]
    unfold swap
    rw [comp_pair_hom, pair_comp_π₁, pair_comp_π₂]
    change _ = _ ≫ prod_hom (𝟙 m) f
    exact (pair_hom_ext _ _ _ (by simp) (by simp)).symm

def counit {m : 𝔽} : expFunc m ⋙ tensorLeft m ⟶ 𝟭 𝔽 where
  app n := swap ≫ eval
  naturality n k f := by
    simp [expFunc]
    change prod_hom (𝟙 m) _ ≫ _ = _
    rw [<-Category.assoc, prod_swap_nat]
    rw [Category.assoc, cur_id_comp_eval]

instance exponentiable {m : 𝔽} : Exponentiable m where
  rightAdj := expFunc m
  adj := {
    unit := unit
    counit := counit
    left_triangle_components n := by
      simp [unit, counit]
      change prod_hom (𝟙 m) _ ≫ _ = _
      rw [<-Category.assoc, prod_swap_nat]
      rw [Category.assoc, cur_id_comp_eval]
      unfold swap
      simp [comp_pair_hom]
      exact (pair_hom_ext _ _ _ rfl rfl).symm
    right_triangle_components n := by
      simp [unit, counit, expFunc]
      apply cur_ext
      rw [id_prod_id, comp_prod_id]
      rw [Category.assoc, comp_prod_id]
      rw [Category.assoc, cur_id_comp_eval]
      rw [cur_id_comp_eval_assoc, Category.assoc]
      rw [cur_id_comp_eval_assoc]
      rw [<-Category.assoc]
      apply eq_whisker
      unfold swap
      simp [comp_pair_hom]
      exact (pair_hom_ext _ _ _ rfl rfl).symm
  }

instance closed : CartesianClosed 𝔽 := CartesianClosed.mk 𝔽 (fun _ ↦ exponentiable)

end Closed

end IndexCategory

end CategoryTheory

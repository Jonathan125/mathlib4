import Mathlib.Data.Nat.Basic
import Mathlib.Order.Basic
import Mathlib.CategoryTheory.IndexCategory.Coproducts
import Mathlib.CategoryTheory.IndexCategory.Products


namespace CategoryTheory

namespace IndexCategory

section Exponential

open 𝔽 CategoryTheory Nat

def hom_to_exp {m n : 𝔽} (f : m ⟶ n) : (n ^ m).fin :=
  match m with
  | 0 => Fin.cast (Nat.pow_zero n).symm 0
  | m + 1 => Fin.cast (Nat.pow_succ n m).symm
    (mul_fin_mul (hom_to_exp (@ι₁ _ 1 ≫ f)) (f (last m)))

def exp_to_hom {m n : 𝔽} (i : (n ^ m).fin) : m ⟶ n :=
  match m with
  | 0 => zero_to n
  | m + 1 => [exp_to_hom (π₁ (Fin.cast (Nat.pow_succ n m) i)),
    const_hom (π₂ (Fin.cast (Nat.pow_succ n m) i))]

lemma hom_to_exp_to_hom_id {m n : 𝔽} (f : m ⟶ n) : exp_to_hom (hom_to_exp f) = f := by
  induction m with
  | zero => exact zero_ext _ _
  | succ m ih =>
    apply @match_ext _ 1
    · apply (ι₁_comp_match _ _).trans
      rw [<-ih (@ι₁ _ 1 ≫ f)]
      exact congr_arg _ (π₁_mul_fin_mul _ _)
    · apply (ι₂_comp_match _ _).trans
      funext i
      apply Fin.eq_of_val_eq
      simp [const_hom, hom_to_exp]
      rw [π₂_mul_fin_mul]
      apply congr_arg
      apply congr_arg
      apply Fin.eq_of_val_eq
      simp [ι₂]

lemma exp_to_hom_to_exp_id {m n : 𝔽} (i : (n ^ m).fin) : hom_to_exp (exp_to_hom i) = i := by
  induction m with
  | zero => exact Fin.subsingleton_one.elim _ _
  | succ m ih =>
    unfold exp_to_hom hom_to_exp
    apply Fin.eq_of_val_eq
    simp [ih]
    exact div_add_mod _ _

def eval {m n : 𝔽} : n ^ m * m ⟶ n :=
  fun i ↦ exp_to_hom (π₁ i) (π₂ i)

def cur {k m n : 𝔽} (f : k * m ⟶ n) : k ⟶ n ^ m :=
  fun i ↦ hom_to_exp (fun j ↦ f (mul_fin_mul i j))

@[reassoc (attr := simp)]
lemma cur_id_comp_eval {k m n : 𝔽} (f : k * m ⟶ n) : prod_hom (cur f) (𝟙 m) ≫ eval = f := by
  funext i
  change exp_to_hom ((pair_hom _ _ ≫ π₁) i) _ = _
  rw [pair_comp_π₁]
  simp [cur, hom_to_exp_to_hom_id,]
  apply congr_arg
  change mul_fin_mul _ ((pair_hom _ _ ≫ π₂) _) = _
  rw [pair_comp_π₂]
  exact Fin.eq_of_val_eq (div_add_mod _ _)

lemma cur_uniq {k m n : 𝔽} (f : k * m ⟶ n) (g : k ⟶ n ^ m) :
    prod_hom g (𝟙 m) ≫ eval = f → g = cur f
  := by
    intro h
    funext i
    apply Function.LeftInverse.injective exp_to_hom_to_exp_id
    simp [cur]
    rw [hom_to_exp_to_hom_id]
    rw [<-h]
    funext j
    simp [eval, prod_hom, pair_hom]
    simp [π₁_mul_fin_mul, π₂_mul_fin_mul]

lemma cur_ext {k m n : 𝔽} (f g : k ⟶ n ^ m) :
    prod_hom f (𝟙 m) ≫ eval = prod_hom g (𝟙 m) ≫ eval → f = g
  := by
    intro h
    calc
     _ = cur (prod_hom f (𝟙 m) ≫ eval) := cur_uniq _ _ rfl
     _ = cur (prod_hom g (𝟙 m) ≫ eval) := congr_arg _ h
     _ = _ := (cur_uniq _ _ rfl).symm

def expFunc (m : 𝔽) : 𝔽 ⥤ 𝔽 where
  obj n := n ^ m
  map f := cur (eval ≫ f)
  map_id n := by apply (cur_uniq _ _ _).symm ; simp [id_prod_id]
  map_comp f g := by
    apply (cur_uniq _ _ _).symm
    rw [comp_prod_id, Category.assoc, cur_id_comp_eval]
    rw [<-Category.assoc, cur_id_comp_eval]
    exact Category.assoc _ _ _

end Exponential

end IndexCategory

end CategoryTheory

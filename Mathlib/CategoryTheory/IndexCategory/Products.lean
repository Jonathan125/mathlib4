import Init.Data.Nat.Div.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Order.Basic
import Mathlib.CategoryTheory.IndexCategory.Defs


namespace CategoryTheory

namespace IndexCategory

section BinaryProducts

open Nat Fin

/-
Re-factor to namespace BinaryProducts
Use protected and export (see mathlib examples)
Rename cast_left / cast_right to cast_initial_segment / cast_concluding_segment

Refactor multiplication morphisms to special case of finite coproducts where all
values are equal?
-/


theorem right_ne_zero_of_mul_fin {m n : IndexCategory} (i : Fin (m * n).len) : n.len ≠ 0 :=
  Nat.ne_zero_of_mul_ne_zero_right (Nat.ne_zero_of_lt (i.isLt.trans_eq mul_len))

theorem right_lt_zero_of_mul_fin {m n : IndexCategory} (i : Fin (m * n).len) : 0 < n.len :=
  Nat.ne_zero_iff_zero_lt.mp (right_ne_zero_of_mul_fin i)

theorem div_right_lt_left_of_mul_fin {m n : IndexCategory} (i : Fin (m * n).len) :
    i.val / n.len < m.len :=
  (div_lt_iff_lt_mul (right_lt_zero_of_mul_fin i)).mpr (i.isLt.trans_eq mul_len)

def mul_to_quotient {m n : IndexCategory} (i : Fin (m * n).len) : Fin m.len :=
  ⟨i.val / n.len, div_right_lt_left_of_mul_fin i⟩

def mul_to_remainder {m n : IndexCategory} (i : Fin (m * n).len) : Fin n.len :=
  ⟨i.val % n.len, mod_lt _ (right_lt_zero_of_mul_fin i)⟩

@[simp]
theorem mul_to_quotient_val {m n : IndexCategory} (i : Fin (m * n).len) :
    (mul_to_quotient i).val = i.val / n.len :=
  rfl

@[simp]
theorem mul_to_remainder_val {m n : IndexCategory} (i : Fin (m * n).len) :
    (mul_to_remainder i).val = i.val % n.len :=
  rfl

def π₁ {m n : IndexCategory} : m * n ⟶ m :=
  Hom.mk mul_to_quotient

def π₂ {m n : IndexCategory} : m * n ⟶ n :=
  Hom.mk mul_to_remainder

@[simp]
theorem π₁_toFun_apply_val {m n : IndexCategory} (i : Fin (m * n).len) :
    (π₁.toFun i).val = i.val / n.len :=
  congr_arg _ <| Hom.toFun_mk_apply _ _

@[simp]
theorem π₂_toFun_apply_val {m n : IndexCategory} (i : Fin (m * n).len) :
    (π₂.toFun i).val = i.val % n.len :=
  congr_arg _ <| Hom.toFun_mk_apply _ _

theorem right_mul_left_val_add_right_val_lt_mul {m n : IndexCategory} (i : Fin m.len)
    (j : Fin n.len) : n.len * i.val + j.val < (m * n).len :=
  (Nat.add_lt_add_iff_left.mpr j.isLt).trans_le <|
    ((mul_add_one n.len i.val).symm.trans (Nat.mul_comm _ _)).le.trans <|
    (mul_le_mul_right _ (succ_le_of_lt i.isLt)).trans_eq mul_len.symm

def quotient_remainder_to_mul {m n : IndexCategory} (i : Fin m.len) (j : Fin n.len) :
    Fin (m * n).len :=
  ⟨n.len * i.val + j.val, right_mul_left_val_add_right_val_lt_mul i j⟩

@[simp]
theorem quotient_remainder_to_mul_val {m n : IndexCategory} (i : Fin m.len) (j : Fin n.len) :
    (quotient_remainder_to_mul i j).val = n.len * i.val + j.val :=
  rfl

@[simp]
theorem π₁_toFun_quotient_remainder_to_mul_id {m n : IndexCategory} (i : Fin m.len)
    (j : Fin n.len) : π₁.toFun (quotient_remainder_to_mul i j) = i := by
  ext
  simp
  apply (Nat.mul_add_div (Nat.ne_zero_iff_zero_lt.mp (Nat.ne_zero_of_lt j.isLt)) _ _).trans
  exact congr_arg _ (Nat.div_eq_of_lt j.isLt)

@[simp]
theorem π₂_toFun_quotient_remainder_to_mul_id {m n : IndexCategory} (i : Fin m.len)
    (j : Fin n.len) : π₂.toFun (quotient_remainder_to_mul i j) = j := by
  ext
  simp
  exact mod_eq_of_lt j.isLt

variable {k m n : IndexCategory} (f : k ⟶ m) (g : k ⟶ n)

def pair_hom : k ⟶ m * n :=
  Hom.mk <| fun i ↦ quotient_remainder_to_mul (f.toFun i) (g.toFun i)

@[simp]
theorem pair_hom_toFun_apply (i : Fin k.len) :
    (pair_hom f g).toFun i = quotient_remainder_to_mul (f.toFun i) (g.toFun i) :=
  Hom.toFun_mk_apply _ _

@[reassoc (attr := simp)]
theorem pair_comp_π₁ : pair_hom f g ≫ π₁ = f :=
  by ext _ ; simp

@[reassoc (attr := simp)]
theorem pair_comp_π₂ : pair_hom f g ≫ π₂ = g :=
  by ext _ ; simp

theorem pair_hom_uniq (h : k ⟶ m * n) : h ≫ π₁ = f → h ≫ π₂ = g → h = pair_hom f g :=
  fun h₁ h₂ ↦ by ext _ ; simp [<-h₁, <-h₂] ; exact (div_add_mod _ n.len).symm

/-
Todo: use congr_arg₂ instead of calc
-/
lemma pair_ext {k m n : 𝔽} (f g : k ⟶ m * n) :
    f ≫ π₁ = g ≫ π₁ → f ≫ π₂ = g ≫ π₂ → f = g
  := by
    intro h₁ h₂
    calc
      _ = pair_hom (f ≫ π₁) (f ≫ π₂) := pair_hom_uniq _ _ _ rfl rfl
      _ = pair_hom (g ≫ π₁) (g ≫ π₂) := congr_arg₂ _ h₁ h₂
      _ = _ := (pair_hom_uniq _ _ _ rfl rfl).symm

@[reducible]
def prod_hom {m n k l : 𝔽} (f : m ⟶ k) (g : n ⟶ l) : m * n ⟶ k * l :=
  pair_hom (π₁ ≫ f) (π₂ ≫ g)

lemma id_prod_id {m n : 𝔽} : prod_hom (𝟙 m) (𝟙 n) = 𝟙 (m * n) :=
  (pair_hom_ext _ _ _ (by simp) (by simp)).symm

lemma comp_prod_id {m n k l : 𝔽} (f : m ⟶ n) (g : n ⟶ k) :
    prod_hom (f ≫ g) (𝟙 l) = prod_hom f (𝟙 l) ≫ prod_hom g (𝟙 l)
  :=
    (pair_hom_ext _ _ _ (by simp) (by simp)).symm

lemma comp_pair_hom {m n k l : 𝔽} (h : k ⟶ l) (f : l ⟶ m) (g : l ⟶ n) :
    h ≫ pair_hom f g = pair_hom (h ≫ f) (h ≫ g)
  :=
    (pair_hom_ext _ _ _ (by simp) (by simp))

lemma comp_prod_comp {m₁ n₁ k₁ m₂ n₂ k₂ : 𝔽} (f₁ : m₁ ⟶ n₁) (g₁ : n₁ ⟶ k₁)
  (f₂ : m₂ ⟶ n₂) (g₂ : n₂ ⟶ k₂) :
    prod_hom (f₁ ≫ g₁) (f₂ ≫ g₂) = prod_hom f₁ f₂ ≫ prod_hom g₁ g₂
  :=
    (pair_hom_ext _ _ _ (by simp) (by simp)).symm

@[reducible]
def swap {m n : 𝔽} : m * n ⟶ n * m := pair_hom π₂ π₁

lemma prod_swap_nat {m n k l : 𝔽} (f : m ⟶ k) (g : n ⟶ l) :
    prod_hom f g ≫ swap = swap ≫ prod_hom g f
  :=
    pair_ext _ _ (by simp) (by simp)



-- lemma right_ne_zero_of_mul_fin {m n : 𝔽} (i : (m * n).fin) : n ≠ 0 :=
--   Nat.ne_zero_of_mul_ne_zero_right (Nat.ne_zero_of_lt i.isLt)

-- lemma right_lt_zero_of_mul_fin {m n : 𝔽} (i : (m * n).fin) : 0 < n :=
--   Nat.ne_zero_iff_zero_lt.mp (right_ne_zero_of_mul_fin i)

-- lemma div_right_lt_left_of_mul_fin {m n : 𝔽} (i : (m * n).fin) : i.val / n < m :=
--   (div_lt_iff_lt_mul (right_lt_zero_of_mul_fin i)).mpr i.isLt

-- def π₁ {m n : 𝔽} : m * n ⟶ m :=
--   fun i ↦ ⟨i.val / n, div_right_lt_left_of_mul_fin i⟩

-- def π₂ {m n : 𝔽} : m * n ⟶ n :=
--   fun i ↦ ⟨i.val % n, mod_lt _ (right_lt_zero_of_mul_fin i)⟩

-- lemma right_mul_val_add_val_lt_mul {m n : 𝔽} (i : m.fin) (j : n.fin) :
--     n * i.val + j.val < m * n
--   := by
--     apply (Nat.add_lt_add_iff_left.mpr j.isLt).trans_le
--     apply ((mul_add_one n i.val).symm.trans (Nat.mul_comm _ _)).le.trans
--     exact mul_le_mul_right _ (succ_le_of_lt i.isLt)

-- def mul_fin_mul {m n : 𝔽} (i : m.fin) (j : n.fin) : (m * n).fin :=
--   ⟨n * i.val + j.val, right_mul_val_add_val_lt_mul i j⟩

-- lemma π₁_mul_fin_mul {m n : 𝔽} (i : m.fin) (j : n.fin) : π₁ (mul_fin_mul i j) = i := by
--   apply eq_of_val_eq
--   simp [mul_fin_mul, π₁]
--   apply (Nat.mul_add_div (Nat.ne_zero_iff_zero_lt.mp (Nat.ne_zero_of_lt j.isLt)) _ _).trans
--   exact congr_arg _ (Nat.div_eq_of_lt j.isLt)

-- lemma π₂_mul_fin_mul {m n : 𝔽} (i : m.fin) (j : n.fin) : π₂ (mul_fin_mul i j) = j := by
--   apply eq_of_val_eq
--   simp [mul_fin_mul, π₂]
--   exact mod_eq_of_lt j.isLt

-- variable {k m n : 𝔽} (f : k ⟶ m) (g : k ⟶ n)

-- def pair_hom : k ⟶ m * n := fun i ↦ mul_fin_mul (f i) (g i)

-- @[reassoc (attr := simp)]
-- lemma pair_comp_π₁ : pair_hom f g ≫ π₁ = f := funext (fun _ ↦ π₁_mul_fin_mul _ _)

-- @[reassoc (attr := simp)]
-- lemma pair_comp_π₂ : pair_hom f g ≫ π₂ = g := funext (fun _ ↦ π₂_mul_fin_mul _ _)

-- lemma pair_hom_ext (h : k ⟶ m * n) : h ≫ π₁ = f → h ≫ π₂ = g → h = pair_hom f g :=
--   fun h₁ h₂ ↦ funext (fun _ ↦ eq_of_val_eq ((div_add_mod _ n).symm.trans
--     (congr_arg₂ (fun f' g' ↦ (pair_hom f' g' _).val) h₁ h₂)))

-- lemma pair_ext {k m n : 𝔽} (f g : k ⟶ m * n) :
--     f ≫ π₁ = g ≫ π₁ → f ≫ π₂ = g ≫ π₂ → f = g
--   := by
--     intro h₁ h₂
--     calc
--       _ = pair_hom (f ≫ π₁) (f ≫ π₂) := pair_hom_ext _ _ _ rfl rfl
--       _ = pair_hom (g ≫ π₁) (g ≫ π₂) := congr_arg₂ _ h₁ h₂
--       _ = _ := (pair_hom_ext _ _ _ rfl rfl).symm

-- @[reducible]
-- def prod_hom {m n k l : 𝔽} (f : m ⟶ k) (g : n ⟶ l) : m * n ⟶ k * l :=
--   pair_hom (π₁ ≫ f) (π₂ ≫ g)

-- lemma id_prod_id {m n : 𝔽} : prod_hom (𝟙 m) (𝟙 n) = 𝟙 (m * n) :=
--   (pair_hom_ext _ _ _ (by simp) (by simp)).symm

-- lemma comp_prod_id {m n k l : 𝔽} (f : m ⟶ n) (g : n ⟶ k) :
--     prod_hom (f ≫ g) (𝟙 l) = prod_hom f (𝟙 l) ≫ prod_hom g (𝟙 l)
--   :=
--     (pair_hom_ext _ _ _ (by simp) (by simp)).symm

-- lemma comp_pair_hom {m n k l : 𝔽} (h : k ⟶ l) (f : l ⟶ m) (g : l ⟶ n) :
--     h ≫ pair_hom f g = pair_hom (h ≫ f) (h ≫ g)
--   :=
--     (pair_hom_ext _ _ _ (by simp) (by simp))

-- lemma comp_prod_comp {m₁ n₁ k₁ m₂ n₂ k₂ : 𝔽} (f₁ : m₁ ⟶ n₁) (g₁ : n₁ ⟶ k₁)
--   (f₂ : m₂ ⟶ n₂) (g₂ : n₂ ⟶ k₂) :
--     prod_hom (f₁ ≫ g₁) (f₂ ≫ g₂) = prod_hom f₁ f₂ ≫ prod_hom g₁ g₂
--   :=
--     (pair_hom_ext _ _ _ (by simp) (by simp)).symm

-- @[reducible]
-- def swap {m n : 𝔽} : m * n ⟶ n * m := pair_hom π₂ π₁

-- lemma prod_swap_nat {m n k l : 𝔽} (f : m ⟶ k) (g : n ⟶ l) :
--     prod_hom f g ≫ swap = swap ≫ prod_hom g f
--   :=
--     pair_ext _ _ (by simp) (by simp)

end BinaryProducts

end IndexCategory

end CategoryTheory

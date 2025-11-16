/-
Copyright (c) 2025 Jonathan Konig. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Konig
-/
import Init.Data.Nat.Div.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Order.Basic
import Mathlib.CategoryTheory.IndexCategory.Basic


namespace CategoryTheory

namespace IndexCategory

namespace BinaryProducts

open Nat Fin

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

def pair_hom {k m n : IndexCategory} (f : k ⟶ m) (g : k ⟶ n) : k ⟶ m * n :=
  Hom.mk <| fun i ↦ quotient_remainder_to_mul (f.toFun i) (g.toFun i)

@[simp]
theorem pair_hom_toFun_apply {k m n : IndexCategory} (f : k ⟶ m) (g : k ⟶ n) (i : Fin k.len) :
    (pair_hom f g).toFun i = quotient_remainder_to_mul (f.toFun i) (g.toFun i) :=
  Hom.toFun_mk_apply _ _

@[reassoc (attr := simp)]
theorem pair_comp_π₁ {k m n : IndexCategory} (f : k ⟶ m) (g : k ⟶ n) : pair_hom f g ≫ π₁ = f :=
  by ext _ ; simp

@[reassoc (attr := simp)]
theorem pair_comp_π₂ {k m n : IndexCategory} (f : k ⟶ m) (g : k ⟶ n) : pair_hom f g ≫ π₂ = g :=
  by ext _ ; simp

theorem pair_uniq {k m n : IndexCategory} {f : k ⟶ m} {g : k ⟶ n} {h : k ⟶ m * n} :
    h ≫ π₁ = f → h ≫ π₂ = g → h = pair_hom f g :=
  fun h₁ h₂ ↦ by ext _ ; simp [<-h₁, <-h₂] ; exact (div_add_mod _ n.len).symm

theorem pair_ext {k m n : IndexCategory} {f g : k ⟶ m * n} :
    f ≫ π₁ = g ≫ π₁ → f ≫ π₂ = g ≫ π₂ → f = g :=
  fun h₁ h₂ ↦ (pair_uniq rfl rfl).trans <| (congr_arg₂ _ h₁ h₂).trans (pair_uniq rfl rfl).symm

@[reducible]
def prod_hom {m n k l : IndexCategory} (f : m ⟶ k) (g : n ⟶ l) : m * n ⟶ k * l :=
  pair_hom (π₁ ≫ f) (π₂ ≫ g)

@[simp]
theorem id_prod_id {m n : IndexCategory} : prod_hom (𝟙 m) (𝟙 n) = 𝟙 (m * n) :=
  Eq.symm <| pair_uniq (by simp) (by simp)

theorem comp_prod_id {m n k l : IndexCategory} (f : m ⟶ n) (g : n ⟶ k) :
    prod_hom (f ≫ g) (𝟙 l) = prod_hom f (𝟙 l) ≫ prod_hom g (𝟙 l) :=
  Eq.symm <| pair_uniq (by simp) (by simp)

theorem comp_pair_hom {m n k l : IndexCategory} (h : k ⟶ l) (f : l ⟶ m) (g : l ⟶ n) :
    h ≫ pair_hom f g = pair_hom (h ≫ f) (h ≫ g) :=
  pair_uniq (by simp) (by simp)

@[reassoc (attr := simp)]
theorem comp_prod_comp {m₁ n₁ k₁ m₂ n₂ k₂ : IndexCategory} (f₁ : m₁ ⟶ n₁) (g₁ : n₁ ⟶ k₁)
    (f₂ : m₂ ⟶ n₂) (g₂ : n₂ ⟶ k₂) :
    prod_hom f₁ f₂ ≫ prod_hom g₁ g₂ = prod_hom (f₁ ≫ g₁) (f₂ ≫ g₂) :=
  pair_uniq (by simp) (by simp)

@[reducible]
def swap {m n : IndexCategory} : m * n ⟶ n * m :=
  pair_hom π₂ π₁

@[reassoc]
theorem swap_nat {m n k l : IndexCategory} (f : m ⟶ k) (g : n ⟶ l) :
    prod_hom f g ≫ swap = swap ≫ prod_hom g f :=
  pair_ext (by simp) (by simp)

@[reassoc (attr := simp)]
theorem swap_swap_id {m n : IndexCategory} : swap ≫ swap = 𝟙 (m * n) :=
  pair_ext (by simp) (by simp)

end BinaryProducts

end IndexCategory

end CategoryTheory

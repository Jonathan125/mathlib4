/-
Copyright (c) 2025 Jonathan Konig. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Konig
-/
import Mathlib.Data.Nat.Basic
import Mathlib.Order.Basic
import Mathlib.CategoryTheory.IndexCategory.Coproducts
import Mathlib.CategoryTheory.IndexCategory.Products


namespace CategoryTheory

namespace IndexCategory

namespace Exponentials

open BinaryCoproducts BinaryProducts Nat

theorem pow_zero (n : IndexCategory) : n ^ zero = one :=
  ext _ _ <| pow_len.trans <| (congr_arg₂ _ rfl zero_len).trans <|
    (Nat.pow_zero n.len).trans one_len.symm

theorem pow_succ (m n : IndexCategory) : n ^ (m + one) = n ^ m * n :=
  ext _ _ <| pow_len.trans <| (congr_arg₂ _ rfl succ_len).trans <|
    (Nat.pow_succ n.len m.len).trans <| (congr_arg₂ _ pow_len.symm rfl).trans <| mul_len.symm

def hom_to_pow_fin {m n : IndexCategory} (f : m ⟶ n) : Fin (n ^ m).len := by
  cases m with
  | zero => exact Fin.cast (congr_arg _ (pow_zero _).symm) fin_one
  | succ m => exact Fin.cast (congr_arg _ (pow_succ _ _).symm) <|
    quotient_remainder_to_mul (hom_to_pow_fin (ι₁ ≫ f)) (f.toFun m.fin_succ_last)

theorem hom_to_pow_fin_zero {n : IndexCategory} (f : zero ⟶ n) :
    hom_to_pow_fin f = Fin.cast (congr_arg _ (pow_zero _).symm) fin_one :=
  by rw [hom_to_pow_fin, IndexCategory.cases_zero]

theorem hom_to_pow_fin_succ {m n : IndexCategory} (f : m + one ⟶ n) :
    hom_to_pow_fin f = Fin.cast (congr_arg _ (pow_succ _ _).symm)
    (quotient_remainder_to_mul (hom_to_pow_fin (ι₁ ≫ f)) (f.toFun m.fin_succ_last)) :=
  by rw [hom_to_pow_fin, IndexCategory.cases_succ]

def pow_fin_to_hom {m n : IndexCategory} (i : Fin (n ^ m).len) : m ⟶ n := by
  cases m with
  | zero => exact zero_to n
  | succ m => exact match_hom (pow_fin_to_hom (π₁.toFun (Fin.cast (congr_arg _ (pow_succ _ _)) i)))
                (one_to (π₂.toFun (Fin.cast (congr_arg _ (pow_succ _ _)) i)))

theorem pow_fin_to_hom_zero {n : IndexCategory} (i : Fin (n ^ zero).len) :
    pow_fin_to_hom i = zero_to n :=
  zero_to_ext _ _

theorem pow_fin_to_hom_succ {m n : IndexCategory} (i : Fin (n ^ (m + one)).len) :
    pow_fin_to_hom i = match_hom
    (pow_fin_to_hom (π₁.toFun (Fin.cast (congr_arg _ (pow_succ _ _)) i)))
    (one_to (π₂.toFun (Fin.cast (congr_arg _ (pow_succ _ _)) i))) :=
  by rw [pow_fin_to_hom, IndexCategory.cases_succ]

@[simp]
theorem hom_to_pow_fin_to_hom_id {m n : IndexCategory} (f : m ⟶ n) :
    pow_fin_to_hom (hom_to_pow_fin f) = f := by
  induction m with
  | zero => exact zero_to_ext _ _
  | succ m ih =>
    apply match_ext
    · simp [pow_fin_to_hom_succ, hom_to_pow_fin_succ]
      exact ih _
    · simp [pow_fin_to_hom_succ, hom_to_pow_fin_succ]
      apply one_to_ext
      simp

@[simp]
theorem pow_fin_to_hom_to_pow_fin_id {m n : IndexCategory} (i : Fin (n ^ m).len) :
    hom_to_pow_fin (pow_fin_to_hom i) = i := by
  induction m with
  | zero =>
    exact (Fin.subsingleton_iff_le_one.mpr ((congr_arg _ (pow_zero n)).trans one_len).le).elim _ _
  | succ m ih =>
    ext
    simp [hom_to_pow_fin_succ, pow_fin_to_hom_succ, ih, div_add_mod]

def eval {m n : IndexCategory} : n ^ m * m ⟶ n :=
  Hom.mk <| fun i ↦ (pow_fin_to_hom (π₁.toFun i)).toFun (π₂.toFun i)

@[simp]
theorem eval_toFun_apply {m n : IndexCategory} (i : Fin (n ^ m * m).len) :
    eval.toFun i = (pow_fin_to_hom (π₁.toFun i)).toFun (π₂.toFun i) :=
  Hom.toFun_mk_apply _ _

def cur {k m n : IndexCategory} (f : k * m ⟶ n) : k ⟶ n ^ m :=
  Hom.mk <| fun i ↦ hom_to_pow_fin <| Hom.mk <| fun j ↦ f.toFun (quotient_remainder_to_mul i j)

@[simp]
theorem cur_toFun_apply {m n k : IndexCategory} (f : k * m ⟶ n) (i : Fin k.len) :
    (cur f).toFun i = hom_to_pow_fin (Hom.mk <| fun j ↦ f.toFun (quotient_remainder_to_mul i j)) :=
  Hom.toFun_mk_apply _ _

@[reassoc (attr := simp)]
theorem cur_prod_id_comp_eval {m n k : IndexCategory} (f : k * m ⟶ n) :
    prod_hom (cur f) (𝟙 m) ≫ eval = f := by
  ext i
  simp
  apply congr_toFun_apply_val
  simp [div_add_mod]

theorem cur_uniq {m n k : IndexCategory} {f : k * m ⟶ n} {g : k ⟶ n ^ m} :
    prod_hom g (𝟙 m) ≫ eval = f → g = cur f := by
  intro h
  ext i : 2
  apply Function.LeftInverse.injective pow_fin_to_hom_to_pow_fin_id
  simp
  rw [<-h]
  simp

theorem cur_ext {m n k : IndexCategory} (f g : k ⟶ n ^ m) :
    prod_hom f (𝟙 m) ≫ eval = prod_hom g (𝟙 m) ≫ eval → f = g :=
  fun h ↦ (cur_uniq rfl).trans <| (congr_arg _ h).trans (cur_uniq rfl).symm

def expFunc (m : IndexCategory) : IndexCategory ⥤ IndexCategory where
  obj n := n ^ m
  map f := cur (eval ≫ f)
  map_id n := (cur_uniq (by simp)).symm
  map_comp f g := (cur_uniq (by rw [comp_prod_id, Category.assoc] ; simp)).symm

end Exponentials

end IndexCategory

end CategoryTheory

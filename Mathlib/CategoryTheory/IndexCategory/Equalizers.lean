/-
Copyright (c) 2025 Jonathan Konig. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Konig
-/
import Mathlib.CategoryTheory.IndexCategory.Coproducts


namespace CategoryTheory

namespace IndexCategory

namespace Equalizers

open BinaryCoproducts Category Nat

@[inline]
protected abbrev last_agree {m n : IndexCategory} (f g : m + one ⟶ n) : Prop :=
  f.toFun m.fin_succ_last = g.toFun m.fin_succ_last

protected def obj {m n : IndexCategory} (f g : m ⟶ n) : IndexCategory := by
  cases m with
  | zero => exact zero
  | succ m =>
    let k : IndexCategory := Equalizers.obj (ι₁ ≫ f) (ι₁ ≫ g)
    exact if Equalizers.last_agree f g then k + one else k

protected theorem obj_zero {n : IndexCategory} (f g : zero ⟶ n) :
    Equalizers.obj f g = zero :=
  by rw [Equalizers.obj, IndexCategory.cases_zero]

protected theorem obj_succ_last_agree {m n : IndexCategory} {f g : m + one ⟶ n}
    (h : Equalizers.last_agree f g) : Equalizers.obj f g = Equalizers.obj (ι₁ ≫ f) (ι₁ ≫ g) + one :=
  by rw [Equalizers.obj, IndexCategory.cases_succ] ; simp [h]

protected theorem obj_succ_not_last_agree {m n : IndexCategory} {f g : m + one ⟶ n}
    (h : ¬ Equalizers.last_agree f g) : Equalizers.obj f g = Equalizers.obj (ι₁ ≫ f) (ι₁ ≫ g) :=
  by rw [Equalizers.obj, IndexCategory.cases_succ] ; simp [h]

protected def hom {m n : IndexCategory} (f g : m ⟶ n) : Equalizers.obj f g ⟶ m := by
  cases m with
  | zero => exact eqHom (Equalizers.obj_zero _ _) ≫ zero_to _
  | succ m =>
    let k : IndexCategory := Equalizers.obj (ι₁ ≫ f) (ι₁ ≫ g)
    let e : k ⟶ m := Equalizers.hom (ι₁ ≫ f) (ι₁ ≫ g)
    exact if h : Equalizers.last_agree f g
    then eqHom (Equalizers.obj_succ_last_agree h) ≫ (e ++ 𝟙 one)
    else eqHom (Equalizers.obj_succ_not_last_agree h) ≫ e ≫ ι₁

protected theorem hom_zero {n : IndexCategory} (f g : zero ⟶ n) :
    Equalizers.hom f g = eqHom (Equalizers.obj_zero _ _) ≫ zero_to _ :=
  by rw [Equalizers.hom, IndexCategory.cases_zero]

protected theorem hom_succ_last_agree {m n : IndexCategory} {f g : m + one ⟶ n}
    (h : Equalizers.last_agree f g) : Equalizers.hom f g =
    eqHom (Equalizers.obj_succ_last_agree h) ≫ (Equalizers.hom (ι₁ ≫ f) (ι₁ ≫ g) ++ 𝟙 one) :=
  by rw [Equalizers.hom, IndexCategory.cases_succ] ; simp [eq_true_intro h]

protected theorem hom_succ_not_last_agree {m n : IndexCategory} {f g : m + one ⟶ n}
    (h : ¬ Equalizers.last_agree f g) : Equalizers.hom f g =
    eqHom (Equalizers.obj_succ_not_last_agree h) ≫ Equalizers.hom (ι₁ ≫ f) (ι₁ ≫ g) ≫ ι₁ :=
  by rw [Equalizers.hom, IndexCategory.cases_succ] ; simp [eq_false_intro h]

protected def uneq {m n : IndexCategory} (f g : m ⟶ n) : m ⟶ Equalizers.obj f g + one := by
  cases m with
  | zero => exact zero_to _
  | succ m =>
    let k : IndexCategory := Equalizers.obj (ι₁ ≫ f) (ι₁ ≫ g)
    let u : m ⟶ k + one := Equalizers.uneq (ι₁ ≫ f) (ι₁ ≫ g)
    exact if h : Equalizers.last_agree f g
    then match_hom (u ≫ (𝟙 k ++ ι₂) ≫ assocIso.inv) (ι₂ ≫ ι₁) ≫
      eqHom (congr_arg (· + one) (Equalizers.obj_succ_last_agree h).symm)
    else match_hom u (one_to k.fin_succ_last) ≫
      eqHom (congr_arg (· + one) (Equalizers.obj_succ_not_last_agree h).symm)

protected theorem uneq_zero {n : IndexCategory} (f g : zero ⟶ n) :
    Equalizers.uneq f g = zero_to _ :=
  zero_to_ext _ _

protected theorem uneq_succ_last_agree {m n : IndexCategory} {f g : m + one ⟶ n}
    (h : Equalizers.last_agree f g) : Equalizers.uneq f g =
    match_hom (Equalizers.uneq (ι₁ ≫ f) (ι₁ ≫ g) ≫ (𝟙 _ ++ ι₂) ≫ assocIso.inv) (ι₂ ≫ ι₁) ≫
    eqHom (congr_arg (· + one) (Equalizers.obj_succ_last_agree h).symm) :=
  by rw [Equalizers.uneq, IndexCategory.cases_succ] ; simp [eq_true_intro h]

protected theorem uneq_succ_not_last_agree {m n : IndexCategory} {f g : m + one ⟶ n}
    (h : ¬ Equalizers.last_agree f g) : Equalizers.uneq f g =
    match_hom (Equalizers.uneq (ι₁ ≫ f) (ι₁ ≫ g)) (one_to (fin_succ_last _)) ≫
    eqHom (congr_arg (· + one) (Equalizers.obj_succ_not_last_agree h).symm) :=
  by rw [Equalizers.uneq, IndexCategory.cases_succ] ; simp [eq_false_intro h]

protected theorem condition {m n : IndexCategory} (f g : m ⟶ n) :
    Equalizers.hom f g ≫ f = Equalizers.hom f g ≫ g := by
  induction m with
  | zero =>
    simp [Equalizers.hom_zero]
    apply whisker_eq
    exact zero_to_ext _ _
  | succ m ih =>
    if h : Equalizers.last_agree f g then
      simp [Equalizers.hom_succ_last_agree h]
      apply whisker_eq
      apply match_ext
      · simp
        exact ih _ _
      · simp
        apply one_to_ext
        simp
        exact Fin.val_eq_of_eq h
    else
      simp [Equalizers.hom_succ_not_last_agree h]
      apply whisker_eq
      exact ih _ _

protected theorem uneq_toFun_apply_val_lt_of_agree {m n : IndexCategory} (f g : m ⟶ n)
    (i : Fin m.len) : f.toFun i = g.toFun i →
    ((Equalizers.uneq f g).toFun i).val < (Equalizers.obj f g).len := by
  induction m with
  | zero => exact elim_zero i
  | succ m ih =>
    intro he
    if h : Equalizers.last_agree f g then
      simp [Equalizers.obj_succ_last_agree h, Equalizers.uneq_succ_last_agree h]
      if hi : i.val < m.len then
        specialize ih (ι₁ ≫ f) (ι₁ ≫ g) (sum_to_initial i hi) (by simp ; exact he)
        simp [hi, ih]
        exact ih.trans_le (Nat.le_succ _)
      else
        simp [hi]
    else
      have hi : i.val < m.len := Nat.lt_of_le_of_ne (le_of_lt_succ (i.isLt.trans_eq succ_len))
        (fun hn ↦ (by obtain rfl : i = m.fin_succ_last := Fin.eq_of_val_eq hn ; exact h he))
      simp [Equalizers.obj_succ_not_last_agree h, Equalizers.uneq_succ_not_last_agree h, hi]
      exact ih (ι₁ ≫ f) (ι₁ ≫ g) (sum_to_initial i hi) (by simp ; exact he)

@[reassoc (attr := simp)]
protected theorem hom_comp_uneq_eq_ι₁ {m n : IndexCategory} (f g : m ⟶ n) :
    Equalizers.hom f g ≫ Equalizers.uneq f g = ι₁ := by
  induction m with
  | zero =>
    simp [Equalizers.hom_zero]
    apply (eqHom_comp_iff _ _ _).mpr
    exact zero_to_ext _ _
  | succ m ih =>
    if h : Equalizers.last_agree f g then
      simp [Equalizers.hom_succ_last_agree h, Equalizers.uneq_succ_last_agree h]
      apply (eqHom_comp_iff _ _ _).mpr
      apply match_ext
      · simp
        rw [<-Category.assoc, ih]
        ext i
        simp
      · ext i
        simp
    else
      simp [Equalizers.hom_succ_not_last_agree h, Equalizers.uneq_succ_not_last_agree h]
      rw [<-(_ ≫= Category.assoc _ _ _), ih]
      ext i
      simp

protected theorem comp_uneq_lt_of_condition {m n k : IndexCategory} (f g : m ⟶ n) (h : k ⟶ m) :
    h ≫ f = h ≫ g →
    ∀ i : Fin k.len, ((h ≫ Equalizers.uneq f g).toFun i).val < (Equalizers.obj f g).len := by
  intro hh i
  simp
  apply Equalizers.uneq_toFun_apply_val_lt_of_agree
  simpa using congr_fun (congr_arg Hom.toFun hh) i

protected def lift {m n k : IndexCategory} {f g : m ⟶ n} {h : k ⟶ m} (hh : h ≫ f = h ≫ g) :
    k ⟶ Equalizers.obj f g :=
  Hom.mk <| fun i ↦ Fin.mk _ <| Equalizers.comp_uneq_lt_of_condition _ _ _ hh i

@[reassoc (attr := simp)]
protected theorem lift_comp_ι₁_eq_post_comp_uneq {m n k : IndexCategory} {f g : m ⟶ n} {h : k ⟶ m}
    (hh : h ≫ f = h ≫ g) : Equalizers.lift hh ≫ ι₁ = h ≫ Equalizers.uneq f g :=
  by ext i ; simp [Equalizers.lift]

@[reassoc]
protected theorem hom_comp_ι₁_nat {m n : IndexCategory} (f g : m ⟶ n) :
    Equalizers.hom f g ≫ ι₁ = ι₁ ≫ (Equalizers.hom f g ++ 𝟙 one) :=
  by ext i ; simp

protected def id_if_eq {m n : IndexCategory} (f g : m ⟶ n) : m ⟶ m + one :=
  Hom.mk <| fun i ↦ if f.toFun i = g.toFun i then ι₁.toFun i else m.fin_succ_last

protected theorem comp_id_if_eq_of_condition {m n k : IndexCategory} {f g : m ⟶ n} {h : k ⟶ m}
    (hh : h ≫ f = h ≫ g) : h ≫ Equalizers.id_if_eq f g = h ≫ ι₁ := by
  ext i
  have h₁ := congr_fun (congr_arg Hom.toFun hh) i
  simp at h₁
  simp [Equalizers.id_if_eq, h₁]

@[reassoc (attr := simp)]
protected theorem ι₁_comp_id_if_eq_succ_nat {m n : IndexCategory} (f g : m + one ⟶ n) :
    ι₁ ≫ Equalizers.id_if_eq f g =
    Equalizers.id_if_eq (ι₁ ≫ f) (ι₁ ≫ g) ≫ match_hom (ι₁ ≫ ι₁) ι₂ := by
  ext i
  if h₁ : ((Equalizers.id_if_eq (ι₁ ≫ f) (ι₁ ≫ g)).toFun i).val < m.len then
    have h₂ : (ι₁ ≫ f).toFun i = (ι₁ ≫ g).toFun i := by
      rw [Equalizers.id_if_eq] at h₁
      dsimp at h₁
      apply by_contradiction
      intro h₂
      rw [ite_cond_eq_false _ _ (eq_false_intro h₂)] at h₁
      apply Nat.not_le_of_lt h₁
      exact Nat.le_refl _
    simp [h₁]
    nth_rewrite 2 [Equalizers.id_if_eq]
    dsimp
    rw [ite_cond_eq_true _ _ (eq_true_intro h₂)]
    simp [Equalizers.id_if_eq]
    simp at h₂
    simp [h₂]
  else
    have h₂ := eq_last_of_not_lt h₁
    simp [Equalizers.id_if_eq] at h₂
    have h₃ : ¬ (ι₁ ≫ f).toFun i = (ι₁ ≫ g).toFun i :=
      not_imp_not.mpr (by simpa using h₂) (Fin.ne_of_val_ne i.isLt.ne)
    nth_rewrite 2 [Equalizers.id_if_eq, comp_toFun]
    dsimp
    rw [ite_cond_eq_false _ _ (eq_false_intro h₃)]
    simp [Equalizers.id_if_eq]
    simp at h₃
    simp [h₃]

@[reassoc (attr := simp)]
protected theorem uneq_comp_hom_sum_id_eq_id_if_eq {m n : IndexCategory} (f g : m ⟶ n) :
    Equalizers.uneq f g ≫ (Equalizers.hom f g ++ 𝟙 one) = Equalizers.id_if_eq f g := by
  induction m with
  | zero => exact zero_to_ext _ _
  | succ m ih =>
    apply match_ext
    · if h : Equalizers.last_agree f g then
        simp [Equalizers.uneq_succ_last_agree h, Equalizers.hom_succ_last_agree h,
          assoc_sum_sum_nat]
        rw [<-Category.comp_id (Equalizers.hom _ _), <-Category.id_comp ι₂]
        rw [<-sum_comp_sum, Category.assoc, <-Category.assoc, ih]
        apply whisker_eq
        ext i
        simp
      else
        simp [Equalizers.uneq_succ_not_last_agree h, Equalizers.hom_succ_not_last_agree h]
        rw [<-Category.id_comp (𝟙 one), <-sum_comp_sum, <-Category.assoc, ih]
        exact _ ≫= congr_arg₂ _ rfl (Category.id_comp _)
    · apply one_to_ext
      if h : Equalizers.last_agree f g then
        simp [Equalizers.uneq_toFun_apply_val_lt_of_agree _ _ _ h]
        simp [Equalizers.uneq_succ_last_agree h, Equalizers.hom_succ_last_agree h]
        simp [Equalizers.id_if_eq, h]
      else
        simp [Equalizers.uneq_succ_not_last_agree h, Equalizers.hom_succ_not_last_agree h]
        simp [Equalizers.id_if_eq, h]

@[simp]
protected theorem lift_hom_id {m n : IndexCategory} {f g : m ⟶ n} :
    Equalizers.lift (Equalizers.condition f g) = 𝟙 (Equalizers.obj f g) :=
  (eq_iff_comp_inj_eq (@ι₁_injective _ one) _ _).mpr <| by simp

@[reassoc (attr := simp)]
protected theorem fac {m n k : IndexCategory} {f g : m ⟶ n} {h : k ⟶ m} (hh : h ≫ f = h ≫ g) :
    Equalizers.lift hh ≫ Equalizers.hom f g = h :=
  (eq_iff_comp_inj_eq (@ι₁_injective _ one) _ _).mpr <| by
    simp [Equalizers.hom_comp_ι₁_nat, -ι₁_comp_match]
    exact Equalizers.comp_id_if_eq_of_condition hh

protected theorem uniq {m n k : IndexCategory} {f g : m ⟶ n} {h : k ⟶ m} (hh : h ≫ f = h ≫ g)
    (s : k ⟶ Equalizers.obj f g) (hs : s ≫ Equalizers.hom f g = h) : s = Equalizers.lift hh :=
  ((s ≫= Equalizers.lift_hom_id).trans (Category.comp_id s)).symm.trans <|
    (eq_iff_comp_inj_eq (@ι₁_injective _ one) _ _).mpr <| by simp [<-hs]

end Equalizers

end IndexCategory

end CategoryTheory

/-
Copyright (c) 2025 Jonathan Konig. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Konig
-/
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.CategoryTheory.Skeletal
import Mathlib.CategoryTheory.IndexCategory.Basic

/-! # The index category is skeletal

In this file, we show that isomorphic objects in the index category are equal. This is accomplished
by first showing that there are no injective functions `Fin (n + 1) → Fin n`. From this, it
follows that for any morphism `f : m ⟶ n`, `Function.Injective f.toFun` implies `m ≤ n`.
-/

namespace CategoryTheory

namespace IndexCategory

namespace Skeletal

theorem to_pred_fun_not_inj {m : ℕ} (f : Fin (m + 1) → Fin m) : ¬ Function.Injective f := by
  apply Function.not_injective_iff.mpr
  induction m with
  | zero => exact (f 0).elim0
  | succ m ih =>
    let j := Fin.find (fun i ↦ (f i.castSucc).val = m)
    if hj : j = none then
      have hlt : ∀ i : Fin (m + 1), (f i.castSucc).val < m :=
        fun _ ↦ Nat.lt_of_le_of_ne (Nat.le_of_lt_succ (Fin.isLt _)) (Fin.find_eq_none_iff.mp hj _)
      specialize ih fun i ↦ ⟨(f i.castSucc).val, hlt i⟩
      apply ih.elim
      intro i ih
      apply ih.elim
      intro i' ih
      simp at ih
      apply Exists.intro i.castSucc
      apply Exists.intro i'.castSucc
      apply And.intro (Fin.eq_of_val_eq ih.left)
      apply Fin.ne_of_val_ne
      simp
      exact Fin.val_ne_of_ne ih.right
    else
      let hs₁ := Option.isSome_iff_ne_none.mpr (Ne.intro hj)
      let i₁ : Fin (m + 2) := (Option.get _ hs₁).castSucc
      let j' := Fin.find (fun i ↦ i ≠ i₁ ∧ (f i).val = m)
      if hj' : j' = none then
        have hlt : ∀ i : Fin (m + 2), i ≠ i₁ → (f i).val < m :=
          fun _ h ↦ Nat.lt_of_le_of_ne (Nat.le_of_lt_succ (Fin.isLt _))
            (not_and.mp (Fin.find_eq_none_iff.mp hj' _) h)
        specialize ih fun i ↦ ⟨(f (i₁.succAbove i)).val, hlt _ (i₁.succAbove_ne _)⟩
        apply ih.elim
        intro i ih
        apply ih.elim
        intro i' ih
        simp at ih
        apply Exists.intro (i₁.succAbove i)
        apply Exists.intro (i₁.succAbove i')
        apply And.intro (Fin.eq_of_val_eq ih.left)
        apply i₁.succAbove_right_inj.ne.mpr (Ne.intro ih.right)
      else
        have hs₂ := Option.isSome_iff_ne_none.mpr (Ne.intro hj')
        let i₂ : Fin (m + 2) := Option.get _ hs₂
        apply Exists.intro i₁
        apply Exists.intro i₂
        have h₁ : (f i₁).val = m := (Fin.find_eq_some_iff.mp (Option.some_get hs₁).symm).left
        have h₂ : i₂ ≠ i₁ ∧ (f i₂).val = m :=
          (Fin.find_eq_some_iff.mp (Option.some_get hs₂).symm).left
        apply And.intro (Fin.eq_of_val_eq (h₁.trans h₂.right.symm))
        exact h₂.left.symm

theorem le_of_inj_fun {m n : ℕ} (f : Fin m → Fin n) :
    Function.Injective f → m ≤ n := by
  intro h
  induction m with
  | zero => exact Nat.zero_le _
  | succ m ih =>
    apply Nat.succ_le_of_lt
    specialize ih (f ∘ Fin.castSucc) (h.comp (Fin.castSucc_injective _))
    apply ih.lt_of_ne
    intro he
    obtain rfl : m = n := he
    exact to_pred_fun_not_inj f h

theorem le_of_toFun_inj {m n : IndexCategory} (f : m ⟶ n) :
    Function.Injective f.toFun → m.len ≤ n.len :=
  le_of_inj_fun f.toFun

theorem eq_of_iso {m n : IndexCategory} (i : m ≅ n) : m = n :=
  ext _ _ <| Nat.le_antisymm (le_of_toFun_inj _ (iso_hom_toFun_injective i)) <|
    le_of_toFun_inj _ <| iso_inv_toFun_injective i

theorem isSkeletal : Skeletal IndexCategory := fun _ _ h ↦ eq_of_iso h.some

end Skeletal

end IndexCategory

end CategoryTheory

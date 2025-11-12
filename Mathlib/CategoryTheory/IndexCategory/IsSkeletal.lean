import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.CategoryTheory.Skeletal
import Mathlib.CategoryTheory.IndexCategory.Defs


namespace CategoryTheory

namespace IndexCategory

lemma to_pred_fun_not_inj {m : ℕ} (f : Fin (m + 1) → Fin m) : ¬ Function.Injective f := by
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

lemma le_of_inj_hom {m n : IndexCategory} (f : m ⟶ n) :
    Function.Injective f.toFun → m.len ≤ n.len := by
  intro h
  induction m with
  | zero => exact zero_len.le.trans (Nat.zero_le _)
  | succ m ih =>
    simp
    apply Nat.succ_le_of_lt
    let g : Fin (m.len + 1) ⟶ Fin n.len := f.toFun ∘ Fin.cast succ_len.symm
    have hg : Function.Injective g := h.comp (Fin.cast_injective _)
    specialize ih (Hom.mk (g ∘ Fin.castSucc))
    specialize ih ((congr_arg Function.Injective (Hom.toFun_mk _)).mpr
      (hg.comp (Fin.castSucc_injective _)))
    apply ih.lt_of_ne
    intro he
    obtain rfl : m = n := ext _ _ he
    exact to_pred_fun_not_inj g hg

lemma eq_of_iso {m n : IndexCategory} (i : m ≅ n) : m = n :=
  ext _ _ <| Nat.le_antisymm (le_of_inj_hom _ (iso_hom_toFun_injective i)) <|
    le_of_inj_hom _ <| iso_inv_toFun_injective i

theorem isSkeletal : Skeletal IndexCategory := fun _ _ h ↦ eq_of_iso h.some

end IndexCategory

end CategoryTheory

/-
Copyright (c) 2025 Jonathan Konig. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Konig
-/
import Mathlib.Data.Nat.Basic
import Mathlib.Order.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Logic.Relation

namespace Fin

open Nat LT LE Relation

section

theorem fin_to_pred_not_inj {m : ℕ} (f : Fin (m + 1) → Fin m) : ¬ Function.Injective f := by
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

theorem le_of_inj {m n : ℕ} (f : Fin m → Fin n) : Function.Injective f → m ≤ n := by
  intro h
  induction m with
  | zero => exact Nat.zero_le _
  | succ m ih =>
    apply Nat.succ_le_of_lt
    apply le.lt_of_ne <| (ih _  <| h.comp <| Fin.castSucc_injective _)
    intro he
    obtain rfl : m = n := he
    exact fin_to_pred_not_inj f h

theorem ge_of_surj {m n : ℕ} (f : Fin m → Fin n) : Function.Surjective f → n ≤ m := by
  intro h
  match n with
  | 0 => exact Nat.zero_le _
  | n + 1 =>
    apply (Function.surjective_iff_hasRightInverse.mp h).elim
    intro g hid
    exact le_of_inj g (Function.injective_iff_hasLeftInverse.mpr (Exists.intro f hid))

theorem eq_of_bij {m n : ℕ} (f : Fin m → Fin n) : Function.Bijective f → m = n :=
  fun hf ↦ Nat.le_antisymm (le_of_inj _ hf.left) (ge_of_surj _ hf.right)

end

section

variable {n : ℕ} (r : Fin n → Fin n → Prop)

def weaken_rel (i j : Fin (n + 1)) : Fin n → Fin n → Prop :=
  fun i' j' ↦ (i'.val < i.val ∨ i'.val = i.val ∧ j'.val < j.val) ∧ r i' j'

lemma weaken_succ (i : Fin n) (i' j' : Fin n) :
    weaken_rel r i.castSucc (last n) i' j' ↔ weaken_rel r i.succ 0 i' j' := by
  constructor
  · intro ⟨hw, hr⟩
    apply And.intro _ hr
    apply hw.elim
    · intro hl
      exact Or.inl (hl.trans (lt_succ_self _))
    · intro ⟨hl, _⟩
      exact Or.inl ((lt_succ_self _).trans_eq' hl)
  · intro ⟨hw, hr⟩
    apply And.intro _ hr
    apply hw.elim
    · intro hl
      if hi : i'.val = i.val then
        exact Or.inr ⟨hi, j'.isLt⟩
      else
        exact Or.inl ((le_of_lt_succ hl).lt_of_ne hi)
    · intro ⟨_, hn⟩
      exact False.elim (Nat.not_lt_zero _ hn)

lemma weaken_last (j : Fin (n + 1)) (i' j' : Fin n) : weaken_rel r (last n) j i' j' ↔ r i' j' :=
  Iff.intro And.right (⟨Or.inl i'.isLt, ·⟩)

end

structure Partition (n : ℕ) where
  size : Fin (n + 1)
  map : Fin n → Fin size.val
  rep : Fin size.val → Fin n
  rinv : map ∘ rep = id
  min : ∀ (i : Fin n) (j : Fin size.val), map i = j → rep j ≤ i
  mono : ∀ (i j : Fin size.val), i < j → rep i < rep j

namespace Partition

section

variable {n : ℕ} (p : Partition n)

@[ext]
theorem ext (p' : Partition n) (h₁ : p.size.val = p'.size.val)
    (h₂ : ∀ i : Fin n, (p.map i).val = (p'.map i).val) : p = p' := by
  match p, p' with
  | Partition.mk s₁ m₁ r₁ ri₁ min₁ _, Partition.mk s₂ m₂ r₂ ri₂ min₂ _ =>
    obtain rfl : s₁ = s₂ := Fin.eq_of_val_eq h₁
    obtain rfl : m₁ = m₂ := funext (fun i ↦ Fin.eq_of_val_eq (h₂ i))
    obtain rfl : r₁ = r₂ := by
      ext i
      apply Nat.le_antisymm
      · exact min₁ (r₂ i) i (congr_fun ri₂ i)
      · exact min₂ (r₁ i) i (congr_fun ri₁ i)
    rfl

theorem size_ne_zero_of_fin (i : Fin n) : p.size ≠ 0 :=
  Fin.pos_iff_ne_zero.mp ((Nat.zero_le _).trans_lt (p.map i).isLt)

@[simp]
theorem map_rep_id (i : Fin p.size.val) : p.map (p.rep i) = i :=
  congr_fun p.rinv i

theorem map_surj : Function.Surjective p.map :=
  Function.RightInverse.surjective p.map_rep_id

theorem rep_inj : Function.Injective p.rep :=
  Function.LeftInverse.injective p.map_rep_id

variable (i j : Fin n)

@[inline]
abbrev mapEq : Prop :=
  p.map i = p.map j

@[inline]
abbrev mapLT : Prop :=
  p.map i < p.map j

@[inline]
abbrev mapGT : Prop :=
  p.map j < p.map i

protected def splitOn {α : Sort*} : (p.mapEq i j → α) → (p.mapLT i j → α) → (p.mapGT i j → α) → α :=
  fun h₁ h₂ h₃ ↦
  if heq : p.mapEq i j then h₁ heq else
  if hlt : p.mapLT i j then h₂ hlt else
  h₃ (Fin.lt_iff_le_and_ne.mpr ⟨Fin.not_lt.mp hlt, Ne.symm heq⟩)

theorem splitOn_eq {α : Sort*} {h₁ : p.mapEq i j → α} {h₂ : p.mapLT i j → α} {h₃ : p.mapGT i j → α}
    (h : p.mapEq i j) : p.splitOn i j h₁ h₂ h₃ = h₁ h :=
  dite_cond_eq_true (eq_true_intro h)

theorem splitOn_lt {α : Sort*} {h₁ : p.mapEq i j → α} {h₂ : p.mapLT i j → α} {h₃ : p.mapGT i j → α}
    (h : p.mapLT i j) : p.splitOn i j h₁ h₂ h₃ = h₂ h :=
  (dite_cond_eq_false (eq_false_intro (Fin.ne_of_lt h))).trans <|
    dite_cond_eq_true (eq_true_intro h)

theorem splitOn_gt {α : Sort*} {h₁ : p.mapEq i j → α} {h₂ : p.mapLT i j → α} {h₃ : p.mapGT i j → α}
    (h : p.mapGT i j) : p.splitOn i j h₁ h₂ h₃ = h₃ h :=
  (dite_cond_eq_false (eq_false_intro (Fin.ne_of_gt h))).trans <|
    dite_cond_eq_false (eq_false_intro (Fin.not_lt.mpr (Fin.le_of_lt h)))

instance mapEq_decideable : Decidable (p.mapEq i j) :=
  by infer_instance

instance mapEq_equivalence : Equivalence p.mapEq :=
  ⟨fun _ ↦ rfl, Eq.symm, Eq.trans⟩

end

section

theorem rep_eq_of_min {n : ℕ} (p : Partition n) (i : Fin n) (j : Fin p.size.val) :
    p.map i = j → (∀ i' : Fin n, p.map i' = j → i ≤ i') → p.rep j = i :=
  fun h₁ h₂ ↦ Fin.eq_of_val_eq <| Nat.le_antisymm (p.min _ _ h₁) (h₂ (p.rep j) (p.map_rep_id j))

theorem le_rep {n : ℕ} (p : Partition n) (i : Fin p.size.val) :
    i.val ≤ (p.rep i).val := by
  cases i with
  | mk i hi =>
    induction i with
    | zero => exact Nat.zero_le _
    | succ i ih =>
      apply Nat.succ_le_of_lt
      apply Nat.lt_of_le_of_lt (ih ((Nat.lt_succ_self _).trans hi))
      exact p.mono _ _ (Nat.lt_succ_self _)

theorem map_le {n : ℕ} (p : Partition n) (i : Fin n) :
    (p.map i).val ≤ i.val := by
  apply Nat.le_of_not_lt
  intro h₁
  let j : Fin p.size.val := ⟨i.val, h₁.trans (p.map i).isLt⟩
  exact Nat.not_le_of_lt (Nat.lt_of_lt_of_le (p.mono j _ h₁) (p.min _ _ rfl)) (p.le_rep j)

theorem rep_map_id_iff_min {n : ℕ} (p : Partition n) (i : Fin n) :
    p.rep (p.map i) = i ↔ ∀ j : Fin n, p.map j = p.map i → i ≤ j :=
  ⟨fun h j he ↦ h.symm.le.trans (p.min j (p.map i) he), rep_eq_of_min _ _ _ rfl⟩

theorem rep_lt_iff_lt {n : ℕ} (p : Partition n) {i j : Fin p.size.val} :
    i < j ↔ p.rep i < p.rep j := by
  apply Iff.intro (p.mono _ _)
  intro h
  apply Nat.lt_of_not_le
  intro h₁
  apply (Nat.lt_or_eq_of_le h₁).elim
  · intro h₂
    apply Nat.not_lt_of_gt h
    exact p.mono _ _ h₂
  · intro h₂
    apply Nat.not_le_of_lt h
    apply Nat.le_of_eq
    apply Fin.val_eq_of_eq
    exact congr_arg _ (Fin.eq_of_val_eq h₂)

theorem rep_le_iff_le {n : ℕ} (p : Partition n) {i j : Fin p.size.val} :
    i ≤ j ↔ p.rep i ≤ p.rep j := by
  constructor
  · intro h
    apply (Nat.lt_or_eq_of_le h).elim
    · intro h
      exact (p.mono _ _ h).le
    · intro h
      apply Nat.le_of_eq
      apply Fin.val_eq_of_eq
      exact congr_arg _ (Fin.eq_of_val_eq h)
  · intro h
    apply (Nat.lt_or_eq_of_le h).elim
    · intro h
      apply Nat.le_of_lt
      exact p.rep_lt_iff_lt.mpr h
    · intro h
      apply Nat.le_of_eq
      apply Fin.val_eq_of_eq
      apply p.rep_inj
      exact Fin.eq_of_val_eq h

theorem rep_succ_le_iff_rep_lt {n : ℕ} (p : Partition n) (i : ℕ) (hi : i + 1 < p.size.val)
  (j : Fin p.size.val) :
    p.rep ⟨i + 1, hi⟩ ≤ p.rep j ↔ p.rep ⟨i, (Nat.lt_succ_self _).trans hi⟩ < p.rep j :=
  p.rep_le_iff_le.symm.trans <| Nat.succ_le_iff.trans <|
    @p.rep_lt_iff_lt _ ⟨i, (Nat.lt_succ_self _).trans hi⟩ j

theorem rep_lt_of_rep_succ_le {n : ℕ} (p : Partition n) (i : ℕ) (hi : i + 1 < p.size.val)
    (j : Fin n) : p.rep ⟨i + 1, hi⟩ ≤ j → p.rep ⟨i, (Nat.lt_succ_self _).trans hi⟩ < j :=
  (p.mono _ _ (Nat.lt_succ_self i)).trans_le

theorem rep_succ_le_of_rep_lt {n : ℕ} (p : Partition n) (i : ℕ) (hi : i + 1 < p.size.val)
    (j : Fin n) :
    p.rep ⟨i, (Nat.lt_succ_self _).trans hi⟩ < j → p.rep (p.map j) = j → p.rep ⟨i + 1, hi⟩ ≤ j := by
  intro h₁ h₂
  rw [<-h₂]
  apply (p.rep_succ_le_iff_rep_lt i hi (p.map j)).mpr
  exact h₁.trans_eq h₂.symm

theorem map'_rep_inj_of_mapEq {n : ℕ} (p p' : Partition n)
    (h : ∀ i j : Fin n, p.mapEq i j ↔ p'.mapEq i j) :
    Function.Injective (p'.map ∘ p.rep) := by
  intro i j
  simp
  intro he
  replace he := (h (p.rep i) (p.rep j)).mpr he
  unfold mapEq at he
  simp at he
  exact he

theorem map_rep'_inj_of_mapEq {n : ℕ} (p p' : Partition n)
    (h : ∀ i j : Fin n, p.mapEq i j ↔ p'.mapEq i j) :
    Function.Injective (p.map ∘ p'.rep) := by
  intro i j
  simp
  intro he
  replace he := (h (p'.rep i) (p'.rep j)).mp he
  unfold mapEq at he
  simp at he
  exact he

theorem size_eq_of_mapEq {n : ℕ} (p p' : Partition n)
    (h : ∀ i j : Fin n, p.mapEq i j ↔ p'.mapEq i j) : p.size.val = p'.size.val :=
  Nat.le_antisymm (le_of_inj _ (map'_rep_inj_of_mapEq _ _ h)) <|
    le_of_inj _ (map_rep'_inj_of_mapEq _ _ h)

theorem map_zero_eq_zero {n : ℕ} (p : Partition n) {i : Fin n} (h : i.val = 0) :
    p.map i = ⟨0, Nat.zero_lt_of_lt (p.map i).isLt⟩ :=
  Fin.eq_of_val_eq <| Nat.eq_zero_of_le_zero <| (p.map_le _).trans_eq h

theorem rep_zero_eq_zero {n : ℕ} (p : Partition n) {i : Fin p.size.val} (h : i.val = 0) :
    p.rep i = ⟨0, (h.symm.le.trans_lt i.isLt).trans_le (Nat.le_of_lt_succ p.size.isLt)⟩ := by
  apply p.rep_eq_of_min _ _ ((p.map_zero_eq_zero rfl).trans (Fin.eq_of_val_eq h.symm))
  intro _ _
  exact Nat.zero_le _

theorem rep_map_inv_of_mapEq {n : ℕ} (p p' : Partition n)
    (h : ∀ i j : Fin n, p.mapEq i j ↔ p'.mapEq i j) :
    ∀ (i : Fin n), p.rep (p.map i) = p'.rep (p'.map i) := by
  match n with
  | 0 => exact fun i ↦ i.elim0
  | n + 1 =>
    intro i
    induction i with
    | mk i hi =>
      induction i using Nat.strongRec with
      | ind i ih =>
        if h₁ : p.rep (p.map ⟨i, hi⟩) = ⟨i, hi⟩ then
          have h₂ := (p.rep_map_id_iff_min ⟨i, hi⟩).mp h₁
          have h₃ : ∀ j, p'.map j = p'.map ⟨i, hi⟩ → i ≤ j.val :=
          fun j he ↦ h₂ j <| (h _ _).mpr he
          exact h₁.trans ((p'.rep_map_id_iff_min ⟨i, hi⟩).mpr h₃).symm
        else
          have h₂ := (p.rep_map_id_iff_min ⟨i, hi⟩).not.mp h₁
          apply (Decidable.exists_not_of_not_forall h₂).elim
          intro j
          simp
          intro h₃ h₄
          have h₅ : p'.map j = p'.map ⟨i, hi⟩ := (h _ _).mp h₃
          rw [<-h₃, <-h₅]
          exact ih j.val h₄ (Nat.lt_trans h₄ hi)

theorem rep_comm_inj_of_mapEq {n : ℕ} (p p' : Partition n)
    (h : ∀ i j : Fin n, p.mapEq i j ↔ p'.mapEq i j) :
    ∀ (j : Fin p.size.val) (j' : Fin p'.size.val), p.rep j = p'.rep j' → j.val = j'.val := by
  intro j
  induction j with
  | mk j h₁ =>
    induction j with
    | zero =>
      intro j'
      simp [rep_zero_eq_zero]
      intro h₂
      apply @Fin.val_eq_of_eq _ ⟨0, h₁.trans_eq (size_eq_of_mapEq _ _ h)⟩
      apply p'.rep_inj
      simp [rep_zero_eq_zero, h₂]
    | succ j ih =>
      intro j' h₂
      apply @Fin.val_eq_of_eq _ ⟨_, h₁.trans_eq (size_eq_of_mapEq _ _ h)⟩
      have h₃ := p.rep_lt_of_rep_succ_le j h₁ _ h₂.le
      have h₄ : 0 < j'.val := by
        apply Nat.lt_of_not_le
        intro h₄
        replace h₄ : j'.val = 0 := Nat.eq_zero_of_le_zero h₄
        exact Nat.not_lt_zero _ (h₃.trans_eq (p'.rep_zero_eq_zero h₄))
      let k : Fin p'.size.val := ⟨j'.val - 1, (Nat.pred_le _).trans_lt j'.isLt⟩
      have hk : j' = ⟨k.val + 1, (Nat.sub_add_cancel (Nat.one_le_of_lt h₄)).le.trans_lt j'.isLt⟩ :=
        Fin.eq_of_val_eq (Nat.sub_add_cancel (Nat.one_le_of_lt h₄)).symm
      rw [hk]
      apply Fin.eq_of_val_eq
      simp
      rw [hk] at h₂
      have h₅ :=
        p'.rep_lt_of_rep_succ_le k ((Fin.val_eq_of_eq hk.symm).le.trans_lt j'.isLt) _ h₂.symm.le
      rw [hk] at h₃
      apply ih ((Nat.lt_succ_self _).trans h₁) k
      apply Fin.eq_of_val_eq
      apply Nat.le_antisymm
      · apply Nat.le_of_not_lt
        intro h₆
        have h₇ := p'.rep_succ_le_of_rep_lt k.val ((Fin.val_eq_of_eq hk.symm).le.trans_lt j'.isLt)
          (p.rep ⟨j, (Nat.lt_succ_self _).trans h₁⟩) h₆ (by simp [<- rep_map_inv_of_mapEq _ _ h])
        apply Nat.not_le_of_lt (h₃.trans_le h₇)
        exact Nat.le_refl _
      · apply Nat.le_of_not_lt
        intro h₆
        have h₇ := p.rep_succ_le_of_rep_lt j h₁ (p'.rep k) h₆ (by simp [rep_map_inv_of_mapEq _ _ h])
        apply Nat.not_le_of_lt (h₅.trans_le h₇)
        exact Nat.le_refl _

theorem map_eq_of_mapEq {n : ℕ} (p p' : Partition n)
    (h : ∀ i j : Fin n, p.mapEq i j ↔ p'.mapEq i j) :
    ∀ i : Fin n, (p.map i).val = (p'.map i).val :=
  fun _ ↦ rep_comm_inj_of_mapEq _ _ h _ _ <| rep_map_inv_of_mapEq _ _ h _

theorem mapEq_ext {n : ℕ} (p p' : Partition n) (h : ∀ i j : Fin n, p.mapEq i j ↔ p'.mapEq i j) :
    p = p' :=
  Partition.ext _ _ (size_eq_of_mapEq _ _ h) <| map_eq_of_mapEq _ _ h

end

section

variable {n : ℕ} (p : Partition n) (r : Fin n → Fin n → Prop)

def sound : Prop := ∀ i j : Fin n, p.mapEq i j → r i j

def exact : Prop := ∀ i j : Fin n, r i j → p.mapEq i j

theorem lift_sound (r' : Fin n → Fin n → Prop) : (∀ i j, r i j → r' i j) → p.sound r → p.sound r' :=
  fun hmp hr _ _ he ↦ hmp _ _ (hr _ _ he)

theorem lift_exact (r' : Fin n → Fin n → Prop) : (∀ i j, r i j → r' i j) → p.exact r' → p.exact r :=
  fun hmp hr _ _ he ↦ hr _ _ (hmp _ _ he)

theorem eqvGen_exact_of_exact : p.exact r → p.exact (EqvGen r) := by
  intro h i j hr
  induction hr with
  | rel i j hr => exact h _ _ hr
  | refl i => exact Eq.refl _
  | symm i j h₁ ih => exact ih.symm
  | trans i j k h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

end

section

variable (n : ℕ)

@[reducible]
def id (n : ℕ) : Partition n where
  size := last n
  map := (·)
  rep := (·)
  rinv := rfl
  min := fun _ _ h ↦ Fin.le_of_eq h.symm
  mono := fun _ _ ↦ (·)

variable (r : Fin n → Fin n → Prop)

theorem id_eqvGen_sound : (id n).sound (EqvGen r) := by
  intro i j he
  simp [mapEq] at he
  obtain rfl : i = j := he
  exact EqvGen.refl _

theorem id_weaken_trivial_exact : (id n).exact (weaken_rel r 0 0) := by
  intro i j ⟨hw, hr⟩
  apply hw.elim
  · intro h
    exact False.elim (Nat.not_lt_zero _ h)
  · intro ⟨_, h⟩
    exact False.elim (Nat.not_lt_zero _ h)

end

section

variable {n : ℕ} (p : Partition n)

def mergeLT_size : Fin (n + 1) :=
  ⟨p.size.val - 1, (Nat.pred_le _).trans_lt p.size.isLt⟩

def mergeLT_fin_of_lt (i : Fin n) {j : Fin n} (h : p.mapLT i j) : Fin p.mergeLT_size.val :=
  ⟨(p.map i).val, Nat.lt_of_lt_of_le h (Nat.le_pred_of_lt (p.map j).isLt)⟩

def mergeLT_fin_of_gt (i : Fin n) {j : Fin n} (h : p.mapGT i j) : Fin p.mergeLT_size.val :=
  ⟨(p.map i).val - 1, Nat.pred_lt_pred (Nat.ne_zero_of_lt h) (p.map i).isLt⟩

variable {l u : Fin n}

def mergeLT_map (h : p.mapLT l u) (i : Fin n) : Fin p.mergeLT_size.val :=
  p.splitOn i u (fun _ ↦ p.mergeLT_fin_of_lt l h) (p.mergeLT_fin_of_lt i) (p.mergeLT_fin_of_gt i)

@[simp]
lemma mergeLT_fin_of_lt_val (i : Fin n) {j : Fin n} (h : p.mapLT i j) :
    (p.mergeLT_fin_of_lt i h).val = (p.map i).val := rfl

@[simp]
lemma mergeLT_fin_of_gt_val (i : Fin n) {j : Fin n} (h : p.mapGT i j) :
    (p.mergeLT_fin_of_gt i h).val = (p.map i).val - 1 := rfl

@[simp]
lemma mergeLT_map_of_eq (h : p.mapLT l u) (i : Fin n) (h' : p.mapEq i u) :
    (p.mergeLT_map h i).val = (p.map l).val :=
  congr_arg _ (p.splitOn_eq _ _ h')

@[simp]
lemma mergeLT_map_of_lt (h : p.mapLT l u) (i : Fin n) (h' : p.mapLT i u) :
    (p.mergeLT_map h i).val = (p.map i).val :=
  congr_arg _ (p.splitOn_lt _ _ h')

@[simp]
lemma mergeLT_map_of_gt (h : p.mapLT l u) (i : Fin n) (h' : p.mapGT i u) :
    (p.mergeLT_map h i).val = (p.map i).val - 1 :=
  congr_arg _ (p.splitOn_gt _ _ h')

lemma mergeLT_map_lt_map_of_gt (h : p.mapLT l u) (i : Fin n) (h' : p.mapGT i u) :
    (p.mergeLT_map h i).val < (p.map i).val :=
  (p.mergeLT_map_of_gt _ _ h').le.trans_lt (Nat.pred_lt_of_lt h')

lemma mergeLT_map_le_map (h : p.mapLT l u) (i : Fin n) :
    (p.mergeLT_map h i).val ≤ (p.map i).val :=
  p.splitOn i u
    (fun h' ↦ (p.mergeLT_map_of_eq _ _ h').le.trans (h.trans_eq h'.symm).le)
    (fun h' ↦ (p.mergeLT_map_of_lt _ _ h').le)
    (fun h' ↦ (p.mergeLT_map_lt_map_of_gt _ _ h').le)

theorem mergeLT_map_eq_lower_iff_eq_or_eq (h : p.mapLT l u) (i : Fin n) :
    (p.mergeLT_map h i).val = (p.map l).val ↔ p.mapEq i l ∨ p.mapEq i u
  := by
    apply p.splitOn i u
    · intro h'
      exact eq_true_intro (p.mergeLT_map_of_eq _ _ h') ▸ (true_iff _).mpr (Or.inr h')
    · intro h'
      rw [p.mergeLT_map_of_lt _ _ h']
      apply Fin.ext_iff.symm.trans
      apply iff_self_or.mpr fun he ↦ False.elim (Fin.ne_of_lt h' he)
    · intro h'
      simp [Fin.ne_of_gt h', Fin.ne_of_gt (Fin.lt_trans h h'), h']
      exact Nat.ne_of_lt' (Nat.lt_of_lt_of_le h (Nat.le_pred_of_lt h'))

theorem mergeLT_map_lt_upper_iff_eq_or_lt (h : p.mapLT l u) (i : Fin n) :
    (p.mergeLT_map h i).val < (p.map u).val ↔ p.mapEq i u ∨ p.mapLT i u
  := by
    apply p.splitOn i u
    · intro h'
      simp [eq_true_intro h']
      exact h
    · intro h'
      simp [p.mergeLT_map_of_lt _ _ h', Fin.ne_of_lt h']
    · intro h'
      simp [p.mergeLT_map_of_gt _ _ h', Fin.ne_of_gt h']
      simp [Fin.not_lt.mpr (Fin.le_of_lt h')]
      apply Nat.le_pred_of_lt h'

theorem mergeLT_map_eq_of_map_eq (h : p.mapLT l u) (i j : Fin n) :
    p.mapEq i j → p.mergeLT_map h i = p.mergeLT_map h j
  := by
    intro h₁
    apply p.splitOn i u
    · intro h₂
      apply Fin.eq_of_val_eq
      apply (p.mergeLT_map_of_eq _ _ h₂).trans
      apply ((p.mergeLT_map_eq_lower_iff_eq_or_eq h j).mpr _).symm
      exact Or.inr (h₁.symm.trans h₂)
    · intro h₂
      apply Fin.eq_of_val_eq
      apply (p.mergeLT_map_of_lt _ _ h₂).trans
      apply (Fin.val_eq_of_eq h₁).trans
      exact (p.mergeLT_map_of_lt _ _ (h₁.symm.trans_lt h₂)).symm
    · intro h₂
      apply Fin.eq_of_val_eq
      apply (p.mergeLT_map_of_gt _ _ h₂).trans
      rw [h₁]
      exact (p.mergeLT_map_of_gt _ _ (h₂.trans_eq h₁)).symm

theorem mergeLT_map_eq_iff (h : p.mapLT l u) (i j : Fin n) :
    p.mergeLT_map h i = p.mergeLT_map h j ↔
    p.mapEq i j ∨ p.mapEq i l ∧ p.mapEq j u ∨ p.mapEq i u ∧ p.mapEq j l
  := by
    apply p.splitOn i u
    · intro h₁
      simp [eq_true_intro h₁, Fin.ne_of_gt (h.trans_eq h₁.symm)]
      apply Fin.ext_iff.trans
      rw [p.mergeLT_map_of_eq _ _ h₁]
      apply Eq.comm.trans
      apply (p.mergeLT_map_eq_lower_iff_eq_or_eq h j).trans
      apply Or.comm.trans
      apply or_congr_left
      constructor
      · intro h₂
        exact h₁.trans h₂.symm
      · intro h₂
        exact h₂.symm.trans h₁
    · intro h₁
      simp [Fin.ne_of_lt h₁]
      apply Fin.ext_iff.trans
      rw [p.mergeLT_map_of_lt _ _ h₁]
      if h₂ : p.mapEq i l then
        rw [Fin.val_eq_of_eq h₂, eq_true_intro h₂]
        apply Eq.comm.trans
        apply (p.mergeLT_map_eq_lower_iff_eq_or_eq h j).trans
        simp
        apply or_congr_left
        constructor
        · intro h₃
          exact h₂.trans h₃.symm
        · intro h₃
          exact h₃.symm.trans h₂
      else
        rw [eq_false_intro h₂]
        simp
        constructor
        · intro h₃
          apply ((p.mergeLT_map_lt_upper_iff_eq_or_lt h j).mp (h₃.symm.trans_lt h₁)).elim
          · intro h₄
            rw [p.mergeLT_map_of_eq _ _ h₄] at h₃
            exact False.elim (h₂ (Fin.eq_of_val_eq h₃))
          · intro h₄
            rw [p.mergeLT_map_of_lt _ _ h₄] at h₃
            exact Fin.eq_of_val_eq h₃
        · intro h₃
          simp [h₃.symm.trans_lt h₁]
          exact Fin.val_eq_of_eq h₃
    · intro h₁
      simp [Fin.ne_of_gt h₁, Fin.ne_of_gt (Fin.lt_trans h h₁)]
      apply Iff.intro _ (p.mergeLT_map_eq_of_map_eq h _ _)
      intro h₂
      replace h₂ := ((p.mergeLT_map_of_gt _ _ h₁)).symm.trans (Fin.val_eq_of_eq h₂)
      have h₃ := Nat.not_lt_of_le ((Nat.le_pred_of_lt h₁).trans_eq h₂)
      have ⟨h₄, h₅⟩ := not_or.mp ((p.mergeLT_map_lt_upper_iff_eq_or_lt h j).not.mp h₃)
      have h₆ := Nat.lt_of_le_of_ne (Nat.le_of_not_lt h₅) (Fin.val_ne_of_ne h₄).symm
      rw [p.mergeLT_map_of_gt _ _ h₆] at h₂
      exact Fin.eq_of_val_eq (Nat.pred_inj (Nat.zero_lt_of_lt h₁) (Nat.zero_lt_of_lt h₆) h₂)

def mergeLT_rep (_ : p.mapLT l u) (i : Fin p.mergeLT_size.val) : Fin n :=
  if i.val < (p.map u).val
  then p.rep (Fin.castLE (Nat.pred_le _) i)
  else p.rep ⟨i.val + 1, Nat.succ_lt_of_lt_pred i.isLt⟩

theorem mergeLT_rinv (h : p.mapLT l u) :
    p.mergeLT_map h ∘ p.mergeLT_rep h = (·) := by
  funext i
  apply Fin.eq_of_val_eq
  if h₁ : i.val < (p.map u).val then
    simp [mergeLT_rep, h₁]
    have h₂ : p.mapLT (p.rep (Fin.castLE (Nat.pred_le _) i)) u := by simp ; exact h₁
    simp [p.mergeLT_map_of_lt _ _ h₂]
  else
    simp [mergeLT_rep, h₁]
    have h₂ : p.mapGT (p.rep ⟨i.val + 1, Nat.succ_lt_of_lt_pred i.isLt⟩) u :=
      by simp ; exact Nat.lt_succ_of_le (Nat.le_of_not_lt h₁)
    simp [p.mergeLT_map_of_gt _ _ h₂]

theorem mergeLT_min (h : p.mapLT l u) (i : Fin n) (j : Fin p.mergeLT_size.val) :
    p.mergeLT_map h i = j → p.mergeLT_rep h j ≤ i
  := by
    intro h₁
    replace h₁ := Fin.val_eq_of_eq h₁
    if h₂ : j.val < (p.map u).val then
      simp [mergeLT_rep, h₂]
      apply p.splitOn i u
      · intro h₃
        exact Nat.le_trans (p.mono _ _ h₂).le (p.min i (p.map u) h₃)
      · intro h₃
        apply p.min
        apply Fin.eq_of_val_eq
        simp [p.mergeLT_map_of_lt _ _ h₃] at h₁
        exact h₁
      · intro h₃
        simp [p.mergeLT_map_of_gt _ _ h₃] at h₁
        apply Fin.le_trans
          (Fin.le_of_lt (p.mono (Fin.castLE (Nat.pred_le _) j) (p.map i) (h₂.trans h₃)))
        exact p.min _ _ rfl
    else
      simp [mergeLT_rep, h₂]
      apply p.splitOn i u
      · intro h₃
        simp [mergeLT_map, p.splitOn_eq _ _ h₃] at h₁
        exact False.elim (h₂ (h₁.symm.le.trans_lt h))
      · intro h₃
        simp [mergeLT_map, p.splitOn_lt _ _ h₃] at h₁
        exact False.elim (h₂ (h₁.symm.le.trans_lt h₃))
      · intro h₃
        simp [p.mergeLT_map_of_gt _ _ h₃] at h₁
        apply p.min
        apply Fin.eq_of_val_eq
        simp [<-h₁]
        exact (Nat.succ_pred (Nat.ne_zero_of_lt h₃)).symm

theorem mergeLT_mono (h : p.mapLT l u) (i j : Fin p.mergeLT_size.val) :
    i < j → p.mergeLT_rep h i < p.mergeLT_rep h j
  := by
    intro h₁
    if h₂ : j.val < (p.map u).val then
      simp [mergeLT_rep, Nat.lt_trans h₁ h₂, h₂]
      exact p.mono _ _ h₁
    else
      if h₃ : i.val < (p.map u).val then
        simp [mergeLT_rep, h₂, h₃]
        apply p.mono
        exact Nat.lt_trans h₁ (Nat.lt_succ_self _)
      else
        simp [mergeLT_rep, h₂, h₃]
        exact p.mono _ _ (Nat.add_lt_add_right h₁ _)

def mergeLT (h : p.mapLT l u) : Partition n where
  size := p.mergeLT_size
  map := p.mergeLT_map h
  rep := p.mergeLT_rep h
  rinv := p.mergeLT_rinv h
  min := p.mergeLT_min h
  mono := p.mergeLT_mono h

theorem mergeLT_mapEq_iff (h : p.mapLT l u) (i j : Fin n) :
    (p.mergeLT h).mapEq i j ↔ p.mapEq i j ∨ p.mapEq i l ∧ p.mapEq j u ∨ p.mapEq i u ∧ p.mapEq j l :=
  p.mergeLT_map_eq_iff h i j

end

section

variable {n : ℕ} (p : Partition n) (l u : Fin n)

def merge : Partition n :=
  p.splitOn l u (fun _ ↦ p) (fun h ↦ p.mergeLT h) (fun h ↦ p.mergeLT h)

theorem merge_mapEq_iff (i j : Fin n) :
    (p.merge l u).mapEq i j ↔
    p.mapEq i j ∨ p.mapEq i l ∧ p.mapEq j u ∨ p.mapEq i u ∧ p.mapEq j l := by
  apply p.splitOn l u
  · intro h₁
    rw [merge, p.splitOn_eq _ _ h₁]
    simp
    intro h
    apply h.elim
    · intro h₂
      exact h₂.left.trans (h₁.trans h₂.right.symm)
    · intro h₂
      exact h₂.left.trans (h₁.symm.trans h₂.right.symm)
  · intro h₁
    rw [merge, p.splitOn_lt _ _ h₁]
    exact p.mergeLT_mapEq_iff h₁ i j
  · intro h₁
    rw [merge, p.splitOn_gt _ _ h₁]
    conv_rhs => arg 2 ; rw [Or.comm]
    exact p.mergeLT_mapEq_iff h₁ i j

end

section

variable {n : ℕ} (p : Partition n) (r : Fin n → Fin n → Prop)

lemma merge_preserves_eqvGen_sound_of_rel (i j : Fin n) :
    p.sound (EqvGen r) → r i j → (p.merge i j).sound (EqvGen r)
  := by
    intro hs hr i' j' hp
    apply ((p.merge_mapEq_iff i j i' j').mp hp).elim (hs i' j' ·)
    intro h
    apply h.elim
    · intro ⟨h₁, h₂⟩
      apply EqvGen.trans _ _ _ (hs _ _ h₁)
      apply EqvGen.trans _ _ _ (EqvGen.rel _ _ hr)
      exact hs _ _ h₂.symm
    · intro ⟨h₁, h₂⟩
      apply EqvGen.trans _ _ _ (hs _ _ h₁)
      apply EqvGen.trans _ _ _ (EqvGen.symm _ _ (EqvGen.rel _ _ hr))
      exact hs _ _ h₂.symm

lemma merge_relaxes_weakend_exact_of_rel (i j : Fin n) :
    p.exact (weaken_rel r i.castSucc j.castSucc) → r i j →
    (p.merge i j).exact (weaken_rel r i.castSucc j.succ)
  := by
    intro he hr i' j' ⟨hw, hr'⟩
    apply (p.merge_mapEq_iff i j i' j').mpr
    apply hw.elim
    · intro hi
      exact Or.inl (he i' j' ⟨Or.inl hi, hr'⟩)
    · intro ⟨hi, hj⟩
      obtain rfl : i = i' := eq_of_val_eq hi.symm
      clear hi hw
      if hj' : j'.val = j.val then
        obtain rfl : j = j' := eq_of_val_eq hj'.symm
        exact Or.inr (Or.inl ⟨rfl, rfl⟩)
      else
        replace hj := (le_of_lt_succ hj).lt_of_ne hj'
        exact Or.inl (he i j' ⟨Or.inr ⟨rfl, hj⟩, hr'⟩)

lemma relaxes_weakend_exact_of_not_rel (i j : Fin n) :
    p.exact (weaken_rel r i.castSucc j.castSucc) → ¬ r i j →
    p.exact (weaken_rel r i.castSucc j.succ)
  := by
    intro he hr i' j' ⟨hw, hr'⟩
    apply hw.elim
    · intro hi
      exact he i' j' ⟨Or.inl hi, hr'⟩
    · intro ⟨hi, hj⟩
      obtain rfl : i = i' := eq_of_val_eq hi.symm
      clear hi hw
      if hj' : j'.val = j.val then
        obtain rfl : j = j' := eq_of_val_eq hj'.symm
        exact False.elim (hr hr')
      else
        exact he i j' ⟨Or.inr ⟨rfl, (le_of_lt_succ hj).lt_of_ne hj'⟩, hr'⟩

variable [∀ i j : Fin n, Decidable (r i j)] (i j : Fin n)

def conditional_merge : Partition n := if r i j then p.merge i j else p

lemma conditional_merge_preserves_eqvGen_sound :
    p.sound (EqvGen r) → (p.conditional_merge r i j).sound (EqvGen r)
  := by
    intro hs
    if hr : r i j then
      rw [conditional_merge, ite_cond_eq_true _ _ (eq_true_intro hr)]
      exact p.merge_preserves_eqvGen_sound_of_rel r i j hs hr
    else
      rw [conditional_merge, ite_cond_eq_false _ _ (eq_false_intro hr)]
      exact hs

lemma condition_merge_relaxes_weakened_exact :
    p.exact (weaken_rel r i.castSucc j.castSucc) →
    (p.conditional_merge r i j).exact (weaken_rel r i.castSucc j.succ)
  := by
    intro he
    if hr : r i j then
      rw [conditional_merge, ite_cond_eq_true _ _ (eq_true_intro hr)]
      exact p.merge_relaxes_weakend_exact_of_rel r i j he hr
    else
      rw [conditional_merge, ite_cond_eq_false _ _ (eq_false_intro hr)]
      exact p.relaxes_weakend_exact_of_not_rel r i j he hr

end

section

variable {n : ℕ} (p : Partition n)
variable (r : Fin n → Fin n → Prop) [∀ i j : Fin n, Decidable (r i j)]

def conditional_merge_rec₂ (i : Fin n) (j : ℕ) (h : j < n + 1) : Partition n :=
  match j with
  | 0 => p
  | j + 1 => (conditional_merge_rec₂ i j ((lt_succ_self _).trans h)).conditional_merge
    r i ⟨j, Nat.add_lt_add_iff_right.mp h⟩

def conditional_merge_rec₁ (i : ℕ) (h : i < n + 1) : Partition n :=
  match i with
  | 0 => p
  | i + 1 => (conditional_merge_rec₁ i ((lt_succ_self _).trans h)).conditional_merge_rec₂
    r ⟨i, Nat.add_lt_add_iff_right.mp h⟩ n (lt_succ_self n)

lemma conditional_merge_rec₂_preserves_eqvGen_sound (i : Fin n) (j : ℕ) (h : j < n + 1) :
    p.sound (EqvGen r) → (p.conditional_merge_rec₂ r i j h).sound (EqvGen r)
  := by
    intro hs
    induction j with
    | zero => exact hs
    | succ j ih => apply conditional_merge_preserves_eqvGen_sound ; apply ih

lemma conditional_merge_rec₁_preserves_eqvGen_sound (i : ℕ) (h : i < n + 1) :
    p.sound (EqvGen r) → (p.conditional_merge_rec₁ r i h).sound (EqvGen r)
  := by
    intro hs
    induction i with
    | zero => exact hs
    | succ i ih => apply conditional_merge_rec₂_preserves_eqvGen_sound ; apply ih

lemma conditional_merge_rec₂_relaxes_weakened_exact (i : Fin n) (j : ℕ) (h : j < n + 1) :
    p.exact (weaken_rel r i.castSucc 0) →
    (p.conditional_merge_rec₂ r i j h).exact (weaken_rel r i.castSucc ⟨j, h⟩)
  := by
    intro he
    induction j with
    | zero => exact he
    | succ j ih => apply condition_merge_relaxes_weakened_exact ; apply ih

lemma conditional_merge_rec₁_relaxes_weakened_exact (i : ℕ) (h : i < n + 1) :
    p.exact (weaken_rel r 0 0) → (p.conditional_merge_rec₁ r i h).exact (weaken_rel r ⟨i, h⟩ 0)
  := by
    intro he
    induction i with
    | zero => exact he
    | succ i ih =>
      apply lift_exact _ _ _ (fun _ _ ↦ (weaken_succ r ⟨i, Nat.add_lt_add_iff_right.mp h⟩ _ _).mpr)
      apply conditional_merge_rec₂_relaxes_weakened_exact ; apply ih

end

section

variable {n : ℕ} (r : Fin n → Fin n → Prop) [∀ i j : Fin n, Decidable (r i j)]

def of_relation : Partition n := (id n).conditional_merge_rec₁ r n (lt_succ_self n)

theorem of_relation_eqvGen_sound : (of_relation r).sound (EqvGen r) :=
  conditional_merge_rec₁_preserves_eqvGen_sound _ _ _ _ (id_eqvGen_sound _ _)

theorem of_relation_exact : (of_relation r).exact r :=
  lift_exact _ _ _ (fun _ _ ↦ (weaken_last _ _ _ _).mpr)
  (conditional_merge_rec₁_relaxes_weakened_exact _ _ _ _ (id_weaken_trivial_exact _ _))

theorem of_relation_eqvGen_exact : (of_relation r).exact (EqvGen r) :=
  eqvGen_exact_of_exact _ _ (of_relation_exact _)

theorem of_relation_iff_eqvGen : ∀ i j : Fin n, (of_relation r).mapEq i j ↔ EqvGen r i j :=
  fun i j ↦ ⟨of_relation_eqvGen_sound r i j, of_relation_eqvGen_exact r i j⟩

theorem of_relation_unique (p : Partition n) (h : ∀ i j : Fin n, p.mapEq i j ↔ EqvGen r i j) :
    p = of_relation r :=
  mapEq_ext _ _ <| fun i j ↦ (h i j).trans (of_relation_iff_eqvGen r i j).symm

end

section

variable {n : ℕ} (p : Partition n)

variable (r : Fin n → Fin n → Prop) (h : ∀ i j : Fin n, p.mapEq i j ↔ r i j)

instance rel_decideable_of_partition (i j : Fin n) : Decidable (r i j) :=
  decidable_of_decidable_of_iff (h i j)

/-
Todo: construct an object of `Partition n` given only:
- size : `Fin (n + 1)`
- map : `Fin n → Fin size.val`
- rep : `Fin size.val → Fin n`
- rinv : `map ∘ rep = id`
By first updating the choice of representative to be the minimum over all values related
to the existing choice, then swapping the images of classes as necessary to ensure the
monotonicity requirement is satisfied.

Todo: construct an object of `Partition n` given only:
- map : `Fin n → Fin m`
- surj : `Function.Surjective map`
For an arbitrary `m` which is guarnateed to be less than `n + 1` by surjectivity.

Todo: establish that a relation on `Fin n` is decideable if it is identified by a
surjective map of `Fin`'s. (The converse implication has already been established.)
-/

end

section

/-- The isomorphism between partitions and decideable equivalence relations. -/

theorem of_relation_mapEq_eq_eqvGen {n : ℕ} (r : Fin n → Fin n → Prop)
    [∀ i j : Fin n, Decidable (r i j)] : (of_relation r).mapEq = EqvGen r :=
  funext₂ <| fun _ _ ↦ propext <| of_relation_iff_eqvGen _ _ _

theorem of_eqv_relation_mapEq_id {n : ℕ} {r : Fin n → Fin n → Prop}
    (h : Equivalence r) [∀ i j : Fin n, Decidable (r i j)] : (of_relation r).mapEq = r :=
  (of_relation_mapEq_eq_eqvGen r).trans <| Equivalence.eqvGen_eq h

theorem mapEq_to_relation_id {n : ℕ} (p : Partition n) : of_relation p.mapEq = p := by
  apply mapEq_ext
  intro i j
  apply Iff.intro _ (of_relation_exact p.mapEq i j)
  intro h
  exact Equivalence.eqvGen_eq p.mapEq_equivalence ▸ (of_relation_iff_eqvGen p.mapEq i j).mp h

end

end Partition

end Fin

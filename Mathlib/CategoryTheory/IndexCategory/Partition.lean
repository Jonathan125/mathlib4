import Mathlib.Data.Nat.Basic
import Mathlib.Order.Basic
import Mathlib.Logic.Relation


namespace Fin

open Nat LT LE Relation

def decr {n : ℕ} (i : Fin n) : Fin n :=
  ⟨i.val - 1, (pred_le _).trans_lt (isLt _)⟩

section

variable {n : ℕ} (r : Fin n → Fin n → Prop)

def weakened (i j : Fin (n + 1)) : Fin n → Fin n → Prop :=
  fun i' j' ↦ (i'.val < i.val ∨ i'.val = i.val ∧ j'.val < j.val) ∧ r i' j'

lemma weakened_step (i : Fin n) (i' j' : Fin n) :
    weakened r i.castSucc (last n) i' j' ↔ weakened r i.succ 0 i' j'
  := by
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

lemma weakened_id (j : Fin (n + 1)) (i' j' : Fin n) :
  weakened r (last n) j i' j' ↔ r i' j' := Iff.intro And.right (⟨Or.inl i'.isLt, ·⟩)

end

structure Partition (n : ℕ) where
  map : Fin n → Fin n
  size : Fin (n + 1)
  inv : ∀ (i : Fin n), (map i).val < size.val
  surj : ∀ (i : Fin n), i.val < size.val → ∃ j : Fin n, i.val = (map j).val

namespace Partition

@[reducible]
def id (n : ℕ) : Partition n where
  map := (·)
  size := last n
  inv := isLt
  surj := fun i _ ↦ Exists.intro i rfl

variable {n : ℕ}

section

variable (p : Partition n)

@[inline]
abbrev val (i : Fin n) : ℕ := (p.map i).val

@[inline]
abbrev pred (i : Fin n) : Fin n := (p.map i).decr

@[inline]
abbrev rel (i j : Fin n) : Prop := p.val i = p.val j

@[inline]
abbrev lt (i j : Fin n) : Prop := p.val i < p.val j

section

variable (r : Fin n → Fin n → Prop)

def sound : Prop := ∀ i j : Fin n, p.rel i j → r i j

def exact : Prop := ∀ i j : Fin n, r i j → p.rel i j

lemma identity_eqv_sound : (id n).sound (EqvGen r) := by
  intro i j hp
  simp [rel, val] at hp
  obtain rfl : i = j := eq_of_val_eq hp
  exact EqvGen.refl _

lemma identity_weakened_trivial_exact : (id n).exact (weakened r 0 0) := by
  intro i j ⟨hw, hr⟩
  apply hw.elim
  · intro h
    exact False.elim (Nat.not_lt_zero _ h)
  · intro ⟨_, h⟩
    exact False.elim (Nat.not_lt_zero _ h)

lemma exact_ext (r' : Fin n → Fin n → Prop) :
    (∀ i j : Fin n, r i j ↔ r' i j) → (p.exact r ↔ p.exact r')
  := by
    intro h
    obtain rfl : r = r' := funext₂ (fun i j ↦ Iff.eq (h i j))
    exact ⟨(·), (·)⟩

lemma eqv_exact_of_rel_exact : p.exact r → p.exact (EqvGen r) := by
  intro h i j hr
  induction hr with
  | rel i j hr => exact h _ _ hr
  | refl i => exact Eq.refl _
  | symm i j h₁ ih => exact ih.symm
  | trans i j k h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

end

section

variable {i j : Fin n}

@[reducible]
def merge_map (_ : p.lt i j) (i' : Fin n) : Fin n :=
  if p.lt i' j then p.map i' else if p.rel i' j then p.map i else p.pred i'

variable (h : p.lt i j) (i' : Fin n)

lemma merge_map_val_of_lt : p.lt i' j → (p.merge_map h i').val = p.val i' := by
  intro hlt
  simp [val, merge_map, hlt]

lemma merge_map_val_of_eq : p.rel i' j → (p.merge_map h i').val = p.val i := by
  intro heq
  simp [val, merge_map, heq, eq_true_intro heq]

lemma merge_map_val_of_gt : ¬ p.lt i' j → ¬ p.rel i' j → (p.merge_map h i').val = p.pred i' := by
  intro hle hne
  simp [val, merge_map, hle, eq_false_intro hne]

lemma merge_map_val_lt_val_of_not_lt : ¬ p.lt i' j → (p.merge_map h i').val < p.val i' := by
  intro h₁
  if h₂ : p.rel i' j then
    apply (p.merge_map_val_of_eq _ _ h₂).le.trans_lt
    exact h.trans_le h₂.symm.le
  else
    apply (p.merge_map_val_of_gt _ _ h₁ h₂).le.trans_lt
    exact pred_lt (Nat.ne_zero_of_lt ((le_of_not_gt h₁).lt_of_ne (Ne.symm h₂)))

lemma merge_map_val_le_val : (p.merge_map h i').val ≤ p.val i' :=
  if h₁ : p.lt i' j then (p.merge_map_val_of_lt _ _ h₁).le
  else (p.merge_map_val_lt_val_of_not_lt _ _ h₁).le

lemma merge_map_inv : (p.merge_map h i').val < p.size.val - 1 :=
  if h₁ : p.lt i' j then
    (p.merge_map_val_le_val h i').trans_lt (h₁.trans_le (le_pred_of_lt (p.inv j)))
  else
    (p.merge_map_val_lt_val_of_not_lt h i' h₁).trans_le (le_pred_of_lt (p.inv _))

lemma merge_map_surj : i'.val < p.size.val - 1 → ∃ j' : Fin n, i'.val = (p.merge_map h j').val := by
  intro h₁
  if h₂ : i'.val < p.val j then
    apply Exists.elim (p.surj i' (h₂.trans (p.inv j)))
    intro j' h₃
    apply Exists.intro j'
    exact h₃.trans (p.merge_map_val_of_lt h j' (h₃.symm.le.trans_lt h₂)).symm
  else
    have h₃ : i'.val + 1 < p.size.val := succ_lt_of_lt_pred h₁
    apply Exists.elim (p.surj ⟨i'.val + 1, h₃.trans_le (le_of_lt_succ p.size.isLt)⟩ h₃)
    intro j' (h₄ : i'.val + 1 = p.val j')
    apply Exists.intro j'
    apply (Nat.eq_sub_of_add_eq h₄).trans
    have h₅ := (le_of_not_gt h₂).trans_lt (lt_of_succ_le h₄.le)
    exact (p.merge_map_val_of_gt h j' (not_lt_of_gt h₅) h₅.ne').symm

def merge' : Partition n where
  map := p.merge_map h
  size := p.size.decr
  inv := p.merge_map_inv h
  surj := p.merge_map_surj h

lemma merge'_val_of_lt : p.lt i' j → (p.merge' h).val i' = p.val i' :=
  p.merge_map_val_of_lt h i'

lemma merge'_val_of_eq : p.rel i' j → (p.merge' h).val i' = p.val i :=
  p.merge_map_val_of_eq h i'

lemma merge'_val_of_gt : ¬ p.lt i' j → ¬ p.rel i' j → (p.merge' h).val i' = p.pred i' :=
  p.merge_map_val_of_gt h i'

lemma merge'_val_eq_iff_rel_or_rel : (p.merge' h).val i' = p.val i ↔ p.rel i' i ∨ p.rel i' j := by
  if h₁ : p.lt i' j then
    rw [p.merge'_val_of_lt _ _ h₁]
    apply iff_self_or.mpr
    intro h₂
    exact False.elim (h₁.ne h₂)
  else
    have h₁' : p.val j ≤ p.val i' := le_of_not_gt h₁
    simp [(h.trans_le h₁').ne']
    if h₂ : p.rel i' j then
      rw [eq_true_intro (p.merge'_val_of_eq _ _ h₂)]
      exact (true_iff _).to_iff.mpr h₂
    else
      rw [p.merge'_val_of_gt _ _ h₁ h₂, eq_false_intro h₂]
      apply (iff_false _).to_iff.mpr
      exact lt.ne' (h.trans_le (le_pred_of_lt (h₁'.lt_of_ne (Ne.symm h₂))))

lemma merge'_val_lt_iff_val_le : (p.merge' h).val i' < p.val j ↔ p.val i' ≤ p.val j := by
  if h₁ : p.lt i' j then
    rw [p.merge'_val_of_lt _ _ h₁]
    exact ⟨(lt.le ·), (le.lt_of_ne · h₁.ne)⟩
  else
    if h₂ : p.rel i' j then
      rw [p.merge'_val_of_eq _ _ h₂, eq_true_intro h₂.le]
      exact (iff_true _).to_iff.mpr h
    else
      have h₃ := (le_of_not_gt h₁).lt_of_ne (Ne.symm h₂)
      rw [p.merge'_val_of_gt _ _ h₁ h₂,eq_false_intro (not_le_of_gt h₃)]
      exact (iff_false _).to_iff.mpr (not_lt_of_ge (le_pred_of_lt h₃))

variable (j' : Fin n)

lemma merge'_rel_of_rel : p.rel i' j' → (p.merge' h).rel i' j' := by
  intro hr
  unfold rel
  if h₁ : p.lt i' j then
    apply (p.merge'_val_of_lt _ _ h₁).trans
    exact hr.trans (p.merge'_val_of_lt _ _ (hr.symm.le.trans_lt h₁)).symm
  else if h₂ : p.rel i' j then
    apply (p.merge'_val_of_eq _ _ h₂).trans
    exact (p.merge'_val_of_eq _ _ (hr.symm.trans h₂)).symm
  else
    apply (p.merge'_val_of_gt _ _ h₁ h₂).trans
    simp [pred, decr, hr]
    apply (p.merge'_val_of_gt _ _ _ (Eq.trans_ne hr.symm h₂)).symm
    exact not_lt_of_ge ((le_of_not_gt h₁).trans hr.le)

lemma merge'_rel_iff : (p.merge' h).rel i' j' ↔
    p.rel i' j' ∨ p.rel i' i ∧ p.rel j' j ∨ p.rel i' j ∧ p.rel j' i
  := by
    constructor
    · intro hr
      unfold rel at hr
      if h₁ : p.lt i' j then
        rw [p.merge'_val_of_lt _ _ h₁] at hr
        if h₂ : p.rel i' i then
          apply ((p.merge'_val_eq_iff_rel_or_rel h j').mp (hr.symm.trans h₂)).elim
          · intro h₃
            exact Or.inl (h₂.trans h₃.symm)
          · intro h₃
            exact Or.inr (Or.inl ⟨h₂, h₃⟩)
        else
          have h₃ := (not_or.mp ((p.merge'_val_eq_iff_rel_or_rel h j').not.mp
            (hr.symm.trans_ne h₂))).right
          have h₄ : p.lt j' j := by
            apply le.lt_of_ne _ h₃
            exact (p.merge'_val_lt_iff_val_le h _).mp (hr.symm.le.trans_lt h₁)
          rw [p.merge'_val_of_lt _ _ h₄] at hr
          exact Or.inl hr
      else
        if h₂ : p.rel i' j then
          rw [p.merge'_val_of_eq _ _ h₂] at hr
          apply ((p.merge'_val_eq_iff_rel_or_rel h j').mp hr.symm).elim
          · intro h₃
            exact Or.inr (Or.inr ⟨h₂, h₃⟩)
          · intro h₃
            exact Or.inl (h₂.trans h₃.symm)
        else
          rw [p.merge'_val_of_gt _ _ h₁ h₂] at hr
          have h₃ := (le_of_not_gt h₁).lt_of_ne (Ne.symm h₂)
          have h₄ := le_of_lt_succ (h₃.trans_eq (Nat.eq_add_of_sub_eq (one_le_of_lt h₃) hr))
          replace h₄ := lt_of_not_ge ((p.merge'_val_lt_iff_val_le h j').not.mp (not_lt_of_ge h₄))
          rw [p.merge'_val_of_gt h j' (not_lt_of_gt h₄) h₄.ne'] at hr
          apply Or.inl
          apply (Nat.eq_add_of_sub_eq (one_le_of_lt h₃) hr).trans
          exact Nat.sub_add_cancel (one_le_of_lt h₄)
    · intro h₁
      apply h₁.elim (p.merge'_rel_of_rel _ _ _)
      clear h₁
      intro h₁
      unfold rel
      apply h₁.elim
      · intro ⟨h₂, h₃⟩
        apply ((p.merge'_val_eq_iff_rel_or_rel h i').mpr (Or.inl h₂)).trans
        exact ((p.merge'_val_eq_iff_rel_or_rel h j').mpr (Or.inr h₃)).symm
      · intro ⟨h₂, h₃⟩
        apply ((p.merge'_val_eq_iff_rel_or_rel h i').mpr (Or.inr h₂)).trans
        exact ((p.merge'_val_eq_iff_rel_or_rel h j').mpr (Or.inl h₃)).symm

end

section

variable (i j : Fin n)

def merge : Partition n :=
  if h₁ : p.rel i j then p else if h₂ : p.lt i j then p.merge' h₂
  else p.merge' ((le_of_not_gt h₂).lt_of_ne (Ne.symm h₁))

variable (i' j' : Fin n)

lemma merge_rel_iff : (p.merge i j).rel i' j' ↔
    p.rel i' j' ∨ p.rel i' i ∧ p.rel j' j ∨ p.rel i' j ∧ p.rel j' i
  := by
    if h₁ : p.rel i j then
      unfold merge
      simp [eq_true_intro h₁]
      intro h
      apply h.elim
      · intro h₂
        exact h₂.left.trans (h₁.trans h₂.right.symm)
      · intro h₂
        exact h₂.left.trans (h₁.symm.trans h₂.right.symm)
    else
      if h₂ : p.lt i j then
        unfold merge
        simp [h₁, h₂]
        exact p.merge'_rel_iff h₂ i' j'
      else
        unfold merge
        simp [h₁, h₂]
        conv_rhs => arg 2 ; rw [Or.comm]
        exact p.merge'_rel_iff ((le_of_not_gt h₂).lt_of_ne (Ne.symm h₁)) i' j'

end

section

variable (r : Fin n → Fin n → Prop)

lemma merge_preserves_eqv_sound_of_rel (i j : Fin n) :
    p.sound (EqvGen r) → r i j → (p.merge i j).sound (EqvGen r)
  := by
    intro hs hr i' j' hp
    apply ((p.merge_rel_iff i j i' j').mp hp).elim (hs i' j' ·)
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
    p.exact (weakened r i.castSucc j.castSucc) → r i j →
    (p.merge i j).exact (weakened r i.castSucc j.succ)
  := by
    intro he hr i' j' ⟨hw, hr'⟩
    apply (p.merge_rel_iff i j i' j').mpr
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
    p.exact (weakened r i.castSucc j.castSucc) → ¬ r i j →
    p.exact (weakened r i.castSucc j.succ)
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

lemma conditional_merge_preserves_eqv_sound :
    p.sound (EqvGen r) → (p.conditional_merge r i j).sound (EqvGen r)
  := by
    intro hs
    if hr : r i j then
      rw [conditional_merge, ite_cond_eq_true _ _ (eq_true_intro hr)]
      exact p.merge_preserves_eqv_sound_of_rel r i j hs hr
    else
      rw [conditional_merge, ite_cond_eq_false _ _ (eq_false_intro hr)]
      exact hs

lemma condition_merge_relaxes_weakened_exact :
    p.exact (weakened r i.castSucc j.castSucc) →
    (p.conditional_merge r i j).exact (weakened r i.castSucc j.succ)
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

lemma conditional_merge_rec₂_preserves_eqv_sound (i : Fin n) (j : ℕ) (h : j < n + 1) :
    p.sound (EqvGen r) → (p.conditional_merge_rec₂ r i j h).sound (EqvGen r)
  := by
    intro hs
    induction j with
    | zero => exact hs
    | succ j ih => apply conditional_merge_preserves_eqv_sound ; apply ih

lemma conditional_merge_rec₁_preserves_eqv_sound (i : ℕ) (h : i < n + 1) :
    p.sound (EqvGen r) → (p.conditional_merge_rec₁ r i h).sound (EqvGen r)
  := by
    intro hs
    induction i with
    | zero => exact hs
    | succ i ih => apply conditional_merge_rec₂_preserves_eqv_sound ; apply ih

lemma conditional_merge_rec₂_relaxes_weakened_exact (i : Fin n) (j : ℕ) (h : j < n + 1) :
    p.exact (weakened r i.castSucc 0) →
    (p.conditional_merge_rec₂ r i j h).exact (weakened r i.castSucc ⟨j, h⟩)
  := by
    intro he
    induction j with
    | zero => exact he
    | succ j ih => apply condition_merge_relaxes_weakened_exact ; apply ih

lemma conditional_merge_rec₁_relaxes_weakened_exact (i : ℕ) (h : i < n + 1) :
    p.exact (weakened r 0 0) → (p.conditional_merge_rec₁ r i h).exact (weakened r ⟨i, h⟩ 0)
  := by
    intro he
    induction i with
    | zero => exact he
    | succ i ih =>
      apply (exact_ext _ _ _ (weakened_step r ⟨i, Nat.add_lt_add_iff_right.mp h⟩)).mp
      apply conditional_merge_rec₂_relaxes_weakened_exact ; apply ih

end

end

variable (r : Fin n → Fin n → Prop) [∀ i j : Fin n, Decidable (r i j)]

def of_relation : Partition n := (id n).conditional_merge_rec₁ r n (lt_succ_self n)

theorem of_relation_eqv_sound : (of_relation r).sound (EqvGen r) :=
  conditional_merge_rec₁_preserves_eqv_sound _ _ _ _ (identity_eqv_sound _)

theorem of_relation_rel_exact : (of_relation r).exact r :=
  (exact_ext _ _ _ (weakened_id _ _)).mp
  (conditional_merge_rec₁_relaxes_weakened_exact _ _ _ _ (identity_weakened_trivial_exact _))

theorem of_relation_eqv_exact : (of_relation r).exact (EqvGen r) :=
  eqv_exact_of_rel_exact _ _ (of_relation_rel_exact _)

theorem of_relation_iff_eqv : ∀ i j : Fin n, (of_relation r).rel i j ↔ EqvGen r i j :=
  fun i j ↦ ⟨of_relation_eqv_sound r i j, of_relation_eqv_exact r i j⟩

end Partition

end Fin

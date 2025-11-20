/-
Copyright (c) 2025 Jonathan Konig. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Konig
-/
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fin.Pigeonhole

namespace Fin

open Function Tuple Nat LE Relation

section

variable {n : ℕ} (r : Fin n → Fin n → Prop)

/-- This definition produces a subset of a relation `Fin n → Fin n → Prop` filtered
by lexicographic comparison on a pair of `Fin (n + 1)` values.
-/
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

section

variable {n s : ℕ}

theorem monotone_min (map : Fin n → Fin s) (rep : Fin s → Fin n) :
    (∀ (i : Fin n) (v : Fin s), map i = v → rep v ≤ i) → ∀ (i : Fin n) (v : Fin s),
    ((sort rep).invFun ∘ map) i = v → (rep ∘ sort rep) v ≤ i := by
  intro min i v h
  simp
  apply min
  simp [<-h]

variable {map : Fin n → Fin s} {rep : Fin s → Fin n}

theorem monotone_rinv (rinv : RightInverse rep map) :
    RightInverse (rep ∘ sort rep) ((sort rep).invFun ∘ map) := by
  intro v
  simp [rinv _]

theorem monotone_mono (rinv : RightInverse rep map) : StrictMono (rep ∘ sort rep) :=
  (monotone_sort rep).strictMono_of_injective <| rinv.injective.comp <| Equiv.injective (sort rep)

end

section

variable {n s : ℕ} (map : Fin n → Fin s)

def minimum_option (v : Fin s) : Option (Fin n) :=
  find (map · = v)

theorem minimum_option_isSome_of_surj (surj : Surjective map) (v : Fin s) :
    (minimum_option map v).isSome := by
  apply Option.isSome_iff_ne_none.mpr
  apply find_eq_none_iff.not.mpr
  apply not_forall_of_exists_not
  apply (exists_congr (fun _ ↦ not_not)).mpr
  exact surj v

variable (surj : Surjective map)

def minimum_rep (v : Fin s) : Fin n :=
  Option.get _ (minimum_option_isSome_of_surj map surj v)

theorem minimum_rinv : RightInverse (minimum_rep map surj) map :=
  fun v ↦ (find_eq_some_iff.mp
    (Option.eq_some_of_isSome (minimum_option_isSome_of_surj map surj v))).left

theorem minimum_min : ∀ (i : Fin n) (v : Fin s), map i = v → minimum_rep map surj v ≤ i :=
  fun i v ↦ (find_eq_some_iff.mp
    (Option.eq_some_of_isSome (minimum_option_isSome_of_surj map surj v))).right i

end

section

variable {n s : ℕ}

variable (map : Fin n → Fin s) (surj : Surjective map)

def partition_map : Fin n → Fin s :=
  (sort (minimum_rep map surj)).invFun ∘ map

def partition_rep : Fin s → Fin n :=
  (minimum_rep map surj) ∘ sort (minimum_rep map surj)

theorem partition_rinv : RightInverse (partition_rep map surj) (partition_map map surj) :=
  monotone_rinv (minimum_rinv map surj)

theorem partition_min : ∀ (i : Fin n) (v : Fin s),
    partition_map map surj i = v → partition_rep map surj v ≤ i :=
  monotone_min _ _ (minimum_min map surj)

theorem partition_mono : StrictMono (partition_rep map surj) :=
  monotone_mono (minimum_rinv map surj)

theorem partition_map_eq_iff_map_eq : ∀ i j : Fin n,
    partition_map map surj i = partition_map map surj j ↔ map i = map j :=
  fun i j ↦ by simp [partition_map]

end

structure Partition (n : ℕ) where
  size : ℕ
  map : Fin n → Fin size
  rep : Fin size → Fin n
  rinv : RightInverse rep map
  min : ∀ i v, map i = v → rep v ≤ i
  mono : StrictMono rep

namespace Partition

section

variable {n : ℕ} (p : Partition n)

theorem map_surj : Surjective p.map :=
  p.rinv.surjective

theorem rep_inj : Injective p.rep :=
  p.rinv.injective

theorem size_le : p.size ≤ n :=
  le_of_surjective _ <| p.map_surj

theorem rep_map_id_iff_range {i : Fin n} : p.rep (p.map i) = i ↔ i ∈ Set.range p.rep :=
  Iff.intro (⟨p.map i, ·⟩) fun h ↦ h.elim <|
    fun v hv ↦ (congr_arg _ ((congr_arg _ hv.symm).trans (p.rinv v))).trans hv

theorem rep_eq_of_min {v : Fin p.size} {i : Fin n} :
    p.map i = v → (∀ j : Fin n, p.map j = v → i ≤ j) → p.rep v = i :=
  fun h₁ h₂ ↦ eq_of_val_eq <| le_antisymm (p.min _ _ h₁) <| h₂ _ <| p.rinv v

theorem min_iff_range {i : Fin n} :
    (∀ j : Fin n, p.map j = p.map i → i ≤ j) ↔ i ∈ Set.range p.rep :=
  Iff.intro (⟨p.map i, p.rep_eq_of_min rfl ·⟩)
    fun h ↦ ((p.rep_map_id_iff_range.mpr h).symm.le.trans <| p.min · _ ·)

theorem le_rep (v : Fin p.size) : v.val ≤ (p.rep v).val := by
  match v with
  | ⟨v, h⟩ =>
    induction v with
    | zero => exact Nat.zero_le _
    | succ v ih =>
      apply Nat.succ_le_of_lt
      apply le.trans_lt <| ih <| (Nat.lt_succ_self _).trans h
      exact p.mono <| Nat.lt_succ_self _

theorem map_le (i : Fin n) : (p.map i).val ≤ i.val :=
  Nat.le_of_not_lt fun h₁ ↦ not_le_of_gt ((p.mono h₁).trans_le (p.min _ _ rfl)) <|
    p.le_rep ⟨i.val, h₁.trans (p.map i).isLt⟩

theorem map_zero (i : Fin n) (h : i.val = 0) : (p.map i).val = 0 :=
  eq_zero_of_le_zero <| (p.map_le i).trans_eq h

theorem rep_zero (v : Fin p.size) (h : v.val = 0) : (p.rep v).val = 0 :=
  eq_zero_of_le_zero <| p.min ⟨0, zero_lt_of_lt <| v.isLt.trans_le p.size_le⟩ _ <|
    Fin.eq_of_val_eq <| (p.map_zero _ rfl).trans h.symm

theorem le_rep_of_lt_rep_succ_range (v : ℕ) (h : v + 1 < p.size) (i : Fin n) :
    i < (p.rep ⟨v + 1, h⟩).val → i ∈ Set.range p.rep → i ≤ p.rep ⟨v, (lt_succ_self _).trans h⟩ := by
  intro h₁ h₂
  replace h₂ := p.rep_map_id_iff_range.mpr h₂
  rw [<-h₂]
  apply p.mono.le_iff_le.mpr
  apply le_of_lt_succ
  exact p.mono.lt_iff_lt.mp <| h₂.le.trans_lt h₁

@[simp]
theorem map_rep_apply (v : Fin p.size) : p.map (p.rep v) = v :=
  p.rinv v

variable (i j : Fin n)

@[inline]
abbrev mapEq : Prop :=
  p.map i = p.map j

/-- The proposition that the image of the first argument is less than the image of the second. -/
@[inline]
abbrev mapLT : Prop :=
  p.map i < p.map j

/-- The proposition that the image of the first argument is less than the image of the second. -/
@[inline]
abbrev mapGT : Prop :=
  p.map j < p.map i

/-- Function for splitting on the ordering of the images of two inputs. -/
protected def splitOn {α : Sort*} : (p.mapEq i j → α) → (p.mapLT i j → α) → (p.mapGT i j → α) → α :=
  fun h₁ h₂ h₃ ↦
  if heq : p.mapEq i j then h₁ heq else
  if hlt : p.mapLT i j then h₂ hlt else
  h₃ <| lt_iff_le_and_ne.mpr ⟨not_lt.mp hlt, Ne.symm heq⟩

theorem splitOn_eq {α : Sort*} {h₁ : p.mapEq i j → α} {h₂ : p.mapLT i j → α} {h₃ : p.mapGT i j → α}
    (h : p.mapEq i j) : p.splitOn i j h₁ h₂ h₃ = h₁ h :=
  dite_cond_eq_true <| eq_true_intro h

theorem splitOn_lt {α : Sort*} {h₁ : p.mapEq i j → α} {h₂ : p.mapLT i j → α} {h₃ : p.mapGT i j → α}
    (h : p.mapLT i j) : p.splitOn i j h₁ h₂ h₃ = h₂ h :=
  (dite_cond_eq_false (eq_false_intro (Fin.ne_of_lt h))).trans <|
    dite_cond_eq_true <| eq_true_intro h

theorem splitOn_gt {α : Sort*} {h₁ : p.mapEq i j → α} {h₂ : p.mapLT i j → α} {h₃ : p.mapGT i j → α}
    (h : p.mapGT i j) : p.splitOn i j h₁ h₂ h₃ = h₃ h :=
  (dite_cond_eq_false (eq_false_intro (Fin.ne_of_gt h))).trans <|
    dite_cond_eq_false <| eq_false_intro <| not_lt.mpr <| le_of_lt h

instance mapEq_decidable : Decidable (p.mapEq i j) :=
  by infer_instance

instance mapEq_equivalence : Equivalence p.mapEq :=
  ⟨fun _ ↦ rfl, Eq.symm, Eq.trans⟩

end

protected def of_surjective {n s : ℕ} (map : Fin n → Fin s) (surj : Surjective map) :
    Partition n where
  size := s
  map := partition_map map surj
  rep := partition_rep map surj
  rinv := partition_rinv map surj
  min := partition_min map surj
  mono := partition_mono map surj

section

variable {n : ℕ} {p p' : Partition n}

theorem map_rep'_inj_of_mapEq_bij (h : ∀ (i j : Fin n), p.mapEq i j ↔ p'.mapEq i j) :
    Injective (p.map ∘ p'.rep) := by
  intro i j
  simp
  intro he
  replace he : _ = _ := (h _ _).mp he
  simpa using he

theorem map'_rep_inj_of_mapEq_bij (h : ∀ (i j : Fin n), p.mapEq i j ↔ p'.mapEq i j) :
    Injective (p'.map ∘ p.rep) := by
  intro i j
  simp
  intro he
  replace he : _ = _ := (h _ _).mpr he
  simpa using he

theorem size_eq_of_mapEq_bij (h : ∀ (i j : Fin n), p.mapEq i j ↔ p'.mapEq i j) :
    p.size = p'.size :=
  le_antisymm (le_of_injective _ <| map'_rep_inj_of_mapEq_bij h) <|
    le_of_injective _ <| map_rep'_inj_of_mapEq_bij h

theorem rep_map_inv_of_mapEq_bij (h : ∀ i j : Fin n, p.mapEq i j ↔ p'.mapEq i j) :
    ∀ i, p.rep (p.map i) = p'.rep (p'.map i) := by
  intro i
  match n with
  | 0 => exact i.elim0
  | n + 1 =>
  match i with
  | ⟨i, hi⟩ =>
  induction i using Nat.strongRec with
  | ind i ih =>
  if h₁ : ⟨i, hi⟩ ∈ Set.range p.rep then
    have h₂ := p'.min_iff_range.mp (p.min_iff_range.mpr h₁ · <| (h _ _).mpr ·)
    exact (p.rep_map_id_iff_range.mpr h₁).trans (p'.rep_map_id_iff_range.mpr h₂).symm
  else
    apply (not_forall.mp <| p.min_iff_range.not.mpr h₁).elim
    intro j hj
    have ⟨h₂, h₃⟩ := Decidable.not_imp_iff_and_not.mp hj
    rw [← h₂, ← (h _ _).mp h₂]
    have h₄ := gt_of_not_le h₃
    exact ih j.val h₄ <| h₄.trans hi

theorem rep_image_iff_of_mapEq_bij (h : ∀ i j : Fin n, p.mapEq i j ↔ p'.mapEq i j) :
    ∀ i, i ∈ Set.range p.rep ↔ i ∈ Set.range p'.rep :=
  fun i ↦ (rep_map_inv_of_mapEq_bij h i ▸ p.rep_map_id_iff_range.symm).trans p'.rep_map_id_iff_range

theorem rep_comm_inj_of_mapEq_bij (h : ∀ i j : Fin n, p.mapEq i j ↔ p'.mapEq i j) :
    ∀ (v : Fin p.size) (v' : Fin p'.size), p.rep v = p'.rep v' → v.val = v'.val := by
  intro v
  match v with
  | ⟨v, hv⟩ =>
  induction v with
  | zero =>
    intro v' hr
    apply Eq.symm <| eq_zero_of_le_zero _
    apply (@StrictMono.le_iff_le _ _ _ _ _ p'.mono _ ⟨0, hv.trans_eq <| size_eq_of_mapEq_bij h⟩).mp
    exact ((val_eq_of_eq hr.symm).trans <| p.rep_zero _ rfl).le.trans <| Nat.zero_le _
  | succ v ih =>
    intro v' hr
    have h₁ := (p.mono (lt_succ_self v : ⟨v, (lt_succ_self _).trans hv⟩ < ⟨_, hv⟩)).trans_eq hr
    have h₂ := zero_lt_of_ne_zero <| not_imp_not.mpr (p'.rep_zero _) <| Nat.ne_zero_of_lt h₁
    apply (Nat.add_one_inj.mpr _).trans <| sub_one_add_one_eq_of_pos h₂
    let w : Fin p'.size := ⟨v'.val - 1, (Nat.pred_le _).trans_lt v'.isLt⟩
    replace h₂ : v' = ⟨w.val + 1, (sub_one_add_one_eq_of_pos h₂).le.trans_lt v'.isLt⟩ :=
      eq_of_val_eq <| Eq.symm <| sub_one_add_one_eq_of_pos h₂
    have h₃ := (p'.mono ((lt_succ_self _).trans_eq <| Fin.val_eq_of_eq h₂.symm)).trans_eq hr.symm
    rw [h₂] at h₁
    apply ih ((lt_succ_self _).trans hv) w
    apply Fin.eq_of_val_eq
    apply Nat.le_antisymm
    · exact p'.le_rep_of_lt_rep_succ_range _ _ _ h₁ <| (rep_image_iff_of_mapEq_bij h _ ).mp ⟨_, rfl⟩
    · exact p.le_rep_of_lt_rep_succ_range _ _ _ h₃ <| (rep_image_iff_of_mapEq_bij h _ ).mpr ⟨_, rfl⟩

theorem map_eq_of_mapEq_bij (h : ∀ i j : Fin n, p.mapEq i j ↔ p'.mapEq i j) :
    ∀ i : Fin n, (p.map i).val = (p'.map i).val :=
  fun _ ↦ rep_comm_inj_of_mapEq_bij h _ _ <| rep_map_inv_of_mapEq_bij h _

end

section

variable {n : ℕ} (p p' : Partition n)

theorem rep_eq_of_map_eq : (∀ i : Fin n, (p.map i).val = (p'.map i).val) →
    ∀ (v : Fin p.size) (v' : Fin p'.size), v.val = v'.val → p.rep v = p'.rep v' :=
  fun h _ _ hv ↦ p.rep_eq_of_min
    (Fin.eq_of_val_eq <| (h _).trans <| (Fin.val_eq_of_eq (p'.rinv _)).trans hv.symm)
    fun _ hi ↦ p'.min _ _ <| Fin.eq_of_val_eq <| (h _).symm.trans <| (Fin.val_eq_of_eq hi).trans hv

protected theorem map_ext :
    p.size = p'.size → (∀ i : Fin n, (p.map i).val = (p'.map i).val) → p = p' := by
  intro h₁ h₂
  have h₃ := rep_eq_of_map_eq p p' h₂
  match p, p' with
  | Partition.mk s₁ m₁ r₁ ri₁ min₁ _, Partition.mk s₂ m₂ r₂ ri₂ min₂ _ =>
    obtain rfl : s₁ = s₂ := h₁
    obtain rfl : m₁ = m₂ := funext <| fun i ↦ Fin.eq_of_val_eq (h₂ i)
    obtain rfl : r₁ = r₂ := funext <| fun i ↦ h₃ i i rfl
    rfl

@[ext]
protected theorem ext : (∀ i j : Fin n, p.mapEq i j ↔ p'.mapEq i j) → p = p' :=
  fun h ↦ Partition.map_ext _ _ (size_eq_of_mapEq_bij h) <| map_eq_of_mapEq_bij h

end

section

def perm_of_surj {n s : ℕ} {f g : Fin n → Fin s} (hf : Function.Surjective f)
    (hg : Function.Surjective g) : Equiv.Perm (Fin s) :=
  (sort (minimum_rep g hg)).symm.trans (sort (minimum_rep f hf))

theorem perm_comm_of_surj_eq_iff {n s : ℕ} {f g : Fin n → Fin s} (hf : Function.Surjective f)
    (hg : Function.Surjective g) (h : ∀ i j : Fin n, f i = f j ↔ g i = g j) :
    f = perm_of_surj hf hg ∘ g := by
  let p₁ : Partition n := Partition.of_surjective f hf
  let p₂ : Partition n := Partition.of_surjective g hg
  have h₂ : p₁.map = (sort (minimum_rep f hf)).invFun ∘ f := rfl
  have h₃ : p₂.map = (sort (minimum_rep g hg)).invFun ∘ g := rfl
  unfold perm_of_surj
  simp [Function.comp_assoc]
  apply (Equiv.symm_comp_eq _ _ _).mp
  apply h₂.symm.trans (Eq.trans _ h₃)
  congr
  ext i j
  simpa [p₁, p₂, Partition.of_surjective, mapEq, partition_map] using h _ _

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
protected def id (n : ℕ) : Partition n where
  size := n
  map := (·)
  rep := (·)
  rinv := fun _ ↦ rfl
  min := fun _ _ h ↦ Fin.le_of_eq h.symm
  mono := fun _ _ ↦ (·)

variable (r : Fin n → Fin n → Prop)

theorem id_eqvGen_sound : (Partition.id n).sound (EqvGen r) := by
  intro i j he
  simp [mapEq] at he
  obtain rfl : i = j := he
  exact EqvGen.refl _

theorem id_weaken_trivial_exact : (Partition.id n).exact (weaken_rel r 0 0) := by
  intro i j ⟨hw, hr⟩
  apply hw.elim
  · intro h
    exact False.elim (Nat.not_lt_zero _ h)
  · intro ⟨_, h⟩
    exact False.elim (Nat.not_lt_zero _ h)

end

section

variable {n : ℕ} (p : Partition n)

def mergeLT_size : ℕ :=
  p.size - 1

def mergeLT_fin_of_lt (i : Fin n) {j : Fin n} (h : p.mapLT i j) : Fin p.mergeLT_size :=
  ⟨(p.map i).val, Nat.lt_of_lt_of_le h (Nat.le_pred_of_lt (p.map j).isLt)⟩

def mergeLT_fin_of_gt (i : Fin n) {j : Fin n} (h : p.mapGT i j) : Fin p.mergeLT_size :=
  ⟨(p.map i).val - 1, Nat.pred_lt_pred (Nat.ne_zero_of_lt h) (p.map i).isLt⟩

variable {l u : Fin n}

def mergeLT_map (h : p.mapLT l u) (i : Fin n) : Fin p.mergeLT_size :=
  p.splitOn i u (fun _ ↦ p.mergeLT_fin_of_lt l h) (p.mergeLT_fin_of_lt i) (p.mergeLT_fin_of_gt i)

@[simp]
lemma mergeLT_fin_of_lt_val (i : Fin n) {j : Fin n} (h : p.mapLT i j) :
    (p.mergeLT_fin_of_lt i h).val = (p.map i).val :=
  rfl

@[simp]
lemma mergeLT_fin_of_gt_val (i : Fin n) {j : Fin n} (h : p.mapGT i j) :
    (p.mergeLT_fin_of_gt i h).val = (p.map i).val - 1 :=
  rfl

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
    (p.mergeLT_map h i).val = (p.map l).val ↔ p.mapEq i l ∨ p.mapEq i u := by
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
    (p.mergeLT_map h i).val < (p.map u).val ↔ p.mapEq i u ∨ p.mapLT i u := by
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
    p.mapEq i j → p.mergeLT_map h i = p.mergeLT_map h j := by
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
    p.mapEq i j ∨ p.mapEq i l ∧ p.mapEq j u ∨ p.mapEq i u ∧ p.mapEq j l := by
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

def mergeLT_rep (_ : p.mapLT l u) (i : Fin p.mergeLT_size) : Fin n :=
  if i.val < (p.map u).val
  then p.rep (Fin.castLE (Nat.pred_le _) i)
  else p.rep ⟨i.val + 1, Nat.succ_lt_of_lt_pred i.isLt⟩

theorem mergeLT_rinv (h : p.mapLT l u) : RightInverse (p.mergeLT_rep h) (p.mergeLT_map h) := by
  intro i
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

theorem mergeLT_min (h : p.mapLT l u) (i : Fin n) (j : Fin p.mergeLT_size) :
    p.mergeLT_map h i = j → p.mergeLT_rep h j ≤ i := by
  intro h₁
  replace h₁ := Fin.val_eq_of_eq h₁
  if h₂ : j.val < (p.map u).val then
    simp [mergeLT_rep, h₂]
    apply p.splitOn i u
    · intro h₃
      exact Nat.le_trans (p.mono h₂).le (p.min i (p.map u) h₃)
    · intro h₃
      apply p.min
      apply Fin.eq_of_val_eq
      simp [p.mergeLT_map_of_lt _ _ h₃] at h₁
      exact h₁
    · intro h₃
      simp [p.mergeLT_map_of_gt _ _ h₃] at h₁
      exact (p.mono (h₂.trans h₃ : Fin.castLE (Nat.pred_le _) j < _)).le.trans <| p.min _ _ rfl
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

theorem mergeLT_mono (h : p.mapLT l u) : StrictMono (p.mergeLT_rep h) := by
  intro i j h₁
  if h₂ : j.val < (p.map u).val then
    simp [mergeLT_rep, Nat.lt_trans h₁ h₂, h₂]
    exact p.mono h₁
  else
    if h₃ : i.val < (p.map u).val then
      simp [mergeLT_rep, h₂, h₃]
      apply p.mono
      exact Nat.lt_trans h₁ (Nat.lt_succ_self _)
    else
      simp [mergeLT_rep, h₂, h₃]
      exact p.mono (Nat.add_lt_add_right h₁ _)

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
    p.sound (EqvGen r) → r i j → (p.merge i j).sound (EqvGen r) := by
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
    (p.merge i j).exact (weaken_rel r i.castSucc j.succ) := by
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
    p.exact (weaken_rel r i.castSucc j.succ) := by
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
    p.sound (EqvGen r) → (p.conditional_merge r i j).sound (EqvGen r) := by
  intro hs
  if hr : r i j then
    rw [conditional_merge, ite_cond_eq_true _ _ (eq_true_intro hr)]
    exact p.merge_preserves_eqvGen_sound_of_rel r i j hs hr
  else
    rw [conditional_merge, ite_cond_eq_false _ _ (eq_false_intro hr)]
    exact hs

lemma condition_merge_relaxes_weakened_exact :
    p.exact (weaken_rel r i.castSucc j.castSucc) →
    (p.conditional_merge r i j).exact (weaken_rel r i.castSucc j.succ) := by
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
    p.sound (EqvGen r) → (p.conditional_merge_rec₂ r i j h).sound (EqvGen r) := by
  intro hs
  induction j with
  | zero => exact hs
  | succ j ih => apply conditional_merge_preserves_eqvGen_sound ; apply ih

lemma conditional_merge_rec₁_preserves_eqvGen_sound (i : ℕ) (h : i < n + 1) :
    p.sound (EqvGen r) → (p.conditional_merge_rec₁ r i h).sound (EqvGen r) := by
  intro hs
  induction i with
  | zero => exact hs
  | succ i ih => apply conditional_merge_rec₂_preserves_eqvGen_sound ; apply ih

lemma conditional_merge_rec₂_relaxes_weakened_exact (i : Fin n) (j : ℕ) (h : j < n + 1) :
    p.exact (weaken_rel r i.castSucc 0) →
    (p.conditional_merge_rec₂ r i j h).exact (weaken_rel r i.castSucc ⟨j, h⟩) := by
  intro he
  induction j with
  | zero => exact he
  | succ j ih => apply condition_merge_relaxes_weakened_exact ; apply ih

lemma conditional_merge_rec₁_relaxes_weakened_exact (i : ℕ) (h : i < n + 1) :
    p.exact (weaken_rel r 0 0) →
    (p.conditional_merge_rec₁ r i h).exact (weaken_rel r ⟨i, h⟩ 0) := by
  intro he
  induction i with
  | zero => exact he
  | succ i ih =>
    apply lift_exact _ _ _ (fun _ _ ↦ (weaken_succ r ⟨i, Nat.add_lt_add_iff_right.mp h⟩ _ _).mpr)
    apply conditional_merge_rec₂_relaxes_weakened_exact ; apply ih

end

section

variable {n : ℕ} (r : Fin n → Fin n → Prop) [∀ i j : Fin n, Decidable (r i j)]

def of_relation : Partition n :=
  (Partition.id n).conditional_merge_rec₁ r n (lt_succ_self n)

theorem of_relation_eqvGen_sound : (of_relation r).sound (EqvGen r) :=
  conditional_merge_rec₁_preserves_eqvGen_sound _ _ _ _ (id_eqvGen_sound _ _)

theorem of_relation_exact : (of_relation r).exact r :=
  lift_exact _ _ _ (fun _ _ ↦ (weaken_last _ _ _ _).mpr)
    (conditional_merge_rec₁_relaxes_weakened_exact _ _ _ _ (id_weaken_trivial_exact _ _))

theorem of_relation_eqvGen_exact : (of_relation r).exact (EqvGen r) :=
  eqvGen_exact_of_exact _ _ (of_relation_exact _)

theorem of_relation_iff_eqvGen : ∀ i j : Fin n, (of_relation r).mapEq i j ↔ EqvGen r i j :=
  fun i j ↦ ⟨of_relation_eqvGen_sound r i j, of_relation_eqvGen_exact r i j⟩

end

section

instance rel_decidable_of_partition {n : ℕ} (p : Partition n) (r : Fin n → Fin n → Prop)
    (h : ∀ i j : Fin n, p.mapEq i j ↔ r i j) (i j : Fin n) : Decidable (r i j) :=
  decidable_of_decidable_of_iff (h i j)

theorem of_relation_mapEq_eq_eqvGen {n : ℕ} (r : Fin n → Fin n → Prop)
    [∀ i j : Fin n, Decidable (r i j)] : (of_relation r).mapEq = EqvGen r :=
  funext₂ <| fun _ _ ↦ propext <| of_relation_iff_eqvGen _ _ _

theorem of_eqv_relation_mapEq_id {n : ℕ} {r : Fin n → Fin n → Prop}
    (h : Equivalence r) [∀ i j : Fin n, Decidable (r i j)] : (of_relation r).mapEq = r :=
  (of_relation_mapEq_eq_eqvGen r).trans <| Equivalence.eqvGen_eq h

theorem mapEq_to_relation_id {n : ℕ} (p : Partition n) : of_relation p.mapEq = p := by
  ext i j
  apply Iff.intro _ (of_relation_exact p.mapEq i j)
  exact (Equivalence.eqvGen_eq p.mapEq_equivalence ▸ (of_relation_iff_eqvGen p.mapEq i j).mp ·)

end

end Partition

end Fin

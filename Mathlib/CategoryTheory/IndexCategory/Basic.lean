/-
Copyright (c) 2025 Jonathan Konig. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Konig
-/
import Mathlib.Data.Nat.Basic
import Mathlib.Order.Basic
import Mathlib.CategoryTheory.Iso

/-! # The index category

The index category, a skeleton of the category of finite sets and functions, is
defined with objects `ℕ` and morphisms `m ⟶ n` the maps from `Fin m` to `Fin n`.

## Remarks

The definitions `IndexCategory` and `IndexCategory.Hom` are marked as irreducible.

We provide the following irreducible functions to work with these objects:
1. `IndexCategory.mk` creates an object of `IndexCategory` from a natural number
2. `IndexCategory.len` gives the natural number for an object of `IndexCategory`.
3. `IndexCategory.Hom.mk` creates a morphism out of a map between `Fin`'s.
4. `IndexCategory.Hom.mk` gives the underyling map for an object of `IndexCategory.Hom`.
-/

namespace CategoryTheory

/-- The objects of the index category are the natural numbers `ℕ` -/
def IndexCategory : Type :=
  ℕ

namespace IndexCategory

/-- Interpret a natural number as an object of the index category. -/
def mk (n : ℕ) : IndexCategory :=
  n

/-- The length of an object of `IndexCategory` as a natural number. -/
def len (n : IndexCategory) : ℕ :=
  n

@[ext]
theorem ext (m n : IndexCategory) : m.len = n.len → m = n :=
  id

attribute [irreducible] IndexCategory

@[simp]
theorem len_mk (n : ℕ) : (mk n).len = n :=
  rfl

@[simp]
theorem mk_len (n : IndexCategory) : mk n.len = n :=
  rfl

/-- A recursor for `IndexCategory`. -/
protected def rec {F : IndexCategory → Sort*} (h : ∀ n : ℕ, F (mk n)) : ∀ n, F n :=
  (h <| len ·)

attribute [irreducible] IndexCategory.mk
attribute [irreducible] IndexCategory.len

/-- A recursor for `IndexCategory` applied on an argument. -/
protected def recOn (n : IndexCategory) {F : IndexCategory → Sort*} (h : ∀ n : ℕ, F (mk n)) : F n :=
  IndexCategory.rec h n

protected theorem rec_heq {F : IndexCategory → Sort*} (h : ∀ n : ℕ, F (mk n)) :
    ∀ n, IndexCategory.rec h n ≍ h n.len :=
  IndexCategory.rec <| by simp [IndexCategory.rec]

protected theorem recOn_heq (n : IndexCategory) {F : IndexCategory → Sort*}
    (h : ∀ n : ℕ, F (mk n)) : IndexCategory.recOn n h ≍ h n.len :=
  IndexCategory.rec_heq h n

instance sizeOf : SizeOf IndexCategory where
  sizeOf n := n.len

@[simp]
protected theorem sizeOf_eq_len (n : IndexCategory) : SizeOf.sizeOf n = n.len :=
  rfl

/-- The addition operation on objects of `IndexCategory` is defined by adding
the lengths of the objects.
-/
protected def add (m n : IndexCategory) : IndexCategory :=
  mk <| m.len + n.len

/-- The subtraction operation on objects of `IndexCategory` is defined by
subtracting the lengths of the objects.
-/
protected def sub (m n : IndexCategory) : IndexCategory :=
  mk <| m.len - n.len

/-- The multiplication operation on objects of `IndexCategory` is defined by
multiplying the lengths of the objects.
-/
protected def mul (m n : IndexCategory) : IndexCategory :=
  mk <| m.len * n.len

/-- The homogenous power operation on objects of `IndexCategory` is defined by
the power operation on the lengths of the objects.
-/
protected def pow (m n : IndexCategory) : IndexCategory :=
  mk <| m.len ^ n.len

instance : Add IndexCategory where
  add := IndexCategory.add

instance : Sub IndexCategory where
  sub := IndexCategory.sub

instance : Mul IndexCategory where
  mul := IndexCategory.mul

instance : HomogeneousPow IndexCategory where
  pow := IndexCategory.pow

@[simp]
theorem add_len {m n : IndexCategory} : (m + n).len = m.len + n.len :=
  len_mk _

@[simp]
theorem sub_len {m n : IndexCategory} : (m - n).len = m.len - n.len :=
  len_mk _

@[simp]
theorem mul_len {m n : IndexCategory} : (m * n).len = m.len * n.len :=
  len_mk _

@[simp]
theorem pow_len {m n : IndexCategory} : (m ^ n).len = m.len ^ n.len :=
  len_mk _

protected theorem add_comm (m n : IndexCategory) : m + n = n + m :=
  ext _ _ <| by simp [Nat.add_comm]

protected theorem add_assoc (m n k : IndexCategory) : m + n + k = m + (n + k) :=
  ext _ _ <| by simp [Nat.add_assoc]

theorem left_add_injective (m : IndexCategory) : Function.Injective (m + ·) :=
  fun _ _ h ↦ ext _ _ <| by simpa using IndexCategory.ext_iff.mp h

theorem right_add_injective (m : IndexCategory) : Function.Injective (· + m) :=
  fun _ _ h ↦ ext _ _ <| by simpa using IndexCategory.ext_iff.mp h

/-- The zero object in the index category. -/
def zero : IndexCategory :=
  mk 0

/-- The one object in the index category. -/
def one : IndexCategory :=
  mk 1

@[simp]
theorem zero_len : zero.len = 0 :=
  len_mk _

protected theorem zero_eq_mk : zero = mk 0 :=
  rfl

protected theorem zero_add {n : IndexCategory} : zero + n = n :=
  ext _ _ <| add_len.trans <| zero_len ▸ Nat.zero_add _

protected theorem add_zero {n : IndexCategory} : n + zero = n :=
  ext _ _ <| add_len.trans <| zero_len ▸ Nat.add_zero _

@[simp]
theorem one_len : one.len = 1 :=
  len_mk _

theorem one_eq_mk : one = mk 1 :=
  rfl

theorem mk_succ {n : ℕ} : mk n + one = mk (n + 1) :=
  ext _ _ <| add_len.trans <| (congr_arg₂ _ (len_mk _) one_len).trans (len_mk _).symm

theorem succ_len {n : IndexCategory} : (n + one).len = n.len + 1 :=
  add_len.trans <| congr_arg₂ _ rfl one_len

/-- We define the cases eliminator for objects of `IndexCategory` with the
cases `IndexCategory.zero` and `n + IndexCategory.one`, analogously to the natural
numbers.
-/
@[cases_eliminator]
protected def cases {F : IndexCategory → Sort*} (zero : F zero) (succ : ∀ n, F (n + one)) :
    ∀ n, F n :=
  IndexCategory.rec <| fun | 0 => zero | n + 1 => mk_succ ▸ succ (mk n)

protected theorem cases_zero {F : IndexCategory → Sort*} (zero : F zero) (succ : ∀ n, F (n + one)) :
    IndexCategory.cases zero succ IndexCategory.zero = zero :=
  heq_iff_eq.mp <| (IndexCategory.rec_heq _ _).trans <| by rw [zero_len]

protected theorem cases_succ {F : IndexCategory → Sort*} (zero : F zero) (succ : ∀ n, F (n + one))
    (n : IndexCategory) : IndexCategory.cases zero succ (n + one) = succ n := by
  apply IndexCategory.recOn n
  intro n
  apply heq_iff_eq.mp
  apply (IndexCategory.rec_heq _ _).trans
  rw [add_len, one_len, len_mk]
  simp

/-- We define the induction eliminator for objects of `IndexCategory` with
the base case for `IndexCategory.zero` and the inductive step for `n + IndexCategory.one`.
-/
@[induction_eliminator]
protected def induction {F : IndexCategory → Sort*} (zero : F zero)
    (succ : ∀ n, F n → F (n + one)) : ∀ n, F n :=
  IndexCategory.rec <| Nat.rec zero <| fun _ h ↦ mk_succ ▸ succ _ h

protected theorem induction_zero {F : IndexCategory → Sort*} (zero : F zero)
    (succ : ∀ n, F n → F (n + one)) : IndexCategory.induction zero succ IndexCategory.zero = zero :=
  heq_iff_eq.mp <| (IndexCategory.rec_heq _ _).trans <| by rw [zero_len] ; simp

protected theorem induction_succ {F : IndexCategory → Sort*} (zero : F zero)
    (succ : ∀ n, F n → F (n + one)) (n : IndexCategory) :
    IndexCategory.induction zero succ (n + one) = succ n (IndexCategory.induction zero succ n) := by
  apply IndexCategory.recOn n
  intro n
  apply heq_iff_eq.mp
  apply (IndexCategory.rec_heq _ _).trans
  rw [add_len, one_len, len_mk]
  simp [IndexCategory.induction, IndexCategory.rec]

/-- A varaint of the induction principle applied on an argument. -/
@[elab_as_elim]
protected def inductionOn (n : IndexCategory) {F : IndexCategory → Sort*} (zero : F zero)
    (succ : ∀ n, F n → F (n + one)) : F n :=
  IndexCategory.induction zero succ n

protected theorem inductionOn_zero {F : IndexCategory → Sort*} (zero : F zero)
    (succ : ∀ n, F n → F (n + one)) :
    IndexCategory.inductionOn IndexCategory.zero zero succ = zero :=
  IndexCategory.induction_zero zero succ

protected theorem inductionOn_succ (n : IndexCategory) {F : IndexCategory → Sort*} (zero : F zero)
    (succ : ∀ n, F n → F (n + one)) : IndexCategory.inductionOn (n + one) zero succ
    = succ n (IndexCategory.inductionOn n zero succ) :=
  IndexCategory.induction_succ zero succ n

/-- Helper function for the zero case of well-founded induction. -/
protected def recLE_zero_hyp {F : IndexCategory → Sort*} {m : IndexCategory}
    (hm : m.len ≤ zero.len) (k : IndexCategory) : k.len < m.len → F k :=
  fun h ↦ False.elim <| Nat.not_lt_zero _ <| h.trans_le <| hm.trans_eq zero_len

/-- Helper function for the successor case of well-founded induction. -/
protected def recLE_succ_hyp {F : IndexCategory → Sort*} {n : IndexCategory}
    (ih : ∀ m, m.len ≤ n.len → F m) {m : IndexCategory} (hm : m.len ≤ (n + one).len)
    (k : IndexCategory) : k.len < m.len → F k :=
  fun hk ↦ ih k <| Nat.le_of_lt_succ <| (hk.trans_le hm).trans_eq succ_len

/-- Helper recursion principle for well-founded induction. -/
@[elab_as_elim]
protected def recLE {F : IndexCategory → Sort*} (succ : ∀ n, (∀ m, m.len < n.len → F m) → F n) :
    ∀ n m : IndexCategory, m.len ≤ n.len → F m :=
  IndexCategory.induction (succ · <| IndexCategory.recLE_zero_hyp ·) <|
    fun n ih m ↦ if h : m.len ≤ n.len then fun _ ↦ ih m h
      else (succ m <| IndexCategory.recLE_succ_hyp ih ·)

protected theorem recLE_zero {F : IndexCategory → Sort*}
    (succ : ∀ n, (∀ m, m.len < n.len → F m) → F n) {m : IndexCategory} (hm : m.len ≤ zero.len) :
    IndexCategory.recLE succ zero m hm = succ m (IndexCategory.recLE_zero_hyp hm) := by
  exact congr_fun₂ (@IndexCategory.induction_zero (fun n ↦ ∀ m, m.len ≤ n.len → F m) _ _) m hm

protected theorem recLE_reduction {F : IndexCategory → Sort*}
    (succ : ∀ n, (∀ m, m.len < n.len → F m) → F n) (n m : IndexCategory) (hm : m.len ≤ n.len) :
    (IndexCategory.recLE succ n m hm : F m) = IndexCategory.recLE succ m m (Nat.le_refl _) := by
  induction n with
  | zero =>
    obtain rfl : m = zero :=
      ext _ _ <| (Nat.eq_zero_of_le_zero (hm.trans_eq zero_len)).trans zero_len.symm
    rfl
  | succ n ih =>
    if h : m.len ≤ n.len then
      nth_rewrite 1 [IndexCategory.recLE, IndexCategory.induction_succ]
      simp [h]
      exact ih h
    else
      obtain rfl : m = n + one := ext _ _ <| Nat.le_antisymm hm <|
        succ_len.le.trans <| Nat.succ_le_of_lt <| Nat.lt_of_not_le h
      rfl

protected theorem recLE_confluence {F : IndexCategory → Sort*}
    (succ : ∀ n, (∀ m, m.len < n.len → F m) → F n) (n m k : IndexCategory) (hn : k.len ≤ n.len)
    (hm : k.len ≤ m.len) :
    (IndexCategory.recLE succ n k hn : F k) = IndexCategory.recLE succ m k hm :=
  (IndexCategory.recLE_reduction succ n k hn).trans (IndexCategory.recLE_reduction succ m k hm).symm

protected theorem recLE_succ_refl {F : IndexCategory → Sort*}
    (succ : ∀ n, (∀ m, m.len < n.len → F m) → F n) (n : IndexCategory) :
    IndexCategory.recLE succ (n + one) (n + one) (Nat.le_refl _) = succ (n + one)
    (IndexCategory.recLE_succ_hyp (IndexCategory.recLE succ n) (Nat.le_refl _)) := by
  nth_rewrite 1 [IndexCategory.recLE, IndexCategory.induction_succ]
  simp [Nat.not_add_one_le_self]
  rfl

protected theorem recLE_succ {F : IndexCategory → Sort*}
    (succ : ∀ n, (∀ m, m.len < n.len → F m) → F n) (n : IndexCategory) {m : IndexCategory}
    (hm : m.len ≤ (n + one).len) : IndexCategory.recLE succ (n + one) m hm
    = succ m (IndexCategory.recLE_succ_hyp (IndexCategory.recLE succ n) hm) := by
  apply (IndexCategory.recLE_reduction _ _ _ _).trans
  cases m with
  | zero =>
    rw [IndexCategory.recLE_zero]
    apply congr_arg
    funext k hk
    exact False.elim (Nat.not_lt_zero _ <| hk.trans_eq zero_len)
  | succ m =>
    rw [IndexCategory.recLE_succ_refl]
    apply congr_arg
    funext k hk
    simp [IndexCategory.recLE_succ_hyp]
    exact IndexCategory.recLE_confluence _ m n k (Nat.le_of_lt_succ <| hk.trans_eq succ_len)
      (Nat.le_of_lt_succ <| hk.trans_le <| hm.trans_eq succ_len)

/- Recusion principle for well-founded induction. -/
@[elab_as_elim]
protected def recLT {F : IndexCategory → Sort*} (succ : ∀ n, (∀ m, m.len < n.len → F m) → F n) :
    ∀ n, F n :=
  fun n ↦ IndexCategory.recLE succ n n (Nat.le_refl _)

protected theorem recLT_zero {F : IndexCategory → Sort*}
    (succ : ∀ n, (∀ m, m.len < n.len → F m) → F n) : IndexCategory.recLT succ zero
    = succ zero (IndexCategory.recLE_zero_hyp (Nat.le_refl _)) :=
  IndexCategory.recLE_zero _ _

protected theorem recLT_succ {F : IndexCategory → Sort*}
    (succ : ∀ n, (∀ m, m.len < n.len → F m) → F n) (n : IndexCategory) :
    IndexCategory.recLT succ (n + one) = succ (n + one)
    (IndexCategory.recLE_succ_hyp (IndexCategory.recLE succ n) (Nat.le_refl _)) :=
  IndexCategory.recLE_succ _ _ _

/-- Recursion principle for strong induction. -/
@[elab_as_elim]
protected def strongRec {F : IndexCategory → Sort*} (zero : F zero)
    (succ : ∀ n, (∀ m, m.len ≤ n.len → F m) → F (n + one)) : ∀ n, F n :=
  IndexCategory.recLT (IndexCategory.cases (fun _ ↦ zero)
    (fun _ ih ↦ succ _ (fun hm ↦ ih · <| (Nat.lt_succ_of_le hm).trans_eq succ_len.symm)))

protected theorem strongRec_zero {F : IndexCategory → Sort*} (zero : F zero)
    (succ : ∀ n, (∀ m, m.len ≤ n.len → F m) → F (n + one)) :
    IndexCategory.strongRec zero succ IndexCategory.zero = zero :=
  (IndexCategory.recLT_zero _).trans <| by rw [IndexCategory.cases_zero]

protected theorem strongRec_succ {F : IndexCategory → Sort*} (zero : F zero)
    (succ : ∀ n, (∀ m, m.len ≤ n.len → F m) → F (n + one)) (n : IndexCategory) :
    IndexCategory.strongRec zero succ (n + one)
    = succ n (fun _ ↦ IndexCategory.strongRec zero succ ·) := by
  apply (IndexCategory.recLT_succ _ _).trans
  rw [IndexCategory.cases_succ]
  exact congr_arg _ (funext₂ (IndexCategory.recLE_reduction _ _ · ·))

/-- The morphisms `m ⟶ n` in the index category are the maps `Fin m.len → Fin n.len`. -/
protected def Hom (m n : IndexCategory) : Type :=
  Fin m.len → Fin n.len

namespace Hom

/-- Interpret a map of `Fin`'s as a morphism in the index category. -/
def mk {m n : IndexCategory} (f : Fin m.len → Fin n.len) : IndexCategory.Hom m n :=
  f

/-- The underlying map of `Fin`'s of a morphism in the index category. -/
def toFun {m n : IndexCategory} (f : IndexCategory.Hom m n) : Fin m.len → Fin n.len :=
  f

@[ext]
theorem ext' {m n : IndexCategory} (f g : IndexCategory.Hom m n) : f.toFun = g.toFun → f = g :=
  id

attribute [irreducible] IndexCategory.Hom

@[simp]
theorem mk_toFun {m n : IndexCategory} (f : IndexCategory.Hom m n) : mk f.toFun = f :=
  rfl

@[simp]
theorem toFun_mk {m n : IndexCategory} (f : Fin m.len → Fin n.len) : (mk f).toFun = f :=
  rfl

attribute [irreducible] IndexCategory.Hom.mk
attribute [irreducible] IndexCategory.Hom.toFun

@[simp]
theorem toFun_mk_apply {m n : IndexCategory} (f : Fin m.len → Fin n.len) (i : Fin m.len) :
    (mk f).toFun i = f i :=
  congr_fun (toFun_mk f) i

/-- Identity morphisms in the index category are given by the identitiy maps. -/
@[simp]
def id (n : IndexCategory) : IndexCategory.Hom n n :=
  mk (·)

/-- Morphism compoisiton in the index category is given by function composition. -/
@[simp]
def comp {m n k : IndexCategory} (f : IndexCategory.Hom m n) (g : IndexCategory.Hom n k) :
    IndexCategory.Hom m k :=
  mk <| g.toFun ∘ f.toFun

end Hom

instance smallCategory : SmallCategory.{0} IndexCategory where
  Hom m n := IndexCategory.Hom m n
  id n := IndexCategory.Hom.id n
  comp f g := IndexCategory.Hom.comp f g

@[simp]
theorem id_toFun (n : IndexCategory) : Hom.toFun (𝟙 n) = (·) :=
  Hom.toFun_mk _

@[simp]
theorem comp_toFun {m n k : IndexCategory} (f : m ⟶ n) (g : n ⟶ k) :
    (f ≫ g).toFun = g.toFun ∘ f.toFun :=
  Hom.toFun_mk _

@[ext]
theorem Hom.ext {m n : IndexCategory} (f g : m ⟶ n) : f.toFun = g.toFun → f = g :=
  Hom.ext' _ _

theorem congr_toFun_apply {m n : IndexCategory} (f : m ⟶ n) (i j : Fin m.len) :
    i.val = j.val → f.toFun i = f.toFun j :=
  fun h ↦ congr_arg _ (Fin.eq_of_val_eq h)

theorem congr_toFun_apply_val {m n : IndexCategory} (f : m ⟶ n) (i j : Fin m.len) :
    i.val = j.val → (f.toFun i).val = (f.toFun j).val :=
  fun h ↦ congr_arg _ (congr_toFun_apply _ _ _ h)

/-- The zero value of type `Fin (n + one).len`. -/
def fin_succ_first (n : IndexCategory) : Fin (n + one).len :=
  ⟨0, by simp⟩

/-- The last value of type `Fin (n + one).len`. -/
def fin_succ_last (n : IndexCategory) : Fin (n + one).len :=
  ⟨n.len, by simp⟩

/-- The unique value of type `Fin one.len`. -/
def fin_one : Fin one.len :=
  ⟨0, by simp⟩

@[simp]
theorem fin_succ_first_val {n : IndexCategory} : n.fin_succ_first.val = 0 :=
  rfl

@[simp]
theorem fin_succ_last_val {n : IndexCategory} : n.fin_succ_last.val = n.len :=
  rfl

@[simp]
theorem fin_one_val : fin_one.val = 0 :=
  rfl

theorem eq_last_of_not_lt {n : IndexCategory} {i : Fin (n + one).len} (h : ¬ i.val < n.len) :
    i = fin_succ_last n :=
  Fin.eq_of_val_eq <| Nat.eq_of_lt_succ_of_not_lt (i.isLt.trans_eq succ_len) h

/-- The type `Fin zero.len` is uninhabited, so it can be used to derive any result whatsoever. -/
def elim_zero (i : Fin zero.len) {α : Sort*} : α :=
  Fin.elim0 <| Fin.cast (len_mk 0) i

theorem fin_one_ext (i j : Fin one.len) : i = j :=
  (congr_arg Fin one_len.symm ▸ Fin.subsingleton_one).elim i j

/-- Construct a morphism with domain `IndexCategory.zero` using `IndexCategory.elim_zero`. -/
def zero_to (n : IndexCategory) : zero ⟶ n :=
  Hom.mk <| fun i ↦ elim_zero i

theorem zero_to_ext {n : IndexCategory} (f g : zero ⟶ n) : f = g :=
  Hom.ext _ _ <| funext fun i ↦ elim_zero i

theorem eq_zero_to_ext {m n : IndexCategory} (h : m = zero) (f g : m ⟶ n) : f = g :=
  by subst h ; exact zero_to_ext f g

/-- The type of morphisms `n + one ⟶ zero` is uninhabited, so it can be used to derive
any result whatsoever.
-/
def elim_succ_to_zero {n : IndexCategory} (f : n + one ⟶ zero) {α : Sort*} : α :=
  elim_zero <| f.toFun <| fin_succ_first _

theorem zero_to_zero_id : zero_to zero = 𝟙 zero :=
  zero_to_ext _ _

theorem eq_zero_of_to_zero {n : IndexCategory} (f : n ⟶ zero) : n = zero := by
  cases n with
  | zero => rfl
  | succ n => exact elim_succ_to_zero f

theorem eq_zero_of_to_mk_zero {n : IndexCategory} (f : n ⟶ mk 0) : n = zero :=
  eq_zero_of_to_zero <| IndexCategory.zero_eq_mk ▸ f

/-- Construct a morphism whose underlying function is constant. -/
def const (m n : IndexCategory) (i : Fin n.len) : m ⟶ n :=
  Hom.mk <| Function.const _ i

@[simp]
theorem const_toFun (m n : IndexCategory) (i : Fin n.len) :
    (const m n i).toFun = Function.const _ i :=
  Hom.toFun_mk _

@[reassoc (attr := simp)]
theorem comp_const {m n k : IndexCategory} (f : m ⟶ n) (i : Fin k.len) :
    f ≫ const n k i = const m k i :=
  by ext _ ; simp

@[reassoc]
theorem const_comp {m n k : IndexCategory} (i : Fin n.len) (f : n ⟶ k) :
    const m n i ≫ f = const m k (f.toFun i) :=
  by ext _ ; simp

/-- Construct a morphism with codomain `IndexCategory.one` using the constant map
with value `IndexCategory.fin_one`.
-/
@[inline]
abbrev to_one (n : IndexCategory) : n ⟶ one :=
  const n one fin_one

theorem to_one_ext {n : IndexCategory} (f g : n ⟶ one) : f = g :=
  Hom.ext _ _ (funext fun _ ↦ fin_one_ext _ _)

theorem to_one_one_id : to_one one = 𝟙 one :=
  to_one_ext _ _

/-- Construct a morphism with domain `IndexCategory.one` by specifiying the unique value
in the image of the underlying map.
-/
@[inline]
abbrev one_to {n : IndexCategory} (i : Fin n.len) : one ⟶ n :=
  const one n i

theorem one_to_ext {n : IndexCategory} (f g : one ⟶ n) :
    (f.toFun fin_one).val = (g.toFun fin_one).val → f = g := by
  intro h
  ext i
  obtain rfl : i = fin_one := fin_one_ext _ _
  exact h

theorem one_to_fin_one_id : one_to fin_one = 𝟙 one :=
  to_one_ext _ _

@[reassoc]
theorem one_to_comp {m n : IndexCategory} (i : Fin m.len) (f : m ⟶ n) :
    one_to i ≫ f = one_to (f.toFun i) :=
  one_to_ext _ _ <| by simp

/-- Construct a morphism between two equal objects. The underlying map of the morphism
uses `Fin.cast` to ensure values can be computed. -/
def eqHom {m n : IndexCategory} (h : m = n) : m ⟶ n :=
  Hom.mk <| Fin.cast (congr_arg _ h)

@[simp]
theorem eqHom_toFun {m n : IndexCategory} (h : m = n) :
    (eqHom h).toFun = Fin.cast (congr_arg _ h) :=
  Hom.toFun_mk _

@[simp]
theorem eqHom_id (n : IndexCategory) : eqHom (Eq.refl n) = 𝟙 n :=
  rfl

@[reassoc (attr := simp)]
theorem eqHom_trans {m n k : IndexCategory} (h₁ : m = n) (h₂ : n = k) :
    eqHom h₁ ≫ eqHom h₂ = eqHom (h₁.trans h₂) :=
  Hom.ext _ _ (funext fun _ ↦ by simp)

theorem comp_eqHom_iff {m n k : IndexCategory} (f : m ⟶ n) (g : m ⟶ k) (h : n = k) :
    f ≫ eqHom h = g ↔ f = g ≫ eqHom h.symm :=
  by subst h ; simp

theorem eqHom_comp_iff {m n k : IndexCategory} (f : n ⟶ k) (g : m ⟶ k) (h : m = n) :
    eqHom h ≫ f = g ↔ f = eqHom h.symm ≫ g :=
  by subst h ; simp

theorem eq_of_eqHom_comp_eq {m n k : IndexCategory} (h : m = n) (f g : n ⟶ k) :
    eqHom h ≫ f = eqHom h ≫ g → f = g :=
  fun h' ↦ by simpa using (eqHom_comp_iff _ _ _).mp h'

theorem eq_of_comp_eqHom_eq {m n k : IndexCategory} (h : n = k) (f g : m ⟶ n) :
    f ≫ eqHom h = g ≫ eqHom h → f = g :=
  fun h' ↦ by simpa using (comp_eqHom_iff _ _ _).mp h'

/-- Construct an isomorphism between two equal objects using `IndexCategory.eqHom`. -/
def eqIso {m n : IndexCategory} (h : m = n) : m ≅ n where
  hom := eqHom h
  inv := eqHom h.symm

/-- The commutativity isomorphism `m + n ≅ n + m` using `IndexCategory.eqIso`. -/
def commIso {m n : IndexCategory} : m + n ≅ n + m :=
  eqIso (IndexCategory.add_comm m n)

/-- The associativity isomorphism `m + n + k ≅ m + (n + k)` using `IndexCategory.eqIso`. -/
def assocIso {m n k : IndexCategory} : m + n + k ≅ m + (n + k) :=
  eqIso (IndexCategory.add_assoc m n k)

@[simp]
theorem eqIso_hom_toFun {m n : IndexCategory} (h : m = n) :
    (eqIso h).hom.toFun = Fin.cast (congr_arg _ h) :=
  eqHom_toFun h

@[simp]
theorem eqIso_inv_toFun {m n : IndexCategory} (h : m = n) :
    (eqIso h).inv.toFun = Fin.cast (congr_arg _ h.symm) :=
  eqHom_toFun h.symm

@[simp]
theorem commIso_hom_toFun {m n : IndexCategory} :
    commIso.hom.toFun = Fin.cast (congr_arg _ (IndexCategory.add_comm m n)) :=
  eqHom_toFun (IndexCategory.add_comm m n)

@[simp]
theorem commIso_inv_toFun {m n : IndexCategory} :
    commIso.inv.toFun = Fin.cast (congr_arg _ (IndexCategory.add_comm n m)) :=
  eqHom_toFun (IndexCategory.add_comm n m)

@[simp]
theorem assocIso_hom_toFun {m n k : IndexCategory} :
    assocIso.hom.toFun = Fin.cast (congr_arg _ (IndexCategory.add_assoc m n k)) :=
  eqHom_toFun (IndexCategory.add_assoc m n k)

@[simp]
theorem assocIso_inv_toFun {m n k : IndexCategory} :
    assocIso.inv.toFun = Fin.cast (congr_arg _ (IndexCategory.add_assoc m n k).symm) :=
  eqHom_toFun (IndexCategory.add_assoc m n k).symm

theorem iso_hom_toFun_injective {m n : IndexCategory} (h : m ≅ n) :
    Function.Injective h.hom.toFun := by
  apply @Function.LeftInverse.injective _ _ h.inv.toFun _
  intro i
  simpa [-Iso.hom_inv_id] using (congr_fun (congr_arg Hom.toFun h.hom_inv_id) i)

theorem iso_hom_toFun_surjective {m n : IndexCategory} (h : m ≅ n) :
    Function.Surjective h.hom.toFun := by
  apply @Function.RightInverse.surjective _ _ _ h.inv.toFun
  intro i
  simpa [-Iso.inv_hom_id] using (congr_fun (congr_arg Hom.toFun h.inv_hom_id) i)

theorem iso_hom_toFun_bijective {m n : IndexCategory} (h : m ≅ n) :
  Function.Bijective h.hom.toFun := ⟨iso_hom_toFun_injective h, iso_hom_toFun_surjective h⟩

theorem iso_inv_toFun_injective {m n : IndexCategory} (h : m ≅ n) :
  Function.Injective h.inv.toFun := iso_hom_toFun_injective h.symm

theorem iso_inv_toFun_surjective {m n : IndexCategory} (h : m ≅ n) :
  Function.Surjective h.inv.toFun := iso_hom_toFun_surjective h.symm

theorem iso_inv_toFun_bijective {m n : IndexCategory} (h : m ≅ n) :
  Function.Bijective h.inv.toFun := iso_hom_toFun_bijective h.symm

theorem eq_iff_comp_inj_eq {m n : IndexCategory} {f : m ⟶ n} (h : Function.Injective f.toFun)
    {k : IndexCategory} (g₁ g₂ : k ⟶ m) : g₁ = g₂ ↔ g₁ ≫ f = g₂ ≫ f := by
  apply Iff.intro (· =≫ f)
  intro h'
  ext i : 2
  apply h
  simpa using congr_fun (congr_arg Hom.toFun h') i

theorem eq_iff_surj_comp_eq {m n : IndexCategory} {f : m ⟶ n} (h : Function.Surjective f.toFun)
    {k : IndexCategory} (g₁ g₂ : n ⟶ k) : g₁ = g₂ ↔ f ≫ g₁ = f ≫ g₂ := by
  apply Iff.intro (f ≫= ·)
  intro h'
  ext i : 2
  apply Exists.elim (h i)
  intro j h
  simpa [<-h] using congr_fun (congr_arg Hom.toFun h') j

end IndexCategory

end CategoryTheory

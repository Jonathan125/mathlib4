import Mathlib.Data.Nat.Basic
import Mathlib.Order.Basic
import Mathlib.CategoryTheory.Iso


namespace CategoryTheory

def IndexCategory : Type :=
  ℕ

namespace IndexCategory

def mk (n : ℕ) : IndexCategory :=
  n

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

protected def rec {F : IndexCategory → Sort*} (h : ∀ n : ℕ, F (mk n)) : ∀ n, F n :=
  (h <| len ·)

attribute [irreducible] IndexCategory.mk
attribute [irreducible] IndexCategory.len

protected def recOn (n : IndexCategory) {F : IndexCategory → Sort*} (h : ∀ n : ℕ, F (mk n)) : F n :=
  IndexCategory.rec h n

protected theorem rec_heq {F : IndexCategory → Sort*} (h : ∀ n : ℕ, F (mk n)) :
    ∀ n, IndexCategory.rec h n ≍ h n.len :=
  IndexCategory.rec <| fun n ↦ by simp [IndexCategory.rec]

protected theorem recOn_heq (n : IndexCategory) {F : IndexCategory → Sort*}
    (h : ∀ n : ℕ, F (mk n)) : IndexCategory.recOn n h ≍ h n.len :=
  IndexCategory.rec_heq h n

instance sizeOf : SizeOf IndexCategory where
  sizeOf n := n.len

@[simp]
protected theorem sizeOf_eq_len (n : IndexCategory) : SizeOf.sizeOf n = n.len :=
  rfl

protected def add (m n : IndexCategory) : IndexCategory :=
  mk <| m.len + n.len

protected def sub (m n : IndexCategory) : IndexCategory :=
  mk <| m.len - n.len

protected def mul (m n : IndexCategory) : IndexCategory :=
  mk <| m.len * n.len

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

def zero : IndexCategory :=
  mk 0

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

@[cases_eliminator]
protected def cases {F : IndexCategory → Sort*} (zero : F zero) (succ : ∀ n, F (n + one)) :
    ∀ n, F n :=
  IndexCategory.rec <| fun | 0 => zero | n + 1 => mk_succ ▸ succ (mk n)

@[simp]
protected theorem cases_zero {F : IndexCategory → Sort*} (zero : F zero) (succ : ∀ n, F (n + one)) :
    IndexCategory.cases zero succ IndexCategory.zero = zero :=
  heq_iff_eq.mp <| (IndexCategory.rec_heq _ _).trans <| by rw [zero_len]

@[simp]
protected theorem cases_succ {F : IndexCategory → Sort*} (zero : F zero) (succ : ∀ n, F (n + one))
    (n : IndexCategory) : IndexCategory.cases zero succ (n + one) = succ n := by
  apply IndexCategory.recOn n
  intro n
  apply heq_iff_eq.mp
  apply (IndexCategory.rec_heq _ _).trans
  rw [add_len, one_len, len_mk]
  simp

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

@[elab_as_elim]
protected def inductionOn (n : IndexCategory) {F : IndexCategory → Sort*} (zero : F zero)
    (succ : ∀ n, F n → F (n + one)) : F n :=
  IndexCategory.induction zero succ n

@[elab_as_elim]
protected def strongRecAux {F : IndexCategory → Sort*}
    (succ : ∀ n : IndexCategory, (∀ m, m.len < n.len → F m) → F n) :
    ∀ n m : IndexCategory, m.len ≤ n.len → F m := by
  apply IndexCategory.rec
  intro n
  induction n with
  | zero =>
    intro m hm
    simp at hm
    apply succ
    intro _ h
    simp [hm] at h
  | succ n ih =>
    apply IndexCategory.rec
    intro m hm
    if h : m < n + 1 then
      apply ih _ (len_mk _ ▸ len_mk _ ▸ Nat.le_of_lt_succ h)
    else
      apply succ _
      intro _ hm'
      apply ih
      apply Nat.le_of_lt_succ
      apply Nat.lt_of_lt_of_le hm'
      simp at hm
      simp
      exact hm

@[elab_as_elim]
protected def strongRec {F : IndexCategory → Sort*}
    (succ : ∀ n : IndexCategory, (∀ m, m.len < n.len → F m) → F n) : ∀ n, F n :=
  fun n ↦ IndexCategory.strongRecAux succ n n (Nat.le_refl _)

@[elab_as_elim]
protected def strong_induction {F : IndexCategory → Sort*} (zero : F zero)
    (succ : ∀ n, (∀ m, m.len ≤ n.len → F m) → F (n + one)) : ∀ n, F n := by
  apply IndexCategory.strongRec
  intro n
  cases n with
  | zero =>
    intro _
    exact zero
  | succ n =>
    intro hlt
    apply succ
    intro m hm
    apply hlt
    simp
    exact Nat.lt_succ_of_le hm


protected def Hom (m n : IndexCategory) : Type :=
  Fin m.len → Fin n.len

namespace Hom

def mk {m n : IndexCategory} (f : Fin m.len → Fin n.len) : IndexCategory.Hom m n :=
  f

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

@[simp]
def id (n : IndexCategory) : IndexCategory.Hom n n :=
  mk (·)

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

def fin_succ_first (n : IndexCategory) : Fin (n + one).len :=
  ⟨0, by simp⟩

def fin_succ_last (n : IndexCategory) : Fin (n + one).len :=
  ⟨n.len, by simp⟩

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

def elim_zero (i : Fin zero.len) {α : Sort*} : α :=
  Fin.elim0 <| Fin.cast (len_mk 0) i

theorem fin_one_ext (i j : Fin one.len) : i = j :=
  (congr_arg Fin one_len.symm ▸ Fin.subsingleton_one).elim i j

def zero_to (n : IndexCategory) : zero ⟶ n :=
  Hom.mk <| fun i ↦ elim_zero i

theorem zero_to_ext {n : IndexCategory} (f g : zero ⟶ n) : f = g :=
  Hom.ext _ _ <| funext fun i ↦ elim_zero i

theorem eq_zero_to_ext {m n : IndexCategory} (h : m = zero) (f g : m ⟶ n) : f = g :=
  by subst h ; exact zero_to_ext f g

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

@[inline]
abbrev to_one (n : IndexCategory) : n ⟶ one :=
  const n one fin_one

theorem to_one_ext {n : IndexCategory} (f g : n ⟶ one) : f = g :=
  Hom.ext _ _ (funext fun _ ↦ fin_one_ext _ _)

theorem to_one_one_id : to_one one = 𝟙 one :=
  to_one_ext _ _

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

def eqIso {m n : IndexCategory} (h : m = n) : m ≅ n where
  hom := eqHom h
  inv := eqHom h.symm

def commIso {m n : IndexCategory} : m + n ≅ n + m :=
  eqIso (IndexCategory.add_comm m n)

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

end IndexCategory

end CategoryTheory

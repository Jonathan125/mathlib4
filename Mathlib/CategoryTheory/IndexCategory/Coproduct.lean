import Mathlib.CategoryTheory.IndexCategory.Defs


namespace CategoryTheory

namespace IndexCategory

section BinaryCoproducts

def ι₁ {m n : IndexCategory} : m ⟶ m + n :=
  Hom.mk (Fin.cast add_len.symm ∘ Fin.castAdd n.len)

def ι₂ {m n : IndexCategory} : n ⟶ m + n :=
  Hom.mk (Fin.cast add_len.symm ∘ Fin.natAdd m.len)

@[simp]
theorem ι₁_toFun_apply {m n : IndexCategory} (i : Fin m.len) :
  Hom.toFun (@ι₁ m n) i = (Fin.cast add_len.symm ∘ Fin.castAdd n.len) i := Hom.toFun_mk_apply _ _

@[simp]
theorem ι₂_toFun_apply {m n : IndexCategory} (i : Fin n.len) :
  Hom.toFun (@ι₂ m n) i = (Fin.cast add_len.symm ∘ Fin.natAdd m.len) i := Hom.toFun_mk_apply _ _

@[reassoc (attr := simp)]
lemma ι₁_assoc_inv {m n k : IndexCategory} : @ι₁ m (n + k) ≫ assocIso.inv = ι₁ ≫ ι₁ :=
  by ext i ; simp

@[reassoc (attr := simp)]
lemma ι₁_ι₁_assoc_hom {m n k : IndexCategory} : ι₁ ≫ @ι₁ (m + n) k ≫ assocIso.hom = ι₁ :=
  by ext i ; simp

@[reassoc (attr := simp)]
lemma ι₂_assoc_hom {m n k : IndexCategory} : @ι₂ (m + n) k ≫ assocIso.hom = ι₂ ≫ ι₂ :=
  by ext i ; simp [Nat.add_assoc]

@[reassoc (attr := simp)]
lemma ι₂_ι₂_assoc_inv {m n k : IndexCategory} : ι₂ ≫ @ι₂ m (n + k) ≫ assocIso.inv = ι₂ :=
  by ext i ; simp [Nat.add_assoc]

@[reassoc (attr := simp)]
lemma ι₁_ι₂_assoc_inv {m n k : IndexCategory} : ι₁ ≫ @ι₂ m (n + k) ≫ assocIso.inv = ι₂ ≫ ι₁ :=
  by ext i ; simp

@[reassoc (attr := simp)]
lemma ι₂_ι₁_assoc_hom {m n k : IndexCategory} : ι₂ ≫ @ι₁ (m + n) k ≫ assocIso.hom = ι₁ ≫ ι₂ :=
  by ext i ; simp

def cast_left {m n : IndexCategory} (i : Fin (m + n).len) (h : i.val < m.len) : Fin m.len :=
  ⟨i.val, h⟩

def cast_right {m n : IndexCategory} (i : Fin (m + n).len) (h : ¬ i.val < m.len) : Fin n.len :=
  ⟨i.val - m.len, (Nat.sub_lt_iff_lt_add' (Nat.le_of_not_lt h)).mpr (i.isLt.trans_eq add_len)⟩

@[simp]
theorem cast_left_val {m n : IndexCategory} (i : Fin (m + n).len) (h : i.val < m.len) :
  (cast_left i h).val = i.val := rfl

@[simp]
theorem cast_right_val {m n : IndexCategory} (i : Fin (m + n).len) (h : ¬ i.val < m.len) :
  (cast_right i h).val = i.val - m.len := rfl

def match_hom {m n k : IndexCategory} (f : m ⟶ k) (g : n ⟶ k) : m + n ⟶ k :=
  Hom.mk (fun i ↦ if h : i.val < m.len then f.toFun (cast_left i h) else g.toFun (cast_right i h))

scoped notation:1050 "[" f ", " g "]" => match_hom f g

@[simp]
theorem match_hom_apply_val {m n k : IndexCategory} (f : m ⟶ k) (g : n ⟶ k) (i : Fin (m + n).len) :
    (Hom.toFun [f, g] i).val = if h : i.val < m.len
    then (f.toFun (cast_left i h)).val else (g.toFun (cast_right i h)).val
  := by
    unfold match_hom
    if h : i.val < m.len then simp [h] else simp [h]

@[simp]
theorem match_hom_apply_left {m n k : IndexCategory} {f : m ⟶ k} {g : n ⟶ k}
  {i : Fin (m + n).len} (h : i.val < m.len) : Hom.toFun [f, g] i = f.toFun (cast_left i h) := by
    unfold match_hom
    simp [h]

@[simp]
theorem match_hom_apply_right {m n k : IndexCategory} {f : m ⟶ k} {g : n ⟶ k}
  {i : Fin (m + n).len} (h : ¬ i.val < m.len) : Hom.toFun [f, g] i = g.toFun (cast_right i h) := by
    unfold match_hom
    simp [h]

@[reassoc (attr := simp)]
theorem ι₁_comp_match {m n k : IndexCategory} (f : m ⟶ k) (g : n ⟶ k) : ι₁ ≫ [f, g] = f :=
  by ext i ; simp ; rfl

@[reassoc (attr := simp)]
theorem ι₂_comp_match {m n k : IndexCategory} (f : m ⟶ k) (g : n ⟶ k) : ι₂ ≫ [f, g] = g :=
  by ext i ; simp ; apply congr_toFun_apply_val ; simp

theorem match_uniq {m n k : IndexCategory} {f : m ⟶ k} {g : n ⟶ k} {h : m + n ⟶ k} :
    ι₁ ≫ h = f → ι₂ ≫ h = g → h = [f, g] := by
  intro h₁ h₂
  ext i
  if hi : i.val < m.len then
    simp [hi, <-h₁]
    rfl
  else
    simp [hi, <-h₂]
    apply congr_toFun_apply_val
    simp [Nat.le_of_not_lt hi]

@[reassoc]
lemma match_comp_hom {m n k l : IndexCategory} (f : m ⟶ k) (g : n ⟶ k) (h : k ⟶ l) :
    [f, g] ≫ h = [f ≫ h, g ≫ h] := match_uniq (by simp) (by simp)

theorem match_ext {m n k : IndexCategory} {f g : m + n ⟶ k} :
    ι₁ ≫ f = ι₁ ≫ g → ι₂ ≫ f = ι₂ ≫ g → f = g :=
  fun h₁ h₂ ↦ (match_uniq rfl rfl).trans <| (congr_arg₂ _ h₁ h₂).trans (match_uniq rfl rfl).symm

@[reducible]
def sum_hom {m n k l : IndexCategory} (f : m ⟶ k) (g : n ⟶ l) : m + n ⟶ k + l :=
  [f ≫ ι₁, g ≫ ι₂]

scoped infixl:65 (priority := high) " ++ " => sum_hom

@[simp]
lemma id_sum_id (m n : IndexCategory) : 𝟙 m ++ 𝟙 n = 𝟙 (m + n) :=
  match_ext (by simp) (by simp)

@[simp]
lemma eqHom_sum_id {m n : IndexCategory} (h : m = n) (k : IndexCategory) :
    eqHom h ++ 𝟙 k = eqHom (congr_arg (· + k) h) :=
  by subst h ; exact id_sum_id m k

@[simp]
lemma id_sum_eqHom (m : IndexCategory) {n k : IndexCategory} (h : n = k) :
    𝟙 m ++ eqHom h = eqHom (congr_arg (m + ·) h) :=
  by subst h ; exact id_sum_id m n

@[reassoc]
lemma comp_sum_id {m n k l : IndexCategory} (f : m ⟶ n) (g : n ⟶ k) :
    f ≫ g ++ 𝟙 l = (f ++ 𝟙 l) ≫ (g ++ 𝟙 l) := match_ext (by simp) (by simp)

@[reassoc]
lemma id_sum_comp {m n k l : IndexCategory} (f : n ⟶ k) (g : k ⟶ l) :
  𝟙 m ++ f ≫ g = (𝟙 m ++ f) ≫ (𝟙 m ++ g) := match_ext (by simp) (by simp)

@[reassoc (attr := simp)]
lemma sum_comp_sum {m₁ n₁ k₁ m₂ n₂ k₂ : IndexCategory} (f₁ : m₁ ⟶ n₁) (g₁ : n₁ ⟶ k₁)
    (f₂ : m₂ ⟶ n₂) (g₂ : n₂ ⟶ k₂) : (f₁ ++ f₂) ≫ (g₁ ++ g₂) = f₁ ≫ g₁ ++ f₂ ≫ g₂ :=
  match_ext (by simp) (by simp)

@[reassoc]
lemma assoc_sum_sum_nat {m₁ n₁ k₁ m₂ n₂ k₂ : IndexCategory} (f : m₁ ⟶ m₂) (g : n₁ ⟶ n₂)
  (h : k₁ ⟶ k₂) : assocIso.inv ≫ (f ++ g ++ h) = (f ++ (g ++ h)) ≫ assocIso.inv :=
    match_ext (by simp) <| match_ext (by simp) (by simp)

-- @[reassoc (attr := simp)]
-- lemma eqHom_comp_sum_left {m n k l : IndexCategory} (h : m + l = n + l) (f : n ⟶ k) (g : l ⟶ l) :
--     eqHom h ≫ (f ++ g) = eqHom (right_add_injective l h) ≫ f ++ g := by
--   obtain rfl : m = n := right_add_injective l h
--   simp

-- @[reassoc (attr := simp)]
-- lemma eqHom_comp_sum_right {m n k l : IndexCategory} (h : m + n = m + k) (f : m ⟶ m)
--(g : k ⟶ l) :
--     eqHom h ≫ (f ++ g) = f ++ eqHom (left_add_injective m h) ≫ g := by
--   obtain rfl : n = k := left_add_injective m h
--   simp

end BinaryCoproducts


section FiniteCoproducts

def sum {n : IndexCategory} (ms : Fin n.len → IndexCategory) : IndexCategory := by
  cases n with
  | zero => exact zero
  | succ n => exact sum (ms ∘ ι₁.toFun) + ms n.fin_succ_last

@[simp]
lemma sum_zero (ms : Fin zero.len → IndexCategory) : sum ms = zero :=
  by unfold sum ; simp

@[simp]
lemma sum_succ {n : IndexCategory} (ms : Fin (n + one).len → IndexCategory) :
    sum ms = sum (ms ∘ ι₁.toFun) + ms n.fin_succ_last :=
  by rw [sum] ; simp

def ι {n : IndexCategory} (ms : Fin n.len → IndexCategory) (i : Fin n.len) : ms i ⟶ sum ms := by
  cases n with
  | zero => exact elim_zero i
  | succ n =>
    exact if h : i.val < n.len
    then eqHom (by simp) ≫ ι (ms ∘ ι₁.toFun) ⟨i.val, h⟩ ≫ ι₁ ≫ eqHom (sum_succ _).symm
    else eqHom (congr_arg _ (eq_last_of_not_lt h)) ≫ ι₂ ≫ eqHom (sum_succ _).symm

def match_homs {n : IndexCategory} {ms : Fin n.len → IndexCategory} {k : IndexCategory}
    (fs : ∀ i : Fin n.len, ms i ⟶ k) : sum ms ⟶ k := by
  cases n with
  | zero => exact eqHom (sum_zero ms) ≫ zero_to k
  | succ n => exact eqHom (sum_succ _) ≫
    [match_homs (fun i ↦ fs (ι₁.toFun i)), fs n.fin_succ_last]

@[reassoc (attr := simp)]
lemma ι_comp_match_homs {n : IndexCategory} {ms : Fin n.len → IndexCategory} {k : IndexCategory}
    (fs : ∀ i : Fin n.len, ms i ⟶ k) (i : Fin n.len) :
    ι ms i ≫ match_homs fs = fs i := by
  induction n with
  | zero => exact elim_zero i
  | succ n ih =>
    unfold match_homs ι
    if h : i.val < n.len then
      simp [h]
      rw [@ih (ms ∘ ι₁.toFun) (fun i ↦ fs (ι₁.toFun i)) ⟨i.val, h⟩]
      simp [ι₁]
    else
      simp [h]
      obtain rfl : i = n.fin_succ_last := eq_last_of_not_lt h
      exact Category.id_comp _

lemma match_homs_uniq {n : IndexCategory} {ms : Fin n.len → IndexCategory} {k : IndexCategory}
    (fs : ∀ i : Fin n.len, ms i ⟶ k) (h : sum ms ⟶ k) :
    (∀ i : Fin n.len, ι ms i ≫ h = fs i) → h = match_homs fs := by
  induction n with
  | zero =>
    intro hi
    apply eq_of_eqHom_comp_eq (sum_zero _).symm
    exact zero_to_ext _ _
  | succ n ih =>
    intro hi
    apply eq_of_eqHom_comp_eq (sum_succ _).symm
    apply match_ext
    · unfold match_homs
      simp
      apply ih
      intro i
      rw [<-hi]
      nth_rewrite 2 [ι]
      simp [ι₁]
    · unfold match_homs
      simp
      rw [<-hi, ι]
      simp

lemma match_homs_comp_hom {n : IndexCategory} {ms : Fin n.len → IndexCategory} {k l : IndexCategory}
    (fs : ∀ i : Fin n.len, ms i ⟶ k) (g : k ⟶ l) :
    match_homs fs ≫ g = match_homs (fun i ↦ fs i ≫ g) :=
  match_homs_uniq _ _ (fun _ ↦ by simp)

lemma match_homs_ext {n : IndexCategory} {ms : Fin n.len → IndexCategory} {k : IndexCategory}
    {f g : sum ms ⟶ k} : (∀ i : Fin n.len, ι ms i ≫ f = ι ms i ≫ g) → f = g :=
  fun h ↦ (match_homs_uniq _ _ (fun _ ↦ rfl)).trans <|
    (congr_arg _ (funext h)).trans (match_homs_uniq _ _ (fun _ ↦ rfl)).symm

@[reducible]
def sum_homs {n : IndexCategory} {ms ks : Fin n.len → IndexCategory}
    (fs : ∀ i : Fin n.len, ms i ⟶ ks i) : sum ms ⟶ sum ks :=
  match_homs (fun i ↦ fs i ≫ ι ks i)

@[simp]
lemma sum_ids {n : IndexCategory} (ms : Fin n.len → IndexCategory) :
    sum_homs (fun i ↦ 𝟙 (ms i)) = 𝟙 (sum ms) :=
  match_homs_ext (fun _ ↦ by simp)

@[simp]
lemma sum_eqHoms {n : IndexCategory} {ms ks : Fin n.len → IndexCategory}
    (h : ∀ i : Fin n.len, ms i = ks i) :
    sum_homs (fun i ↦ eqHom (h i)) = eqHom (congr_arg sum (funext h))
  := by
    obtain rfl : ms = ks := funext h
    exact sum_ids ms

def sumLT {n : IndexCategory} (ms : Fin n.len → IndexCategory) (i : Fin n.len) : IndexCategory := by
  cases n with
  | zero => exact zero
  | succ n =>
    let ms' := ms ∘ ι₁.toFun
    exact if h : i.val < n.len then sumLT ms' ⟨i.val, h⟩ else sum ms'

def sumLE {n : IndexCategory} (ms : Fin n.len → IndexCategory) (i : Fin n.len) : IndexCategory :=
  sumLT ms i + ms i

lemma sumLE_le_sum {n : IndexCategory} (ms : Fin n.len → IndexCategory) (i : Fin n.len) :
    (sumLE ms i).len ≤ (sum ms).len := by
  induction n with
  | zero => exact elim_zero i
  | succ n ih =>
    if h : i.val < n.len then
      unfold sumLE sumLT
      simp [h]
      specialize ih (ms ∘ Hom.toFun ι₁) ⟨i.val, h⟩
      simp [sumLE] at ih
      apply Nat.le_trans ih
      exact Nat.le_add_right _ _
    else
      apply Nat.le_of_eq
      obtain rfl : i = n.fin_succ_last := eq_last_of_not_lt h
      rw [sumLE, sumLT]
      simp

lemma sumLT_add_lt_sum {n : IndexCategory} {ms : Fin n.len → IndexCategory} {i : Fin n.len}
    (j : Fin (ms i).len) : (sumLT ms i).len + j.val < (sum ms).len :=
  (Nat.add_lt_add_left j.isLt _).trans_le <| add_len.symm.le.trans <| sumLE_le_sum ms i

lemma ι_hom_toFun {n : IndexCategory} (ms : Fin n.len → IndexCategory) (i : Fin n.len) :
    (ι ms i).toFun = fun j ↦ ⟨(sumLT ms i).len + j.val, sumLT_add_lt_sum j⟩
  := by
    induction n with
    | zero => exact elim_zero i
    | succ n ih =>
      if h : i.val < n.len then
        ext j
        simp
        rw [ι, sumLT]
        simp [h]
        specialize ih (ms ∘ ι₁.toFun) ⟨i, h⟩
        replace ih := Fin.val_eq_of_eq (congr_fun ih (Fin.cast (by simp) j))
        simp at ih
        exact ih
      else
        ext j
        simp
        rw [ι, sumLT]
        simp [h]

@[simp]
lemma ι_app_val {n : IndexCategory} {ms : Fin n.len → IndexCategory} {i : Fin n.len}
    (j : Fin (ms i).len) : ((ι ms i).toFun j).val = (sumLT ms i).len + j.val
  :=
    congr_arg Fin.val (congr_fun (ι_hom_toFun ms i) j)

end FiniteCoproducts

end IndexCategory

end CategoryTheory

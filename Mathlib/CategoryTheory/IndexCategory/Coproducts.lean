import Mathlib.CategoryTheory.IndexCategory.Basic


namespace CategoryTheory

namespace IndexCategory

open 𝔽


section BinaryCoproducts

def ι₁ {m : 𝔽} (n : 𝔽) : m ⟶ m + n := Fin.castAdd n

@[simp]
lemma ι₁_val {m n : 𝔽} (i : m.fin) : (ι₁ n i).val = i.val := rfl

def ι₂ (m : 𝔽) {n : 𝔽} : n ⟶ m + n := Fin.natAdd m

@[simp]
lemma ι₂_val {m n : 𝔽} (i : n.fin) : (ι₂ m i).val = m + i.val := rfl

@[reassoc (attr := simp)]
lemma ι₁_comp_ι₁ (m n k : 𝔽) :
    @ι₁ m (n + k) ≫ assocIso.inv = ι₁ n ≫ ι₁ k
  :=
    funext fun _ ↦ Fin.eq_of_val_eq rfl

@[reassoc (attr := simp)]
lemma ι₂_comp_ι₂ (m n k : 𝔽) :
    @ι₂ (m + n) k ≫ assocIso.hom = ι₂ n ≫ ι₂ m
  :=
    funext fun i ↦ Fin.eq_of_val_eq (by simp [Nat.add_assoc])

def cast_left {m n : 𝔽} (i : (m + n).fin) (h : i.val < m) : m.fin :=
  ⟨i.val, h⟩

@[simp]
lemma cast_left_val {m n : 𝔽} (i : (m + n).fin) (h : i.val < m) :
  (cast_left i h).val = i.val := rfl

def cast_right {m n : 𝔽} (i : (m + n).fin) (h : ¬ i.val < m) : n.fin :=
  Fin.subNat m (commIso.hom i) (Nat.le_of_not_lt h)

@[simp]
lemma cast_right_val {m n : 𝔽} (i : (m + n).fin) (h : ¬ i.val < m) :
  (cast_right i h).val = i.val - m := rfl

def match_hom {m n k : 𝔽} (f : m ⟶ k) (g : n ⟶ k) : m + n ⟶ k :=
  fun i ↦ if h : i.val < m then f (cast_left i h) else g (cast_right i h)

scoped notation:1050 "[" f ", " g "]" => match_hom f g

@[simp]
lemma match_hom_left {m n k : 𝔽} {f : m ⟶ k} {g : n ⟶ k}
  {i : (m + n).fin} (h : i.val < m) : [f, g] i = f (cast_left i h) :=
    dite_cond_eq_true (eq_true_intro h)

@[simp]
lemma match_hom_right {m n k : 𝔽} {f : m ⟶ k} {g : n ⟶ k}
  {i : (m + n).fin} (h : ¬ i.val < m) : [f, g] i = g (cast_right i h) :=
    dite_cond_eq_false (eq_false_intro h)

@[reassoc (attr := simp)]
lemma ι₁_comp_match {m n k : 𝔽} (f : m ⟶ k) (g : n ⟶ k) : ι₁ n ≫ [f, g] = f :=
  funext (fun _ ↦ by simp ; rfl)

@[reassoc (attr := simp)]
lemma ι₂_comp_match {m n k : 𝔽} (f : m ⟶ k) (g : n ⟶ k) : ι₂ m ≫ [f, g] = g :=
  funext (fun _ ↦ by simp ; exact hom_app_ext _ _ _ (by simp))

lemma match_uniq {m n k : 𝔽} {f : m ⟶ k} {g : n ⟶ k} {h : m + n ⟶ k} :
    ι₁ n ≫ h = f → ι₂ m ≫ h = g → h = [f, g]
  := by
    intro h₁ h₂
    funext i
    unfold match_hom
    if hi : i.val < m then
      simp [hi, <-h₁]
      rfl
    else
      simp [hi, <-h₂]
      apply hom_app_ext
      simp
      exact (Nat.add_sub_cancel' (Nat.le_of_not_lt hi)).symm

@[reassoc]
lemma match_comp_hom {m n k l : 𝔽} (f : m ⟶ k) (g : n ⟶ k) (h : k ⟶ l) :
    [f, g] ≫ h = [f ≫ h, g ≫ h]
  := match_uniq (by simp) (by simp)

lemma match_ext {m n k : 𝔽} {f g : m + n ⟶ k} :
    ι₁ n ≫ f = ι₁ n ≫ g → ι₂ m ≫ f = ι₂ m ≫ g → f = g
  :=
    fun h₁ h₂ ↦ (match_uniq rfl rfl).trans ((congr_arg₂ _ h₁ h₂).trans (match_uniq rfl rfl).symm)

@[reducible]
def sum_hom {m n k l : 𝔽} (f : m ⟶ k) (g : n ⟶ l) : m + n ⟶ k + l :=
  [f ≫ ι₁ l, g ≫ ι₂ k]

scoped infixl:65 (priority := high) " ++ " => sum_hom

@[simp]
lemma id_sum_id (m n : 𝔽) : 𝟙 m ++ 𝟙 n = 𝟙 (m + n) := match_ext (by simp) (by simp)

@[simp]
lemma eqHom_sum_id {m n : 𝔽} (h : m = n) (k : 𝔽) :
    eqHom h ++ 𝟙 k = eqHom (congr_arg (· + k) h) := by subst h ; exact id_sum_id m k

@[simp]
lemma id_sum_eqHom (m : 𝔽) {n k : 𝔽} (h : n = k) :
    𝟙 m ++ eqHom h = eqHom (congr_arg (m + ·) h) := by subst h ; exact id_sum_id m n

@[reassoc]
lemma comp_sum_id {m n k l : 𝔽} (f : m ⟶ n) (g : n ⟶ k) :
  f ≫ g ++ 𝟙 l = (f ++ 𝟙 l) ≫ (g ++ 𝟙 l) := match_ext (by simp) (by simp)

@[reassoc]
lemma id_sum_comp {m n k l : 𝔽} (f : n ⟶ k) (g : k ⟶ l) :
  𝟙 m ++ f ≫ g = (𝟙 m ++ f) ≫ (𝟙 m ++ g) := match_ext (by simp) (by simp)

@[reassoc (attr := simp)]
lemma sum_comp_sum {m₁ n₁ k₁ m₂ n₂ k₂ : 𝔽} (f₁ : m₁ ⟶ n₁) (g₁ : n₁ ⟶ k₁)
  (f₂ : m₂ ⟶ n₂) (g₂ : n₂ ⟶ k₂) :
    (f₁ ++ f₂) ≫ (g₁ ++ g₂) = f₁ ≫ g₁ ++ f₂ ≫ g₂ := match_ext (by simp) (by simp)

@[reassoc]
lemma sum_sum_conj_assoc {m₁ n₁ k₁ m₂ n₂ k₂ : 𝔽} (f : m₁ ⟶ m₂) (g : n₁ ⟶ n₂)
  (h : k₁ ⟶ k₂) : f ++ g ++ h = assocIso.hom ≫ (f ++ (g ++ h)) ≫ assocIso.inv := by
    apply match_ext
    · simp [-eqHomIso_hom]
      apply match_ext
      · simp [<-ι₁_comp_ι₁, <-ι₁_comp_ι₁_assoc]
      · simp [-eqHomIso_hom]
        have h₁ : (@ι₂ m₁ n₁ ≫ ι₁ k₁) ≫ assocIso.hom = ι₁ k₁ ≫ ι₂ m₁ := rfl
        simp only [<-Category.assoc, h₁]
        simp
        rfl
    · simp [-eqHomIso_hom, ι₂_comp_ι₂_assoc]
      simp [<-ι₂_comp_ι₂_assoc]

@[reassoc (attr := simp)]
lemma eqHom_succ_comp_sum {m n k : 𝔽} (h : m + 1 = n + 1) (f : n ⟶ k) :
    eqHom h ≫ (f ++ 𝟙 1) = eqHom (Nat.add_right_cancel h) ≫ f ++ 𝟙 1
  := by
    obtain rfl : m = n := Nat.add_right_cancel h
    rfl

@[reassoc (attr := simp)]
lemma ι₁_succ_succ_comp_match {m n k : 𝔽} (f : m + 1 ⟶ n) (g : 1 ⟶ k) :
    ι₁ 2 ≫ (f ++ g : _ ⟶ n + k) = ι₁ 1 ≫ f ≫ ι₁ k
  :=
    ((Category.comp_id _).symm.trans (ι₁_comp_ι₁ m 1 1) =≫ _).trans (by simp)

@[reassoc (attr := simp)]
lemma ι₂_succ_succ_comp_match {m n k : 𝔽} (f : m + 1 ⟶ n) (g : 1 ⟶ k) :
    ι₂ 1 ≫ ι₂ m ≫ (f ++ g : _ ⟶ n + k) = g ≫ ι₂ n
  :=
    ((_ ≫= Category.id_comp _).symm.trans (ι₂_comp_ι₂_assoc m 1 1 _)).symm.trans (by simp)

end BinaryCoproducts


section FiniteCoproducts

def sum {n : 𝔽} (ms : n.fin → 𝔽) : 𝔽 :=
  match n with
  | 0 => 0
  | n + 1 => sum (ms ∘ castSucc) + ms n.last

def ι {n : 𝔽} (ms : n.fin → 𝔽) (i : n.fin) : ms i ⟶ sum ms :=
  match n with
  | 0 => i.elim0
  | n + 1 =>
    if h : i.val < n
    then ι (ms ∘ castSucc) ⟨i, h⟩ ≫ ι₁ (ms n.last)
    else eqHom (congr_arg ms (Fin.eq_last_of_not_lt h)) ≫ ι₂ (sum (ms ∘ castSucc))

def match_homs {n : 𝔽} {ms : n.fin → 𝔽} {k : 𝔽} (fs : (i : n.fin) → ms i ⟶ k) :
    sum ms ⟶ k
  :=
    match n with
    | 0 => Fin.elim0
    | n + 1 => [match_homs (fun i ↦ fs (castSucc i)), fs n.last]

@[reassoc (attr := simp)]
lemma ι_comp_match_homs {n : 𝔽} (ms : n.fin → 𝔽) {k : 𝔽}
  (fs : (i : n.fin) → ms i ⟶ k) (i : n.fin) :
    ι ms i ≫ match_homs fs = fs i
  := by
    induction n with
    | zero => exact i.elim0
    | succ n ih =>
      unfold match_homs ι
      if h : i.val < n then
        simp [h]
        exact ih _ _ _
      else
        simp [h]
        obtain rfl : i = last n := Fin.eq_last_of_not_lt h
        rfl

lemma match_homs_uniq {n : 𝔽} {ms : n.fin → 𝔽} {k : 𝔽}
  (fs : (i : n.fin) → ms i ⟶ k) (h : sum ms ⟶ k) :
    (∀ i : n.fin, ι ms i ≫ h = fs i) → h = match_homs fs
  := by
    induction n with
    | zero =>
      intro hi
      exact zero_ext _ _
    | succ n ih =>
      intro hi
      apply match_ext
      · unfold match_homs
        simp
        apply ih
        intro i
        rw [<-hi, <-Category.assoc]
        apply eq_whisker
        simp [ι]
      · unfold match_homs
        simp
        specialize hi (last n)
        simp [ι] at hi
        exact hi

lemma match_homs_comp_hom {n : 𝔽} (ms : n.fin → 𝔽) {k l : 𝔽}
  (fs : (i : n.fin) → ms i ⟶ k) (g : k ⟶ l) :
    match_homs fs ≫ g = match_homs (fun i ↦ fs i ≫ g)
  := match_homs_uniq _ _ (fun _ ↦ by simp)

lemma match_homs_ext {n : 𝔽} {ms : n.fin → 𝔽} {k : 𝔽} {f g : sum ms ⟶ k} :
  (∀ i : n.fin, ι ms i ≫ f = ι ms i ≫ g) → f = g
  := by
    intro h
    calc
      _ = match_homs (fun i ↦ ι ms i ≫ f) := match_homs_uniq _ _ (fun _ ↦ rfl)
      _ = match_homs (fun i ↦ ι ms i ≫ g) := congr_arg _ (funext h)
      _ = _ := (match_homs_uniq _ _ (fun _ ↦ rfl)).symm

@[reducible]
def sum_homs {n : 𝔽} {ms : n.fin → 𝔽} {ks : n.fin → 𝔽} (fs : (i : n.fin) → ms i ⟶ ks i) :
  sum ms ⟶ sum ks := match_homs (fun i ↦ fs i ≫ ι ks i)

@[simp]
lemma sum_ids {n : 𝔽} (ms : n.fin → 𝔽) : sum_homs (fun i ↦ 𝟙 (ms i)) = 𝟙 (sum ms) :=
  match_homs_ext (fun _ ↦ by simp)

@[simp]
lemma sum_eqHoms {n : 𝔽} {ms : n.fin → 𝔽} {ks : n.fin → 𝔽} (h : ∀ i : n.fin, ms i = ks i) :
    sum_homs (fun i ↦ eqHom (h i)) = eqHom (congr_arg sum (funext h))
  := by
    obtain rfl : ms = ks := funext h
    exact sum_ids ms

def sumLT {n : 𝔽} (ms : n.fin → 𝔽) (i : n.fin) : 𝔽 :=
  match n with
  | 0 => 0
  | n + 1 =>
    let ms' := ms ∘ castSucc
    if h : i.val < n then sumLT ms' ⟨i.val, h⟩ else sum ms'

def sumLE {n : 𝔽} (ms : n.fin → 𝔽) (i : n.fin) : 𝔽 :=
  sumLT ms i + ms i

lemma sumLE_le_sum {n : 𝔽} (ms : n.fin → 𝔽) (i : n.fin) : sumLE ms i ≤ sum ms := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    if h : i.val < n then
      unfold sumLE sumLT
      simp [h]
      apply Nat.le_trans (ih _ ⟨i.val, h⟩)
      exact Nat.le_add_right _ _
    else
      apply Nat.le_of_eq
      obtain rfl : i = last n := Fin.eq_last_of_not_lt h
      simp [sumLE, sumLT]
      rfl

lemma sumLT_add_lt_sum {n : 𝔽} {ms : n.fin → 𝔽} {i : n.fin} (j : (ms i).fin) :
    sumLT ms i + j.val < sum ms
  :=
    Nat.lt_of_lt_of_le (Nat.add_lt_add_left j.isLt _) (sumLE_le_sum ms i)

lemma ι_hom_eq {n : 𝔽} (ms : n.fin → 𝔽) (i : n.fin) :
    ι ms i = fun j ↦ ⟨sumLT ms i + j.val, sumLT_add_lt_sum j⟩
  := by
    induction n with
    | zero => exact i.elim0
    | succ n ih =>
      if h : i.val < n then
        funext j
        apply Fin.eq_of_val_eq
        simp [ι, sumLT, h]
        specialize ih (ms ∘ castSucc) ⟨i, h⟩
        replace ih := Fin.val_eq_of_eq (congr_fun ih j)
        simp at ih
        exact ih
      else
        funext j
        apply Fin.eq_of_val_eq
        simp [ι, sumLT, h]

@[simp]
lemma ι_app_val {n : 𝔽} {ms : n.fin → 𝔽} {i : n.fin} (j : (ms i).fin) :
    (ι ms i j).val = sumLT ms i + j.val
  :=
    congr_arg Fin.val (congr_fun (ι_hom_eq ms i) j)

end FiniteCoproducts

end IndexCategory

end CategoryTheory

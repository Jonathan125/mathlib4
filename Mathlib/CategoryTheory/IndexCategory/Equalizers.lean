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

protected def id_if_eq {m n : IndexCategory} (f g : m ⟶ n) : m ⟶ m + one :=
  Hom.mk <| fun i ↦ if f.toFun i = g.toFun i then ι₁.toFun i else m.fin_succ_last

protected theorem id_if_eq_toFun_apply_agree {m n : IndexCategory} (f g : m ⟶ n)
    (i : Fin m.len) (h : f.toFun i = g.toFun i) : (Equalizers.id_if_eq f g).toFun i = ι₁.toFun i :=
  (Hom.toFun_mk_apply _ _).trans <| by simp [h]

protected theorem id_if_eq_toFun_apply_not_agree {m n : IndexCategory} (f g : m ⟶ n)
    (i : Fin m.len) (h : ¬ f.toFun i = g.toFun i) :
    (Equalizers.id_if_eq f g).toFun i = m.fin_succ_last :=
  (Hom.toFun_mk_apply _ _).trans <| by simp [h]

protected theorem id_if_eq_toFun_apply_val {m n : IndexCategory} (f g : m ⟶ n) (i : Fin m.len) :
    ((Equalizers.id_if_eq f g).toFun i).val
    = if f.toFun i = g.toFun i then i.val else m.len := by
  if h : f.toFun i = g.toFun i then
    simp [Equalizers.id_if_eq_toFun_apply_agree _ _ _ h, h]
  else
    simp [Equalizers.id_if_eq_toFun_apply_not_agree _ _ _ h, h]

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
        ext i
        simp
        if hi : (ι₁ ≫ f).toFun i = (ι₁ ≫ g).toFun i then
          have hi' : f.toFun (Fin.cast succ_len.symm i.castSucc)
            = g.toFun (Fin.cast succ_len.symm i.castSucc) := by simpa using hi
          simp [Equalizers.id_if_eq_toFun_apply_agree _ _ _ hi,
            Equalizers.id_if_eq_toFun_apply_agree _ _ _ hi']
        else
          have hi' : ¬ f.toFun (Fin.cast succ_len.symm i.castSucc)
            = g.toFun (Fin.cast succ_len.symm i.castSucc) := by simpa using hi
          simp [Equalizers.id_if_eq_toFun_apply_not_agree _ _ _ hi,
            Equalizers.id_if_eq_toFun_apply_not_agree _ _ _ hi']
      else
        simp [Equalizers.uneq_succ_not_last_agree h, Equalizers.hom_succ_not_last_agree h]
        rw [<-Category.id_comp (𝟙 one), <-sum_comp_sum, <-Category.assoc, ih]
        ext i
        simp
        if hi : (ι₁ ≫ f).toFun i = (ι₁ ≫ g).toFun i then
          have hi' : f.toFun (Fin.cast succ_len.symm i.castSucc)
            = g.toFun (Fin.cast succ_len.symm i.castSucc) := by simpa using hi
          simp [Equalizers.id_if_eq_toFun_apply_agree _ _ _ hi,
            Equalizers.id_if_eq_toFun_apply_agree _ _ _ hi']
        else
          have hi' : ¬ f.toFun (Fin.cast succ_len.symm i.castSucc)
            = g.toFun (Fin.cast succ_len.symm i.castSucc) := by simpa using hi
          simp [Equalizers.id_if_eq_toFun_apply_not_agree _ _ _ hi,
            Equalizers.id_if_eq_toFun_apply_not_agree _ _ _ hi']
    · apply one_to_ext
      if h : Equalizers.last_agree f g then
        simp [Equalizers.uneq_toFun_apply_val_lt_of_agree _ _ _ h]
        simp [Equalizers.uneq_succ_last_agree h, Equalizers.hom_succ_last_agree h,
          Equalizers.id_if_eq_toFun_apply_val]
        exact h
      else
        simp [Equalizers.uneq_succ_not_last_agree h, Equalizers.hom_succ_not_last_agree h,
          Equalizers.id_if_eq_toFun_apply_val]
        exact h

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

theorem lift_comp_ι₁_eq_post_comp_uneq {m n k : IndexCategory} {f g : m ⟶ n} (h : k ⟶ m)
    (hh : h ≫ f = h ≫ g) : Equalizers.lift hh ≫ ι₁ = h ≫ Equalizers.uneq f g :=
  by ext _ ; simp [Equalizers.lift]

theorem hom_post_comp_uneq_comp_hom_sum_id_iff_hom_comp_lift_comp_hom {m n k : IndexCategory}
    {f g : m ⟶ n} (h : k ⟶ m) (hh : h ≫ f = h ≫ g) {l₁ l₂ : IndexCategory} (u₁ : l₁ ⟶ k)
    (u₂ : Equalizers.obj f g ⟶ l₂) {v : l₁ ⟶ l₂} :
    u₁ ≫ h ≫ Equalizers.uneq f g ≫ (u₂ ++ 𝟙 one) = v ≫ ι₁ ↔ u₁ ≫ Equalizers.lift hh ≫ u₂ = v := by
  have hlt (i : Fin l₁.len) := Equalizers.comp_uneq_lt_of_condition f g h hh (u₁.toFun i)
  simp at hlt
  constructor
  · intro h₁
    ext i
    replace h₁ := Fin.val_eq_of_eq (congr_fun (congr_arg Hom.toFun h₁) i)
    simp [hlt i] at h₁
    rw [<-h₁]
    simp [Equalizers.lift]
    rfl
  · intro h₁
    ext i
    replace h₁ := Fin.val_eq_of_eq (congr_fun (congr_arg Hom.toFun h₁) i)
    simp [hlt i, <-h₁, Equalizers.lift]
    rfl

theorem post_comp_uneq_iff_lift {m n k : IndexCategory} {f g : m ⟶ n} (h : k ⟶ m)
    (hh : h ≫ f = h ≫ g) {u : k ⟶ Equalizers.obj f g} :
    h ≫ Equalizers.uneq f g = u ≫ ι₁ ↔ Equalizers.lift hh = u :=
  by simpa using hom_post_comp_uneq_comp_hom_sum_id_iff_hom_comp_lift_comp_hom h hh (𝟙 _) (𝟙 _)

theorem post_comp_uneq_comp_hom_sum_id_iff_lift_comp_hom {m n k : IndexCategory} {f g : m ⟶ n}
    (h : k ⟶ m) (hh : h ≫ f = h ≫ g) {l : IndexCategory} {u : Equalizers.obj f g ⟶ l}
    {v : k ⟶ l} : h ≫ Equalizers.uneq f g ≫ (u ++ 𝟙 _) = v ≫ ι₁ ↔ Equalizers.lift hh ≫ u = v :=
  by simpa using hom_post_comp_uneq_comp_hom_sum_id_iff_hom_comp_lift_comp_hom h hh (𝟙 _) _

theorem hom_post_comp_uneq_iff_hom_comp_lift {m n k : IndexCategory} {f g : m ⟶ n} (h : k ⟶ m)
    (hh : h ≫ f = h ≫ g) {l : IndexCategory} {u : l ⟶ k} {v : l ⟶ Equalizers.obj f g} :
    u ≫ h ≫ Equalizers.uneq f g = v ≫ ι₁ ↔ u ≫ Equalizers.lift hh = v :=
  by simpa using hom_post_comp_uneq_comp_hom_sum_id_iff_hom_comp_lift_comp_hom h hh _ (𝟙 _)

protected theorem lift_hom_id {m n : IndexCategory} {f g : m ⟶ n} :
    Equalizers.lift (Equalizers.condition f g) = 𝟙 (Equalizers.obj f g) :=
  (post_comp_uneq_iff_lift _ _).mp <|
    (Equalizers.hom_comp_uneq_eq_ι₁ f g).trans (Category.id_comp _).symm


protected theorem fac {m n k : IndexCategory} {f g : m ⟶ n} {h : k ⟶ m} (hh : h ≫ f = h ≫ g) :
    Equalizers.lift hh ≫ Equalizers.hom f g = h :=
  (post_comp_uneq_comp_hom_sum_id_iff_lift_comp_hom _ hh).mp <| by
  ext i ; simp [Equalizers.id_if_eq_toFun_apply_agree _ _ _
    (by simpa using congr_fun (congr_arg Hom.toFun hh) i)]

protected theorem uniq {m n k : IndexCategory} {f g : m ⟶ n} {h : k ⟶ m} (hh : h ≫ f = h ≫ g)
    (s : k ⟶ Equalizers.obj f g) (hs : s ≫ Equalizers.hom f g = h) : s = Equalizers.lift hh :=
  ((s ≫= Equalizers.lift_hom_id).trans (Category.comp_id s)).symm.trans <|
    (hom_post_comp_uneq_iff_hom_comp_lift _ (Equalizers.condition f g)).mp <|
    (Category.assoc _ _ _).symm.trans <| (hs =≫ _).trans (lift_comp_ι₁_eq_post_comp_uneq _ _).symm

end Equalizers

end IndexCategory

end CategoryTheory

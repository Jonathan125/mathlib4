import Mathlib.CategoryTheory.IndexCategory.Coproducts


namespace CategoryTheory

namespace IndexCategory

section Equalizer

open 𝔽 Category Nat

@[inline]
abbrev last_agree {m n : 𝔽} (f g : m + 1 ⟶ n) : Prop := f m.last = g m.last

def obj {m n : 𝔽} (f g : m ⟶ n) : 𝔽 :=
  match m with
  | 0 => 0
  | _ + 1 =>
    let k : 𝔽 := obj (ι₁ 1 ≫ f) (ι₁ 1 ≫ g)
    if last_agree f g then k + 1 else k

section

variable {m n : 𝔽} {f g : m + 1 ⟶ n}

lemma obj_succ_eq (h : last_agree f g) :
    obj f g = obj (ι₁ 1 ≫ f) (ι₁ 1 ≫ g) + 1
  := by
    simp [obj, h]

lemma obj_succ_ne (h : ¬ last_agree f g) :
    obj f g = obj (ι₁ 1 ≫ f) (ι₁ 1 ≫ g)
  := by
    simp [obj, h]

end

def equal {m n : 𝔽} (f g : m ⟶ n) : obj f g ⟶ m :=
  match m with
  | 0 => zero_to 0
  | m + 1 =>
    let k : 𝔽 := obj (ι₁ 1 ≫ f) (ι₁ 1 ≫ g)
    let e : k ⟶ m := equal (ι₁ 1 ≫ f) (ι₁ 1 ≫ g)
    if h : last_agree f g
    then eqHom (obj_succ_eq h) ≫ (e ++ 𝟙 1)
    else eqHom (obj_succ_ne h) ≫ e ≫ ι₁ 1

def uneq {m n : 𝔽} (f g : m ⟶ n) : m ⟶ obj f g + 1 :=
  match m with
  | 0 => zero_to _
  | m + 1 =>
    let k : 𝔽 := obj (ι₁ 1 ≫ f) (ι₁ 1 ≫ g)
    let u : m ⟶ k + 1 := uneq (ι₁ 1 ≫ f) (ι₁ 1 ≫ g)
    if h : last_agree f g
    then [u ≫ (𝟙 k ++ ι₂ _), ι₂ _ ≫ ι₁ 1] ≫ eqHom (congr_arg (· + 1) (obj_succ_eq h).symm)
    else [u, const_hom k.last] ≫ eqHom (congr_arg (· + 1) (obj_succ_ne h).symm)

section

variable {m n : 𝔽} {f g : m + 1 ⟶ n}

lemma equal_succ_eq (h : last_agree f g) :
    equal f g = eqHom (obj_succ_eq h) ≫ (equal (ι₁ 1 ≫ f) (ι₁ 1 ≫ g) ++ 𝟙 1)
  :=
    dite_cond_eq_true (eq_true_intro h)

lemma equal_succ_ne (h : ¬ last_agree f g) :
    equal f g = eqHom (obj_succ_ne h) ≫ equal (ι₁ 1 ≫ f) (ι₁ 1 ≫ g) ≫ ι₁ 1
  :=
    dite_cond_eq_false (eq_false_intro h)

lemma uneq_succ_eq (h : last_agree f g) :
    uneq f g = [uneq (ι₁ 1 ≫ f) (ι₁ 1 ≫ g) ≫ (𝟙 _ ++ ι₂ 1), ι₂ _ ≫ ι₁ 1] ≫
      eqHom (congr_arg (· + 1) (obj_succ_eq h).symm)
  :=
    dite_cond_eq_true (eq_true_intro h)

lemma uneq_succ_ne (h : ¬ last_agree f g) :
    uneq f g = [uneq (ι₁ 1 ≫ f) (ι₁ 1 ≫ g), const_hom (obj (ι₁ 1 ≫ f) (ι₁ 1 ≫ g)).last] ≫
      eqHom (congr_arg (· + 1) (obj_succ_ne h).symm)
  :=
    dite_cond_eq_false (eq_false_intro h)

end

section

variable {m n : 𝔽} (f g : m ⟶ n)

lemma equal_condition : equal f g ≫ f = equal f g ≫ g := by
  induction m with
  | zero => exact zero_ext _ _
  | succ m ih =>
    if h : last_agree f g then
      simp [equal_succ_eq h]
      apply whisker_eq
      apply match_ext
      · simp
        exact ih _ _
      · simp
        funext i
        obtain rfl : i = 0 := Fin.subsingleton_one.elim _ _
        exact h
    else
      simp [equal_succ_ne h]
      apply whisker_eq
      exact ih _ _

variable (i : m.fin)

lemma uneq_lt_of_eq : f i = g i → (uneq f g i).val < obj f g := by
  induction m with
  | zero => exact i.elim0
  | succ m ih =>
    intro he
    if hm : last_agree f g then
      simp [uneq_succ_eq hm, obj_succ_eq hm]
      if hi : i.val < m then
        simp [hi, sum_hom, match_hom]
        rw [dite_cond_eq_true (eq_true_intro (ih _ _ _ he))]
        simp
      else
        simp [hi]
    else
      simp [uneq_succ_ne hm, obj_succ_ne hm]
      have hi : i.val < m := Nat.lt_of_le_of_ne (le_of_lt_succ i.isLt)
        (fun hn ↦ (by obtain rfl : i = last m := Fin.eq_of_val_eq hn ; exact hm he))
      simp [hi]
      exact ih _ _ _ he

end

section

variable {m n : 𝔽} (f g : m ⟶ n)

lemma left_comp_eq : equal f g ≫ uneq f g = ι₁ 1 := by
  induction m with
  | zero => exact zero_ext _ _
  | succ m ih =>
    if hm : last_agree f g then
      rw [equal_succ_eq hm, uneq_succ_eq hm, Category.assoc]
      rw [match_comp_hom_assoc]
      simp
      rw [(Category.assoc _ _ _).symm.trans (ih _ _ =≫ _)]
      simp
      funext i
      apply Fin.eq_of_val_eq
      if hi : i.val < obj (@ι₁ _ 1 ≫ f) (@ι₁ _ 1 ≫ g) then
        simp [hi]
      else
        simp [hi]
        exact Fin.val_eq_of_eq (@Fin.eq_last_of_not_lt _ (Fin.cast (obj_succ_eq hm) i) hi).symm
    else
      rw [equal_succ_ne hm, uneq_succ_ne hm]
      simp
      rw [(Category.assoc _ _ _).symm.trans (ih _ _ =≫ _)]
      rfl

@[simp]
def id_if_eq : m ⟶ m + 1 := fun i ↦ if f i = g i then i.castSucc else m.last

lemma right_comp_eq : uneq f g ≫ (equal f g ++ 𝟙 1) = id_if_eq f g := by
  induction m with
  | zero => exact zero_ext _ _
  | succ m ih =>
    apply @match_ext _ 1
    · if hm : last_agree f g then
        simp [uneq_succ_eq hm, match_comp_hom, equal_succ_eq hm]
        change _ ≫ (equal _ _ ≫ ι₁ 1 ++ 𝟙 _) = _
        rw [comp_sum_id, <-Category.assoc, ih]
        funext i
        apply Fin.eq_of_val_eq
        if h : f (ι₁ 1 i) = g (ι₁ 1 i) then simp [h] else simp [h]
      else
        simp [uneq_succ_ne hm, equal_succ_ne hm]
        rw [comp_sum_id, <-Category.assoc, ih]
        funext i
        apply Fin.eq_of_val_eq
        if h : f (ι₁ 1 i) = g (ι₁ 1 i) then simp [h] else simp [h]
    · apply const_hom_ext
      apply Fin.eq_of_val_eq
      if hm : last_agree f g then
        rw [uneq_succ_eq hm]
        simp [match_hom]
        rw [ite_cond_eq_true _ _ (eq_true_intro (by assumption))]
        rw [equal_succ_eq hm]
        simp
      else
        simp [uneq_succ_ne hm]
        rw [ite_cond_eq_false _ _ (eq_false_intro (by assumption))]
        rfl

variable {k : 𝔽} (h : k ⟶ m)

lemma comp_uneq_lt_of_condition :
    h ≫ f = h ≫ g → ∀ i : k.fin, ((h ≫ uneq f g) i).val < obj f g
  := fun hh _ ↦ uneq_lt_of_eq f g _ (congr_fun hh _)

end

section

variable {m n : 𝔽} {f g : m ⟶ n} {k : 𝔽} (h : k ⟶ m)
variable (hh : h ≫ f = h ≫ g)

def comp_uneq_hom : k ⟶ obj f g :=
  fun i ↦ ⟨((h ≫ uneq f g) i).val, comp_uneq_lt_of_condition _ _ _ hh _⟩

lemma comp_uneq_hom_eq : comp_uneq_hom h hh ≫ ι₁ 1 = h ≫ uneq f g := rfl

lemma hom_comp_uneq_hom_iff_uneq {l₁ l₂ : 𝔽}
  {u₁ : l₁ ⟶ k} {u₂ : obj f g ⟶ l₂} {v : l₁ ⟶ l₂} :
    u₁ ≫ h ≫ uneq f g ≫ (u₂ ++ 𝟙 1) = v ≫ ι₁ 1 ↔ u₁ ≫ comp_uneq_hom h hh ≫ u₂ = v
  := by
    have hlt (i : l₁.fin) := (comp_uneq_lt_of_condition f g h hh (u₁ i))
    simp at hlt
    constructor
    · intro h₁
      funext i
      replace h₁ := Fin.val_eq_of_eq (congr_fun h₁ i)
      simp [hlt i] at h₁
      exact Fin.eq_of_val_eq h₁
    · intro h₁
      funext i
      replace h₁ := Fin.val_eq_of_eq (congr_fun h₁ i)
      apply Fin.eq_of_val_eq
      simp [hlt i]
      exact h₁

lemma comp_uneq_iff_uneq {u : k ⟶ obj f g} :
    h ≫ uneq f g = u ≫ ι₁ 1 ↔ comp_uneq_hom h hh = u
  := by
    have i := @hom_comp_uneq_hom_iff_uneq _ _ _ _ _ h hh _ _ (𝟙 _) (𝟙 _) u
    simp at i
    exact i

lemma comp_uneq_hom_iff_uneq {l : 𝔽} {u : obj f g ⟶ l} {v : k ⟶ l} :
    h ≫ uneq f g ≫ (u ++ 𝟙 _) = v ≫ ι₁ 1 ↔ comp_uneq_hom h hh ≫ u = v
  := by
    have i := @hom_comp_uneq_hom_iff_uneq _ _ _ _ _ h hh _ _ (𝟙 _) u v
    simp at i
    exact i

lemma hom_comp_uneq_iff_uneq {l : 𝔽} {u : l ⟶ k} {v : l ⟶ obj f g} :
    u ≫ h ≫ uneq f g = v ≫ ι₁ 1 ↔ u ≫ comp_uneq_hom h hh = v
  := by
    have i := @hom_comp_uneq_hom_iff_uneq _ _ _ _ _ h hh _ _ u (𝟙 _) v
    simp at i
    exact i

end

section

variable {m n : 𝔽} {f g : m ⟶ n}

lemma equal_comp_uneq_id :
    comp_uneq_hom (equal f g) (equal_condition f g) = 𝟙 (obj f g)
  :=
    (comp_uneq_iff_uneq _ (equal_condition f g)).mp
      ((left_comp_eq f g).trans (Category.id_comp _).symm)

variable {k : 𝔽} {h : k ⟶ m} (hh : h ≫ f = h ≫ g)

@[inline]
abbrev lift : k ⟶ obj f g := comp_uneq_hom h hh

lemma fac : lift hh ≫ equal f g = h := by
  apply (comp_uneq_hom_iff_uneq _ hh).mp
  funext i
  apply (congr_fun (_ ≫= right_comp_eq f g) i).trans
  apply Fin.eq_of_val_eq
  replace hh := congr_fun hh i
  simp at hh
  simp [hh]

lemma uniq (s : k ⟶ obj f g) (hs : s ≫ equal f g = h) :
    s = comp_uneq_hom h hh
  :=
    ((s ≫= equal_comp_uneq_id).trans (Category.comp_id s)).symm.trans
      ((hom_comp_uneq_iff_uneq _ (equal_condition f g)).mp
        ((Category.assoc _ _ _).symm.trans (hs =≫ _)))

end

end Equalizer

end IndexCategory

end CategoryTheory

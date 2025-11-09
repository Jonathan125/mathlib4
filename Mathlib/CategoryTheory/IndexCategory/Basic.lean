import Mathlib.CategoryTheory.Iso


namespace CategoryTheory

namespace IndexCategory

abbrev 𝔽 : Type := ℕ

namespace 𝔽

@[inline]
abbrev fin (n : 𝔽) : Type := Fin n

@[inline]
abbrev Hom (m n : 𝔽) : Type := m.fin → n.fin

instance Quiver : Quiver 𝔽 where
  Hom := Hom

def id (n : 𝔽) : n ⟶ n := (·)

def comp {m n k : 𝔽} (f : m ⟶ n) (g : n ⟶ k) : m ⟶ k := g ∘ f

instance Cat : SmallCategory.{0} 𝔽 where
  id := id
  comp := comp

@[simp]
lemma id_app (n : 𝔽) (i : n.fin) : 𝟙 n i = i := rfl

@[simp]
lemma comp_app {m n k : 𝔽} (f : m ⟶ n) (g : n ⟶ k) (i : m.fin) :
  (f ≫ g) i = g (f i) := rfl

@[simp]
lemma hom_app_ext {m n : 𝔽} (f : m ⟶ n) (i j : m.fin) :
    i.val = j.val → f i = f j
  :=
    fun h ↦ congr_arg f (Fin.eq_of_val_eq h)

@[simp]
lemma hom_app_val_ext {m n : 𝔽} (f : m ⟶ n) (i j : m.fin) :
    i.val = j.val → (f i).val = (f j).val
  :=
    fun h ↦ congr_arg _ (hom_app_ext f i j h)

@[inline]
abbrev zero : 𝔽 := 0

def zero_to (n : 𝔽) : zero ⟶ n := Fin.elim0

lemma zero_ext {n : 𝔽} (f g : zero ⟶ n) : f = g :=
  funext (fun i ↦ i.elim0)

def elim_succ_hom_zero {m : 𝔽} (f : m + 1 ⟶ zero) {α : Sort*} : α :=
  (f 0).elim0

@[inline]
abbrev one : 𝔽 := 1

def to_one (n : 𝔽) : n ⟶ one := Function.const _ 0

lemma one_ext {n : 𝔽} (f g : n ⟶ 1) : f = g :=
  funext (fun _ ↦ Fin.subsingleton_one.elim _ _)

@[simp]
lemma to_one_app {n : 𝔽} (f : n ⟶ 1) (i : n.fin) : f i = 0 :=
  Fin.subsingleton_one.elim _ _

def const_hom {n : 𝔽} (i : n.fin) : 1 ⟶ n := Function.const _ i

@[simp]
lemma const_hom_app {n : 𝔽} (i : n.fin) (j : one.fin) : const_hom i j = i := rfl

lemma const_hom_ext {n : 𝔽} (f g : 1 ⟶ n) : f 0 = g 0 → f = g := by
  intro h
  funext i
  obtain rfl : i = 0 := Fin.subsingleton_one.elim _ _
  exact h

def eqHom {m n : 𝔽} (h : m = n) : m ⟶ n := Fin.cast h

@[simp]
lemma eqHom_val {m n : 𝔽} (h : m = n) (i : m.fin) : (eqHom h i).val = i.val := rfl

@[simp]
lemma eqHom_id (m : 𝔽) : eqHom (Eq.refl m) = 𝟙 m := rfl

@[reassoc (attr := simp)]
lemma eqHom_comp_eqHom {m n k : 𝔽} (h₁ : m = n) (h₂ : n = k) :
  eqHom h₁ ≫ eqHom h₂ = eqHom (h₁.trans h₂) := rfl

lemma hom_hext {m₁ n₁ m₂ n₂ : 𝔽} (f₁ : m₁ ⟶ n₁) (f₂ : m₂ ⟶ n₂) :
    m₁ = m₂ → n₁ = n₂ →
    (∀ (i₁ : m₁.fin) (i₂ : m₂.fin), i₁.val = i₂.val → (f₁ i₁).val = (f₂ i₂).val) →
    HEq f₁ f₂
  := by
    intro h₁ h₂
    subst h₁ h₂
    intro h₃
    apply (heq_eq_eq _ _).mpr
    funext i
    exact Fin.eq_of_val_eq (h₃ _ _ rfl)

@[simps]
def eqHomIso {m n : 𝔽} (h : m = n) : m ≅ n where
  hom := eqHom h
  inv := eqHom h.symm

@[inline]
abbrev commIso {m n : 𝔽} : m + n ≅ n + m := eqHomIso (Nat.add_comm m n)

@[inline]
abbrev assocIso {m n k : 𝔽} : m + n + k ≅ m + (n + k) := eqHomIso (Nat.add_assoc m n k)

@[inline]
abbrev last (m : 𝔽) : (m + 1).fin := Fin.last m

@[simp]
lemma last_val (m : 𝔽) : m.last.val = m := rfl

def castSucc {n : 𝔽} : n ⟶ n + 1 := fun i ↦ i.castSucc

@[simp]
lemma castSucc_val {n : 𝔽} (i : n.fin) : (castSucc i).val = i.val := rfl

def addSucc {n : 𝔽} : n ⟶ n + 1 := fun i ↦ i.succ

@[simp]
lemma addSucc_val {n : 𝔽} (i : n.fin) : (addSucc i).val = i.val + 1 := rfl

def pred {n : 𝔽} : n ⟶ n :=
  fun i ↦ ⟨i.val - 1, Nat.lt_of_le_of_lt (Nat.pred_le i.val) i.isLt⟩

@[simp]
lemma pred_value {n : 𝔽} (i : n.fin) : (pred i).val = i.val - 1 := rfl

end 𝔽

end IndexCategory

end CategoryTheory

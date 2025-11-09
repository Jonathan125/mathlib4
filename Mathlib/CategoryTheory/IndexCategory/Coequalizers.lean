import Mathlib.Data.FinEnum
import Mathlib.CategoryTheory.IndexCategory.Partition
import Mathlib.CategoryTheory.IndexCategory.Basic


namespace CategoryTheory

namespace IndexCategory

section Coequalizer

open 𝔽 Category Nat Fin Partition Relation

variable {m n : 𝔽} (f g : m ⟶ n)

@[reducible]
def relation (i j : n.fin) : Prop := ∃ k : m.fin, f k = i ∧ g k = j

def equivalence : n.fin → n.fin → Prop := EqvGen (relation f g)

lemma condition {k : 𝔽} (h : n ⟶ k) :
    f ≫ h = g ≫ h ↔ ∀ (i j : n.fin), equivalence f g i j → h i = h j
  := by
    constructor
    · intro he i j hr
      induction hr with
      | rel i j hr =>
        apply Exists.elim hr
        intro u ⟨h₁, h₂⟩
        exact ((congr_arg h h₁.symm).trans (congr_fun he u)).trans (congr_arg h h₂)
      | refl i => exact Eq.refl _
      | symm i j h₁ ih => exact ih.symm
      | trans i j k h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂
    · intro he
      funext i
      simp
      apply he
      exact EqvGen.rel _ _ (Exists.intro i ⟨rfl, rfl⟩)

def partition : Partition n := Partition.of_relation (relation f g)

def obj : 𝔽 := (partition f g).size.val

def coeq : n ⟶ obj f g := fun i ↦ ⟨(partition f g).val i, (partition f g).inv i⟩

lemma coeq_condition : f ≫ coeq f g = g ≫ coeq f g :=
  (condition f g _).mpr (fun i j hr ↦ eq_of_val_eq (of_relation_eqv_exact _ i j hr))

noncomputable def representatives : obj f g ⟶ n :=
  fun i ↦ Classical.choose ((partition f g).surj (castLE (le_of_lt_succ (isLt _)) i) i.isLt)

lemma right_inv : representatives f g ≫ coeq f g = 𝟙 (obj f g) := by
  funext i
  apply Fin.eq_of_val_eq
  exact (Classical.choose_spec
    ((partition f g).surj (castLE (le_of_lt_succ (isLt _)) i) i.isLt)).symm

lemma left_rel (i : n.fin) : (partition f g).rel ((coeq f g ≫ representatives f g) i) i := by
  change ((coeq f g ≫ representatives f g ≫ coeq f g) i).val = (coeq f g i).val
  exact congr_arg _ (congr_fun ((_ ≫= right_inv f g).trans (comp_id _)) i)

variable {k : 𝔽} (h : n ⟶ k)

noncomputable def desc : obj f g ⟶ k := representatives f g ≫ h

lemma fac (hh : f ≫ h = g ≫ h) : coeq f g ≫ desc f g h = h :=
  funext (fun i ↦ (condition f g h).mp hh _ _ (of_relation_eqv_sound _ _ _ (left_rel f g i)))

lemma uniq (s : obj f g ⟶ k) (hs : coeq f g ≫ s = h) : s = desc f g h :=
  (id_comp _).symm.trans (((right_inv _ _).symm =≫ _).trans ((assoc _ _ _).trans (_ ≫= hs)))

end Coequalizer

end IndexCategory

end CategoryTheory

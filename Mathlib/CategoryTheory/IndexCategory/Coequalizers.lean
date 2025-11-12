import Mathlib.Data.FinEnum
import Mathlib.CategoryTheory.IndexCategory.Partition
import Mathlib.CategoryTheory.IndexCategory.Defs


namespace CategoryTheory

namespace IndexCategory

section Coequalizer

open Category Nat Fin Partition Relation

variable {m n : IndexCategory} (f g : m ⟶ n)

@[reducible]
def relation (i j : Fin n.len) : Prop := ∃ k : Fin m.len, f.toFun k = i ∧ g.toFun k = j

def equivalence : Fin n.len → Fin n.len → Prop := EqvGen (relation f g)

lemma coeq_condition_iff_eqv_exact {k : IndexCategory} (h : n ⟶ k) :
    f ≫ h = g ≫ h ↔ ∀ (i j : Fin n.len), equivalence f g i j → h.toFun i = h.toFun j
  := by
    constructor
    · intro he i j hr
      induction hr with
      | rel i j hr =>
        apply Exists.elim hr
        intro u ⟨h₁, h₂⟩
        replace he := congr_fun (congr_arg Hom.toFun he) u
        simp at he
        exact (congr_arg h.toFun h₁.symm).trans (he.trans (congr_arg h.toFun h₂))
      | refl i => exact Eq.refl _
      | symm i j h₁ ih => exact ih.symm
      | trans i j k h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂
    · intro he
      apply Hom.ext
      funext i
      simp
      apply he
      exact EqvGen.rel _ _ (Exists.intro i ⟨rfl, rfl⟩)

def partition : Partition n.len :=
  Partition.of_relation (relation f g)

@[inline]
abbrev coeq_obj : IndexCategory := mk (partition f g).size.val

@[inline, simp]
abbrev coeq_toFun : Fin n.len → Fin (coeq_obj f g).len :=
  Fin.cast (len_mk _).symm ∘ (partition f g).map

def coeq_hom : n ⟶ coeq_obj f g :=
  Hom.mk (coeq_toFun f g)

@[simp]
lemma coeq_hom_toFun : (coeq_hom f g).toFun = coeq_toFun f g :=
  Hom.toFun_mk _

theorem coeq_condition : f ≫ coeq_hom f g = g ≫ coeq_hom f g := by
  apply (coeq_condition_iff_eqv_exact f g _).mpr
  intro i j hr
  simp
  exact of_relation_eqvGen_exact _ i j hr

@[inline, simp]
abbrev rep_toFun : Fin (coeq_obj f g).len → Fin n.len :=
  (partition f g).rep ∘ Fin.cast (len_mk _)

def rep_hom : coeq_obj f g ⟶ n :=
  Hom.mk (rep_toFun f g)

@[simp]
lemma rep_hom_toFun : (rep_hom f g).toFun = rep_toFun f g :=
  Hom.toFun_mk _

@[reassoc (attr := simp)]
theorem rep_comp_coeq_id : rep_hom f g ≫ coeq_hom f g = 𝟙 (coeq_obj f g) :=
  by ext i ; simp [Function.comp, Fin.cast]

theorem coeq_comp_rep_mapEq (i : Fin n.len) :
    (partition f g).mapEq ((coeq_hom f g ≫ rep_hom f g).toFun i) i :=
  by ext ; simp

variable {k : IndexCategory} (h : n ⟶ k)

def desc : coeq_obj f g ⟶ k :=
  rep_hom f g ≫ h

theorem fac (hh : f ≫ h = g ≫ h) : coeq_hom f g ≫ desc f g h = h := by
  apply Hom.ext
  funext i
  rw [desc, <-Category.assoc, comp_toFun]
  dsimp
  apply (coeq_condition_iff_eqv_exact f g h).mp hh
  apply of_relation_eqvGen_sound
  exact coeq_comp_rep_mapEq _ _ i

theorem uniq (s : coeq_obj f g ⟶ k) (hs : coeq_hom f g ≫ s = h) : s = desc f g h :=
  (id_comp _).symm.trans <| ((rep_comp_coeq_id _ _).symm =≫ _).trans <|
    (assoc _ _ _).trans (_ ≫= hs)

end Coequalizer

end IndexCategory

end CategoryTheory

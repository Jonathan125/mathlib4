/-
Copyright (c) 2025 Jonathan Konig. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Konig
-/
import Mathlib.Data.FinEnum
import Mathlib.CategoryTheory.IndexCategory.Partition
import Mathlib.CategoryTheory.IndexCategory.Basic


namespace CategoryTheory

namespace IndexCategory

namespace Coequalizer

open Category Nat Fin Partition Relation

variable {m n : IndexCategory} (f g : m ⟶ n)

@[reducible]
protected def relation (i j : Fin n.len) : Prop :=
  ∃ k : Fin m.len, f.toFun k = i ∧ g.toFun k = j

protected def equivalence : Fin n.len → Fin n.len → Prop :=
  EqvGen (Coequalizer.relation f g)

protected theorem condition_iff_equivalence_exact {k : IndexCategory} (h : n ⟶ k) :
    f ≫ h = g ≫ h ↔
    ∀ (i j : Fin n.len), Coequalizer.equivalence f g i j → h.toFun i = h.toFun j := by
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

protected def partition : Partition n.len :=
  Partition.of_relation (Coequalizer.relation f g)

protected def obj : IndexCategory :=
  mk (Coequalizer.partition f g).size

protected def hom : n ⟶ Coequalizer.obj f g :=
  Hom.mk <| Fin.cast (len_mk _).symm ∘ (Coequalizer.partition f g).map

@[simp]
protected theorem coeq_toFun_apply (i : Fin n.len) :
    (Coequalizer.hom f g).toFun i = Fin.cast (len_mk _).symm ((Coequalizer.partition f g).map i) :=
  Hom.toFun_mk_apply _ _

protected theorem condition : f ≫ Coequalizer.hom f g = g ≫ Coequalizer.hom f g := by
  apply (Coequalizer.condition_iff_equivalence_exact f g _).mpr
  intro i j hr
  simp only [Coequalizer.coeq_toFun_apply]
  exact congr_arg _ (of_relation_eqvGen_exact (Coequalizer.relation f g) i j hr)

protected def rep : Coequalizer.obj f g ⟶ n :=
  Hom.mk <| (Coequalizer.partition f g).rep ∘ Fin.cast (len_mk _)

@[simp]
protected theorem rep_toFun_apply (i : Fin (Coequalizer.obj f g).len) :
    (Coequalizer.rep f g).toFun i = (Coequalizer.partition f g).rep (Fin.cast (len_mk _) i) :=
  Hom.toFun_mk_apply _ _

@[reassoc (attr := simp)]
protected theorem rep_comp_coeq_id :
    Coequalizer.rep f g ≫ Coequalizer.hom f g = 𝟙 (Coequalizer.obj f g) :=
  by ext i ; simp [-len_mk]

protected theorem coeq_comp_rep_mapEq (i : Fin n.len) :
    (Coequalizer.partition f g).mapEq ((Coequalizer.hom f g ≫ Coequalizer.rep f g).toFun i) i :=
  by ext ; simp [-len_mk]

variable {k : IndexCategory} (h : n ⟶ k)

protected def desc : Coequalizer.obj f g ⟶ k :=
  Coequalizer.rep f g ≫ h

protected theorem fac (hh : f ≫ h = g ≫ h) : Coequalizer.hom f g ≫ Coequalizer.desc f g h = h := by
  ext i : 2
  rw [Coequalizer.desc, <-Category.assoc, comp_toFun]
  dsimp
  apply (Coequalizer.condition_iff_equivalence_exact f g h).mp hh
  exact of_relation_eqvGen_sound _ _ _ (Coequalizer.coeq_comp_rep_mapEq _ _ i)

protected theorem uniq (s : Coequalizer.obj f g ⟶ k) (hs : Coequalizer.hom f g ≫ s = h) :
    s = Coequalizer.desc f g h :=
  (id_comp _).symm.trans <| ((Coequalizer.rep_comp_coeq_id _ _).symm =≫ _).trans <|
    (assoc _ _ _).trans (_ ≫= hs)

end Coequalizer

end IndexCategory

end CategoryTheory

import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import Mathlib.CategoryTheory.IndexCategory.Coproduct
import Mathlib.CategoryTheory.IndexCategory.Coequalizers


namespace CategoryTheory

namespace IndexCategory

open Limits


section Initial

def initial : IsInitial zero where
  desc s := zero_to s.pt
  uniq _ _ _ := zero_to_ext _ _

instance hasInitial : HasInitial IndexCategory := initial.hasInitial

end Initial


section BinaryCoproducts

def binary_cofan (m n : IndexCategory) : BinaryCofan m n := BinaryCofan.mk ι₁ ι₂

def binary_coproduct {m n : IndexCategory} : IsColimit (binary_cofan m n) :=
  BinaryCofan.isColimitMk (fun s ↦ [s.inl, s.inr])
    (fun _ ↦ ι₁_comp_match _ _) (fun _ ↦ ι₂_comp_match _ _) (fun _ _ ↦ match_uniq)

instance hasColimitPair {m n : IndexCategory} : HasColimit (pair m n) :=
  HasColimit.mk ⟨_, binary_coproduct⟩

instance hasBinaryCoproducts : HasBinaryCoproducts IndexCategory :=
  hasBinaryCoproducts_of_hasColimit_pair IndexCategory

end BinaryCoproducts


section FiniteCoproducts

def finite_cofan_colimit {n : IndexCategory} (f : Fin n.len → IndexCategory) :
    IsColimit (Cofan.mk (sum f) (ι f)) :=
  mkCofanColimit _ (fun s ↦ match_homs (s.ι.app ⟨·⟩))
    (fun _ ↦ ι_comp_match_homs _) (fun _ ↦ match_homs_uniq _)

variable {n : ℕ} (F : Discrete (Fin n) ⥤ IndexCategory)

def finite_cofan : Cocone F where
  pt := sum (F.obj ∘ Discrete.mk ∘ Fin.cast (len_mk _))
  ι := Discrete.natTrans (fun ⟨i⟩ ↦ ι (F.obj ∘ Discrete.mk ∘ Fin.cast (len_mk _))
    (Fin.cast (len_mk _).symm i))

def finite_coproduct : IsColimit (finite_cofan F) where
  desc := fun s ↦ match_homs (fun i ↦ s.ι.app ⟨Fin.cast (len_mk _) i⟩)
  fac := fun _ ⟨i⟩ ↦ ι_comp_match_homs _ (Fin.cast (len_mk _).symm i)
  uniq := fun _ _ hm ↦ match_homs_uniq _ _ (hm ⟨Fin.cast (len_mk _) ·⟩)

instance hasFiniteCoproducts : HasFiniteCoproducts IndexCategory :=
  ⟨fun _ ↦ ⟨(HasColimit.mk ⟨_, finite_coproduct ·⟩)⟩⟩

end FiniteCoproducts


section Coequalizers

variable {m n : IndexCategory} (f g : m ⟶ n)

def coequalizer_cofork : Cofork f g := Cofork.ofπ (coeq_hom f g) (coeq_condition f g)

def coequalizer : IsColimit (coequalizer_cofork f g) :=
  Cofork.IsColimit.mk _ (fun s ↦ desc f g s.π) (fun s ↦ fac _ _ _ s.condition) (fun _ ↦ uniq _ _ _)

instance hasColimitParallelPair : HasColimit (parallelPair f g) :=
  HasColimit.mk ⟨_, coequalizer f g⟩

instance hasCoequalizers : HasCoequalizers IndexCategory :=
  hasCoequalizers_of_hasColimit_parallelPair IndexCategory

end Coequalizers


section FinitelyCocomplete

instance finitelyCocomplete : HasFiniteColimits IndexCategory :=
  hasFiniteColimits_of_hasCoequalizers_and_finite_coproducts

end FinitelyCocomplete


end IndexCategory

end CategoryTheory

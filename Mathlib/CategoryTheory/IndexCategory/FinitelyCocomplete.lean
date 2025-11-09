import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import Mathlib.CategoryTheory.IndexCategory.Coproducts
import Mathlib.CategoryTheory.IndexCategory.Coequalizers


namespace CategoryTheory

namespace IndexCategory

open 𝔽 Limits


section Initial

def initial : IsInitial zero where
  desc s := zero_to s.pt
  uniq _ _ _ := zero_ext _ _

instance hasInitial : HasInitial 𝔽 := initial.hasInitial

end Initial


section BinaryCoproducts

open BinaryCofan HasColimit

def binary_cofan (m n : 𝔽) : BinaryCofan m n := mk (ι₁ n) (ι₂ m)

def binary_coproduct {m n : 𝔽} : IsColimit (binary_cofan m n) :=
  isColimitMk (fun s ↦ [s.inl, s.inr])
    (fun _ ↦ ι₁_comp_match _ _) (fun _ ↦ ι₂_comp_match _ _) (fun _ _ ↦ match_uniq)

instance hasColimitPair {m n : 𝔽} : HasColimit (pair m n) :=
  mk ⟨_, binary_coproduct⟩

instance hasBinaryCoproducts : HasBinaryCoproducts 𝔽 :=
  hasBinaryCoproducts_of_hasColimit_pair 𝔽

end BinaryCoproducts


section FiniteCoproducts

open Discrete HasColimit Cofan

def finite_cofan_colimit {n : 𝔽} (f : n.fin → 𝔽) : IsColimit (mk (sum f) (ι f)) :=
  mkCofanColimit _ (fun s ↦ match_homs (s.ι.app ⟨·⟩))
    (fun _ ↦ ι_comp_match_homs _ _) (fun _ ↦ match_homs_uniq _)

variable {n : 𝔽} (F : Discrete n.fin ⥤ 𝔽)

def finite_cofan : Cocone F where
  pt := sum (F.obj ∘ mk)
  ι := natTrans (fun ⟨i⟩ ↦ ι (F.obj ∘ mk) i)

def finite_coproduct : IsColimit (finite_cofan F) where
  desc := fun s ↦ match_homs (fun i ↦ s.ι.app ⟨i⟩)
  fac := fun _ ⟨i⟩ ↦ ι_comp_match_homs _ _ i
  uniq := fun _ _ hm ↦ match_homs_uniq _ _ (hm ⟨·⟩)

instance hasFiniteCoproducts : HasFiniteCoproducts 𝔽 :=
  ⟨fun _ ↦ ⟨(mk ⟨_, finite_coproduct ·⟩)⟩⟩

end FiniteCoproducts


section Coequalizers

open Cofork IsColimit HasColimit

variable {m n : 𝔽} (f g : m ⟶ n)

def coequalizer_cofork : Cofork f g := ofπ (coeq f g) (coeq_condition f g)

noncomputable def coequalizer : IsColimit (coequalizer_cofork f g) :=
  mk _ (fun s ↦ desc f g s.π) (fun s ↦ fac _ _ _ s.condition) (fun _ ↦ uniq _ _ _)

instance hasColimitParallelPair : HasColimit (parallelPair f g) :=
  mk ⟨_, coequalizer f g⟩

instance hasCoequalizers : HasCoequalizers 𝔽 :=
  hasCoequalizers_of_hasColimit_parallelPair 𝔽

end Coequalizers


section FinitelyCocomplete

instance finitelyCocomplete : HasFiniteColimits 𝔽 :=
  hasFiniteColimits_of_hasCoequalizers_and_finite_coproducts

end FinitelyCocomplete


end IndexCategory

end CategoryTheory

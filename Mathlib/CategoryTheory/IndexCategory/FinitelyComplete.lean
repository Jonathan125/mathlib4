import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import Mathlib.CategoryTheory.IndexCategory.CartesianClosed
import Mathlib.CategoryTheory.IndexCategory.Equalizers


namespace CategoryTheory

namespace IndexCategory

open 𝔽 Limits

section FiniteProducts

instance hasFiniteProducts : HasFiniteProducts 𝔽 :=
  hasFiniteProducts_of_has_binary_and_terminal

end FiniteProducts


section Equalizers

open Fork IsLimit HasLimit

variable {m n : 𝔽} (f g : m ⟶ n)

def equalizer_fork : Fork f g := ofι (equal f g) (equal_condition f g)

noncomputable def equalizer : IsLimit (equalizer_fork f g) :=
  Fork.IsLimit.mk _ (fun s ↦ lift s.condition)
    (fun s ↦ fac s.condition) (fun s _ ↦ uniq s.condition _)

instance hasLimitParallelPair : HasLimit (parallelPair f g) :=
  mk ⟨_, equalizer f g⟩

instance hasEqualizers : HasEqualizers 𝔽 :=
  hasEqualizers_of_hasLimit_parallelPair 𝔽

end Equalizers


section FinitelyComplete

instance fintelyComplete : HasFiniteLimits 𝔽 :=
  hasFiniteLimits_of_hasEqualizers_and_finite_products

end FinitelyComplete

end IndexCategory

end CategoryTheory

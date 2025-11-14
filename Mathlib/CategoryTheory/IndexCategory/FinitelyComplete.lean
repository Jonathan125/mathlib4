import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import Mathlib.CategoryTheory.IndexCategory.CartesianClosed
import Mathlib.CategoryTheory.IndexCategory.Equalizers


namespace CategoryTheory

namespace IndexCategory

open Limits

namespace FiniteProducts

instance hasFiniteProducts : HasFiniteProducts IndexCategory :=
  hasFiniteProducts_of_has_binary_and_terminal

end FiniteProducts


namespace Equalizers

variable {m n : IndexCategory} (f g : m ⟶ n)

def equalizer_fork : Fork f g :=
  Fork.ofι (Equalizers.hom f g) (Equalizers.condition f g)

def equalizer : IsLimit (equalizer_fork f g) :=
  Fork.IsLimit.mk _ (fun s ↦ Equalizers.lift s.condition)
    (fun s ↦ Equalizers.fac s.condition) (fun s _ ↦ Equalizers.uniq s.condition _)

instance hasLimitParallelPair : HasLimit (parallelPair f g) :=
  HasLimit.mk ⟨_, equalizer f g⟩

instance hasEqualizers : HasEqualizers IndexCategory :=
  hasEqualizers_of_hasLimit_parallelPair IndexCategory

end Equalizers


namespace FinitelyComplete

instance fintelyComplete : HasFiniteLimits IndexCategory :=
  hasFiniteLimits_of_hasEqualizers_and_finite_products

end FinitelyComplete

end IndexCategory

end CategoryTheory

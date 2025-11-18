/-
Copyright (c) 2025 Jonathan Konig. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Konig
-/
import Mathlib.CategoryTheory.Skeletal
import Mathlib.CategoryTheory.IndexCategory.Partition
import Mathlib.CategoryTheory.IndexCategory.Basic

/-! # The index category is skeletal

In this file, we show that isomorphic objects in the index category are equal. This
is accomplished using results about function properties defined
in `Mathlib/CategoryTheory/IndexCategory/Partition.lean`.
-/

namespace CategoryTheory

namespace IndexCategory

namespace Skeletal

theorem le_of_toFun_inj {m n : IndexCategory} (f : m ⟶ n) :
    Function.Injective f.toFun → m.len ≤ n.len :=
  Fin.le_of_inj f.toFun

theorem eq_of_iso {m n : IndexCategory} (i : m ≅ n) : m = n :=
  ext _ _ <| Fin.eq_of_bij i.hom.toFun (iso_hom_toFun_bijective i)

theorem isSkeletal : Skeletal IndexCategory := fun _ _ h ↦ eq_of_iso h.some

end Skeletal

end IndexCategory

end CategoryTheory

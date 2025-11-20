/-
Copyright (c) 2025 Jonathan Konig. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Konig
-/
import Mathlib.CategoryTheory.Skeletal
import Mathlib.Data.Fin.Pigeonhole
import Mathlib.CategoryTheory.IndexCategory.Basic

/-! # The index category is skeletal

In this file, we show that isomorphic objects in the index category are equal.
-/

namespace CategoryTheory

namespace IndexCategory

namespace Skeletal

theorem le_of_toFun_inj {m n : IndexCategory} (f : m ⟶ n) :
    Function.Injective f.toFun → m.len ≤ n.len :=
  Fin.le_of_injective f.toFun

theorem le_of_toFun_surj {m n : IndexCategory} (f : m ⟶ n) :
    Function.Surjective f.toFun → n.len ≤ m.len :=
  Fin.le_of_surjective _

theorem eq_of_toFun_bij {m n : IndexCategory} (f : m ⟶ n) :
    Function.Bijective f.toFun → m.len = n.len :=
  fun h ↦ Nat.le_antisymm (le_of_toFun_inj _ h.left) (le_of_toFun_surj _ h.right)

theorem eq_of_iso {m n : IndexCategory} (i : m ≅ n) : m = n :=
  ext _ _ <| eq_of_toFun_bij _ <| iso_hom_toFun_bijective i

theorem isSkeletal : Skeletal IndexCategory := fun _ _ h ↦ eq_of_iso h.some

end Skeletal

end IndexCategory

end CategoryTheory

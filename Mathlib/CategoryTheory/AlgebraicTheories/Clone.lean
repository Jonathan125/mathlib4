/-
Copyright (c) 2026 Jonathan Konig. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import Mathlib.Data.Nat.Basic
import Mathlib.CategoryTheory.Category.Basic


/-!
# Clone

## Main definitions

* `FooBar`

## Main statements

* `fooBar_unique`

## Notation



## Implementation details



## References

* [F. Bar, *Quuxes*][bibkey]

## Tags

Foobars, barfoos
-/

namespace CategoryTheory

namespace AlgebraicTheories

universe u

structure AbstractClone where
  c : ℕ → Type u
  υ {n : ℕ} : Fin n → c n
  μ {m n : ℕ} : c m → (Fin m → c n) → c n
  projection {m n : ℕ} (i : Fin m) (xs : Fin m → c n) : μ (υ i) xs = xs i
  identity {n : ℕ} (x : c n) : μ x υ = x
  associativity {m n k : ℕ} (x : c m) (ys : Fin m → c n) (zs : Fin n → c k) :
    μ (μ x ys) zs = μ x (fun i ↦ μ (ys i) zs)

attribute [simp] AbstractClone.projection AbstractClone.identity AbstractClone.associativity


namespace AbstractClone

protected structure Hom (A B : AbstractClone) where
  hom {n : ℕ} : A.c n → B.c n
  υ_comm {n : ℕ} (i : Fin n) : hom (A.υ i) = B.υ i
  μ_comm {m n : ℕ} (x : A.c m) (ys : Fin m → A.c n) :
    hom (A.μ x ys) = B.μ (hom x) (fun i ↦ hom (ys i))

attribute [simp] AbstractClone.Hom.υ_comm AbstractClone.Hom.μ_comm

namespace Hom

@[simps]
protected def id (A : AbstractClone) : AbstractClone.Hom A A where
  hom := id
  υ_comm _ := rfl
  μ_comm _ _ := rfl

@[simps]
protected def comp {A B C : AbstractClone} (f : AbstractClone.Hom A B) (g : AbstractClone.Hom B C) :
    AbstractClone.Hom A C where
  hom := g.hom ∘ f.hom
  υ_comm _ := by simp
  μ_comm _ _ := by simp

end Hom

protected instance Cat : LargeCategory.{u} AbstractClone.{u} where
  Hom := AbstractClone.Hom
  id := AbstractClone.Hom.id
  comp := AbstractClone.Hom.comp


end AbstractClone

end AlgebraicTheories

end CategoryTheory

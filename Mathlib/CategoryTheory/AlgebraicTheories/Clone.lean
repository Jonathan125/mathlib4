/-
Copyright (c) 2026 Jonathan Konig. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Konig
-/
module

public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.Data.Nat.Basic

/-!
# Clone

This file defines the `AbstractClone` as a structure consisting of a family of types `C`, variables
`υ`, and a substitution operation `μ`, satisfying the laws of `projection`, `identity`, and
`associativity`.

A homomorphism of abstract clones `AbstractClone.Hom` is defined as a typeclass consisting of a
family of functions `hom` on the respective types commuting with the variables and projection
operations.

The category of abstract clones `AbstractClone.category` is defined with these objects and
morphisms.
-/

@[expose] public section

namespace CategoryTheory

namespace AlgebraicTheories

universe u

/-
The main structure defining an `AbstractClone`.
-/
structure AbstractClone : Type (u + 1) where
  C : ℕ → Type u
  υ {n : ℕ} : Fin n → C n
  μ {m n : ℕ} : C m → (Fin m → C n) → C n
  projection {m n : ℕ} (i : Fin m) (xs : Fin m → C n) : μ (υ i) xs = xs i := by cat_disch
  identity {n : ℕ} (x : C n) : μ x υ = x := by cat_disch
  associativity {m n k : ℕ} (x : C m) (ys : Fin m → C n) (zs : Fin n → C k) :
    μ (μ x ys) zs = μ x (fun i ↦ μ (ys i) zs) := by cat_disch

attribute [simp] AbstractClone.projection AbstractClone.identity AbstractClone.associativity


namespace AbstractClone

/-
A homomorphism of abstract clones
-/
@[ext]
protected structure Hom (A B : AbstractClone.{u}) : Type u where
  hom {n : ℕ} : A.C n → B.C n
  υ_comm {n : ℕ} (i : Fin n) : hom (A.υ i) = B.υ i := by cat_disch
  μ_comm {m n : ℕ} (x : A.C m) (ys : Fin m → A.C n) :
    hom (A.μ x ys) = B.μ (hom x) (fun i ↦ hom (ys i)) := by cat_disch

attribute [simp] AbstractClone.Hom.υ_comm AbstractClone.Hom.μ_comm

namespace Hom

/-
The identity morphism in the category of abstract clones.
-/
protected def id (A : AbstractClone.{u}) : AbstractClone.Hom A A where hom := id

/-
The composition of morphisms in the category of abstract clones.
-/
protected def comp {A B C : AbstractClone.{u}} (f : AbstractClone.Hom A B)
    (g : AbstractClone.Hom B C) : AbstractClone.Hom A C where hom := g.hom ∘ f.hom

end Hom

/-
The category of abstract clones.
-/
protected instance category : LargeCategory.{u} AbstractClone.{u} where
  Hom := AbstractClone.Hom
  id := AbstractClone.Hom.id
  comp := AbstractClone.Hom.comp


namespace Hom

/-
A simp theorem for the application of the identity morphism
-/
@[simp]
protected theorem id_app (A : AbstractClone.{u}) {n : ℕ} (X : A.C n) :
    AbstractClone.Hom.hom (𝟙 A) X = X := rfl

/-
A simp theorem for the application of the composition of morphisms.
-/
@[simp]
protected theorem comp_app {A B C : AbstractClone.{u}} (f : A ⟶ B) (g : B ⟶ C) {n : ℕ}
    (X : A.C n) : AbstractClone.Hom.hom (f ≫ g) X = g.hom (f.hom X) := rfl

end Hom

end AbstractClone

end AlgebraicTheories

end CategoryTheory

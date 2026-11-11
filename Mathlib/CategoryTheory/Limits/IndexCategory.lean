/-
Copyright (c) 2026 Jonathan Konig. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Konig
-/
import Mathlib.CategoryTheory.FintypeCat
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.BinaryProducts
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Square


/-!
# Basic

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

namespace FintypeCat.Skeleton

universe u

@[simp]
protected theorem id_app {n : FintypeCat.Skeleton.{u}} (i : ULift (Fin n.len)) :
    𝟙 n i = i :=
  rfl

@[simp]
protected theorem comp_app {m n k : FintypeCat.Skeleton.{u}} (f : m ⟶ n) (g : n ⟶ k)
    (i : ULift (Fin m.len)) : (f ≫ g) i = g (f i):=
  rfl

@[aesop unsafe apply]
protected theorem congr_app_val {m n : FintypeCat.Skeleton.{u}} (f : m ⟶ n)
    (i j : ULift (Fin m.len)) : i.down.val = j.down.val → (f i).down.val = (f j).down.val :=
  fun h ↦ by congr ; ext ; exact h


protected def zero_to (n : FintypeCat.Skeleton.{u}) : FintypeCat.Skeleton.mk 0 ⟶ n :=
  fun ⟨i⟩ ↦ i.elim0

protected theorem zero_to_uniq {n : FintypeCat.Skeleton.{u}} (f g : FintypeCat.Skeleton.mk 0 ⟶ n) :
    f = g :=
  funext <| fun ⟨i⟩ ↦ i.elim0

protected theorem const_comp {X Y : FintypeCat.Skeleton.{u}} (f : X ⟶ Y) (i : Fin X.len) :
    (fun (_ : ULift.{u} (Fin (FintypeCat.Skeleton.mk.{u} 1).len)) ↦ ⟨(f ⟨i⟩).down⟩)
    = (fun _ ↦ ⟨i⟩) ≫ f := rfl

protected instance add :
    HAdd FintypeCat.Skeleton.{u} FintypeCat.Skeleton.{u} FintypeCat.Skeleton.{u} where
  hAdd := fun ⟨m⟩ ⟨n⟩ ↦ ⟨m + n⟩


def to_initial_segment (m n : FintypeCat.Skeleton.{u}) : m ⟶ m + n :=
  fun ⟨i⟩ ↦ ⟨Fin.castAdd _ i⟩

def to_concluding_segment (m n : FintypeCat.Skeleton.{u}) : n ⟶ m + n :=
  fun ⟨i⟩ ↦ ⟨Fin.natAdd m.len i⟩


@[simp]
theorem to_initial_segment_app_val {m : FintypeCat.Skeleton.{u}} (i : ULift (Fin m.len))
    (n : FintypeCat.Skeleton.{u}) : (to_initial_segment m n i).down.val = i.down.val :=
  rfl

@[simp]
theorem to_concluding_segment_app_val (m : FintypeCat.Skeleton.{u}) {n : FintypeCat.Skeleton.{u}}
    (i : ULift (Fin n.len)) : (to_concluding_segment m n i).down.val = m.len + i.down.val :=
  rfl


def cast_initial_segment_to_left {m n : FintypeCat.Skeleton.{u}} (i : ULift (Fin (m + n).len))
    (h : i.down.val < m.len) : ULift (Fin m.len) :=
  ⟨⟨i.down.val, h⟩⟩

lemma cast_concluding_segment_to_right_lt {m n : FintypeCat.Skeleton.{u}}
    (i : ULift (Fin (m + n).len)) (h : ¬ i.down.val < m.len) : i.down.val - m.len < n.len :=
  Nat.sub_lt_left_of_lt_add (Nat.le_of_not_lt h) i.down.isLt

def cast_concluding_segment_to_right {m n : FintypeCat.Skeleton.{u}}
    (i : ULift (Fin (m + n).len)) (h : ¬ i.down.val < m.len) : ULift (Fin n.len) :=
  ⟨⟨i.down.val - m.len, cast_concluding_segment_to_right_lt i h⟩⟩


@[simp]
theorem cast_initial_segment_to_left_app_val {m n : FintypeCat.Skeleton.{u}}
    (i : ULift (Fin (m + n).len)) (h : i.down.val < m.len) :
    (cast_initial_segment_to_left i h).down.val = i.down.val :=
  rfl

@[simp]
theorem cast_concluding_segment_to_right_app_val {m n : FintypeCat.Skeleton.{u}}
    (i : ULift (Fin (m + n).len)) (h : ¬ i.down.val < m.len) :
    (cast_concluding_segment_to_right i h).down.val = i.down.val - m.len :=
  rfl

@[simp]
theorem to_initial_segment_cast_initial_segment_to_left {m n : FintypeCat.Skeleton.{u}}
    (i : ULift (Fin (m + n).len)) (h : i.down.val < m.len) :
    to_initial_segment m n (cast_initial_segment_to_left i h) = i :=
  rfl

@[simp]
theorem to_concluding_segment_cast_concluding_segment_to_right {m n : FintypeCat.Skeleton.{u}}
    (i : ULift (Fin (m + n).len)) (h : ¬ i.down.val < m.len) :
    to_concluding_segment m n (cast_concluding_segment_to_right i h) = i :=
  by ext ; simp [Nat.add_sub_cancel' (Nat.le_of_not_lt h)]

def coproduct_hom {m n k : FintypeCat.Skeleton.{u}} (f : m ⟶ k) (g : n ⟶ k) : m + n ⟶ k :=
  fun i ↦ if h : i.down.val < m.len
    then f (cast_initial_segment_to_left i h) else g (cast_concluding_segment_to_right i h)

infixl:80 " [,] " => coproduct_hom


@[reassoc (attr := simp)]
theorem to_initial_segment_comp_coproduct_hom {m n k : FintypeCat.Skeleton.{u}} (f : m ⟶ k)
    (g : n ⟶ k) : to_initial_segment m n ≫ f [,] g = f :=
  by funext i ; ext ; unfold coproduct_hom ; aesop

@[reassoc (attr := simp)]
theorem to_concluding_segment_comp_coproduct_hom {m n k : FintypeCat.Skeleton.{u}} (f : m ⟶ k)
    (g : n ⟶ k) : to_concluding_segment m n ≫ f [,] g = g :=
  by funext i ; ext ; simp [coproduct_hom, Nat.not_lt_of_le (Nat.le_add_right _ _)] ; aesop


theorem coproduct_hom_unique {m n k : FintypeCat.Skeleton.{u}} (f : m ⟶ k) (g : n ⟶ k)
    (h : m + n ⟶ k) : to_initial_segment m n ≫ h = f → to_concluding_segment m n ≫ h = g →
    h = coproduct_hom f g := by
  intro h₁ h₂
  funext i
  if hi : i.down.val < m.len then simp [coproduct_hom, hi, ← h₁] else simp [coproduct_hom, hi, ← h₂]

@[aesop safe apply]
theorem coproduct_hom_ext {m n k : FintypeCat.Skeleton.{u}} (f g : m + n ⟶ k) :
    to_initial_segment m n ≫ f = to_initial_segment m n ≫ g →
    to_concluding_segment m n ≫ f = to_concluding_segment m n ≫ g → f = g :=
  fun h₁ h₂ ↦ (coproduct_hom_unique _ _ _ rfl rfl).trans <| (congr_arg₂ _ h₁ h₂).trans <|
    (coproduct_hom_unique _ _ _ rfl rfl).symm


protected def initial_coproduct_square (m n : FintypeCat.Skeleton.{u}) :
    Square FintypeCat.Skeleton.{u} where
  f₁₂ := FintypeCat.Skeleton.zero_to m
  f₁₃ := FintypeCat.Skeleton.zero_to n
  f₂₄ := FintypeCat.Skeleton.to_initial_segment m n
  f₃₄ := FintypeCat.Skeleton.to_concluding_segment m n
  fac := FintypeCat.Skeleton.zero_to_uniq _ _


/-- Depends on Classical.choice -/
protected def initial : Limits.IsInitial (FintypeCat.Skeleton.mk.{u} 0) where
  desc s := FintypeCat.Skeleton.zero_to s.pt
  uniq _ _ _ := FintypeCat.Skeleton.zero_to_uniq _ _

/-- Depends on Classical.choice -/
protected instance has_initial : Limits.HasInitial FintypeCat.Skeleton :=
  FintypeCat.Skeleton.initial.hasInitial

/-- Depends on Classical.choice -/
protected def binary_cofan {m n : FintypeCat.Skeleton.{u}} : Limits.BinaryCofan m n :=
  Limits.BinaryCofan.mk (to_initial_segment m n) (to_concluding_segment m n)

/-- Depends on Classical.choice -/
protected def binary_coprod {m n : FintypeCat.Skeleton.{u}} :
    Limits.IsColimit (@FintypeCat.Skeleton.binary_cofan m n) :=
  Limits.BinaryCofan.isColimitMk (fun s ↦ s.inl [,] s.inr)
    (fun _ ↦ to_initial_segment_comp_coproduct_hom _ _)
    (fun _ ↦ to_concluding_segment_comp_coproduct_hom _ _) (fun _ _ ↦ coproduct_hom_unique _ _ _)

/-- Depends on Classical.choice -/
protected instance hasColimitPair {m n : FintypeCat.Skeleton.{u}} :
    Limits.HasColimit (Limits.pair m n) :=
  Limits.HasColimit.mk ⟨_, FintypeCat.Skeleton.binary_coprod⟩

/-- Depends on Classical.choice -/
protected instance hasBinaryCoproducts : Limits.HasBinaryCoproducts FintypeCat.Skeleton.{u} :=
  Limits.hasBinaryCoproducts_of_hasColimit_pair FintypeCat.Skeleton

/-- Depends on Classical.choice -/
protected theorem initial_coproduct_square_is_pushout {m n : FintypeCat.Skeleton.{u}} :
    (FintypeCat.Skeleton.initial_coproduct_square m n).IsPushout :=
  IsPushout.of_is_coproduct FintypeCat.Skeleton.binary_coprod FintypeCat.Skeleton.initial


end FintypeCat.Skeleton

end CategoryTheory

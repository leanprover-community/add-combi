/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import AddCombi.Mathlib.Analysis.Convex.Body

/-!
# Convex progressions

A convex progression in an abelian group `G` is given by a dimension `dim`, an `origin : G`, a
homomorphism `hom : (Fin dim → ℤ) →+ G` and a convex body `body` in `Fin dim → ℝ`. Its points are
`origin + hom v` with `v` a lattice point of `body`. We write `x ∈ P` when `x` is a point of `P`,
and `P.toFinset` is the finset of its points when `G` has decidable equality. It is `t`-proper,
written `P.Proper t`, when `hom` is injective on the lattice points of `t • body`.

## Main definitions

* `ConvexProgression G`: a convex progression in `G`.
* `ConvexProgression.toFinset`: the finset of points.
* `ConvexProgression.Proper t`: `hom` is injective on the lattice points of `t • body`.

## Main statements

* `ConvexProgression.proper_one_iff_card_toFinset`: a convex progression is `1`-proper if and only
  if it has as many points as its body has lattice points.
* `ConvexProgression.Proper.mono`: if the body contains `0`, then being `b`-proper implies being
  `a`-proper for all `0 ≤ a ≤ b`.

## Tags

convex progression, convex body, lattice points, additive combinatorics
-/

public section

open Finset
open scoped Pointwise

/-- A convex progression: the set of the points `origin + hom v` with `v` a lattice point of
`body`. -/
structure ConvexProgression (G : Type*) [AddCommGroup G] where
  /-- The dimension of the ambient lattice. -/
  dim : ℕ
  /-- The base point. -/
  origin : G
  /-- The homomorphism from the lattice to `G`. -/
  hom : (Fin dim → ℤ) →+ G
  /-- The convex body whose lattice points parametrize the progression. -/
  body : ConvexBody (Fin dim → ℝ)

namespace ConvexProgression

variable {G : Type*} [AddCommGroup G] {P : ConvexProgression G}

/-- The points of a convex progression are the `origin + hom v` with `v` a lattice point of
`body`. -/
instance : Membership G (ConvexProgression G) where
  mem P x := ∃ v ∈ P.body.latticePoints, P.origin + P.hom v = x

lemma mem_def {x : G} : x ∈ P ↔ ∃ v ∈ P.body.latticePoints, P.origin + P.hom v = x := .rfl

/-- The finset of points of a convex progression. -/
@[expose]
noncomputable def toFinset [DecidableEq G] (P : ConvexProgression G) : Finset G :=
  P.body.latticePoints.image fun v ↦ P.origin + P.hom v

section Finset

variable [DecidableEq G]

@[simp]
lemma mem_toFinset {x : G} : x ∈ P.toFinset ↔ x ∈ P := by
  simp [toFinset, mem_def]

@[simp, norm_cast]
lemma coe_toFinset (P : ConvexProgression G) : (P.toFinset : Set G) = {x | x ∈ P} :=
  Set.ext fun _ ↦ mem_toFinset

/-- A convex progression has at most as many points as its body has lattice points. -/
lemma card_toFinset_le (P : ConvexProgression G) : #P.toFinset ≤ #P.body.latticePoints :=
  card_image_le

end Finset

/-- A convex progression is `t`-proper if `hom` is injective on the lattice points of
`t • body`. -/
@[expose]
def Proper (t : ℝ) (P : ConvexProgression G) : Prop := Set.InjOn P.hom (t • P.body).latticePoints

/-- A convex progression is `1`-proper if and only if it has as many points as its body has lattice
points. -/
lemma proper_one_iff_card_toFinset [DecidableEq G] :
    P.Proper 1 ↔ #P.toFinset = #P.body.latticePoints := by
  rw [Proper, one_smul, toFinset, card_image_iff]
  simp [Set.InjOn]

/-- Every convex progression is `0`-proper, because `0` is the only lattice point of
`0 • body`. -/
@[simp]
lemma proper_zero (P : ConvexProgression G) : P.Proper 0 := by
  simp [Proper]

/-- If the body contains `0`, then being `b`-proper implies being `a`-proper for all
`0 ≤ a ≤ b`. -/
lemma Proper.mono (h₀ : 0 ∈ P.body) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (h : P.Proper b) :
    P.Proper a := by
  refine Set.InjOn.mono ?_ h
  lift b to NNReal using ha.trans hab
  lift a to NNReal using ha
  exact coe_subset.2 <| ConvexBody.latticePoints_mono <| P.body.smul_le_of_le h₀ <|
    NNReal.coe_le_coe.1 hab

end ConvexProgression

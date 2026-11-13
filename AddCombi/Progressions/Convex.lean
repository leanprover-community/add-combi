/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Mathlib.Analysis.Convex.Body

/-!
# Convex progressions

A finset in an additive commutative group `G` is a convex progression of rank `d` if there exist a
base point `a : G`, basis vectors `v : Fin d → G` and a convex body `𝒦` in `Fin d → ℝ` such that its
elements are the sums `a + ∑ i, ℓ i • v i` over the lattice points `ℓ : Fin d → ℤ` of `𝒦`.

A finset is a proper convex progression if there exist such `a`, `v` and `𝒦` for which these sums
are distinct. It is a `t`-proper convex progression for a real number `t` if there exist such `a`,
`v` and `𝒦` for which the sums `a + ∑ i, ℓ i • v i` over the lattice points `ℓ` of `t • 𝒦` are
distinct.

## Main definitions

* `convexProgressionTerm a v ℓ`: The term `a + ∑ i, ℓ i • v i` of index `ℓ` of the convex
  progressions with base point `a` and basis vectors `v`.
* `ConvexBody.latticePoints 𝒦`: The finset of the lattice points `ℓ : Fin d → ℤ` of the convex body
  `𝒦` in `Fin d → ℝ`.
* `convexProgression a v 𝒦`: The convex progression with base point `a`, basis vectors `v` and
  convex body `𝒦`.
* `IsConvexProgressionWith 𝒦 P`: The finset `P` is a convex progression with convex body `𝒦`.
* `IsConvexProgression d P`: The finset `P` is a convex progression of rank `d`.
* `IsProperConvexProgressionWith t 𝒦 P`: The finset `P` is a `t`-proper convex progression with
  convex body `𝒦`.
* `IsProperConvexProgression t d P`: The finset `P` is a `t`-proper convex progression of rank `d`.

## Main statements

* `card_convexProgression_eq_iff`: The cardinality of `convexProgression a v 𝒦` is the number of
  lattice points of `𝒦` if and only if its terms with indices in `𝒦` are distinct.
* `IsProperConvexProgressionWith.anti`: If `𝒦` contains `0`, then being `t₂`-proper with convex body
  `𝒦` implies being `t₁`-proper with convex body `𝒦` for all `0 ≤ t₁ ≤ t₂`.
* `nsmul_image_convexProgressionTerm`: The `t`-fold sumset of the terms with base point `a` and
  indices in a finset `s` is the finset of the terms with base point `t • a` and indices in the
  `t`-fold sumset `t • s`.

## Tags

convex progression, convex body, lattice points, additive combinatorics
-/

public section

open Finset
open scoped Pointwise

variable {G : Type*} [AddCommGroup G] {d : ℕ} {a x : G} {v : Fin d → G}
  {𝒦 : ConvexBody (Fin d → ℝ)} {ℓ : Fin d → ℤ}

/-- The term of index `ℓ` of the convex progressions in an additive commutative group `G` with base
point `a` and basis vectors `v` is the sum `a + ∑ i, ℓ i • v i`. -/
@[expose]
def convexProgressionTerm (a : G) (v : Fin d → G) (ℓ : Fin d → ℤ) : G := a + ∑ i, ℓ i • v i

lemma convexProgressionTerm_add (a b : G) (v : Fin d → G) (ℓ₁ ℓ₂ : Fin d → ℤ) :
    convexProgressionTerm (a + b) v (ℓ₁ + ℓ₂) =
      convexProgressionTerm a v ℓ₁ + convexProgressionTerm b v ℓ₂ := by
  simp [convexProgressionTerm, add_smul, sum_add_distrib, add_add_add_comm]

/-- Whether the terms with indices in `s` are distinct does not depend on the base point. -/
lemma injOn_convexProgressionTerm_iff (a b : G) {s : Set (Fin d → ℤ)} :
    Set.InjOn (convexProgressionTerm a v) s ↔ Set.InjOn (convexProgressionTerm b v) s := by
  simp [Set.InjOn, convexProgressionTerm]

namespace ConvexBody

private lemma finite_setOf_intCast_mem (𝒦 : ConvexBody (Fin d → ℝ)) :
    {ℓ : Fin d → ℤ | (fun i ↦ (ℓ i : ℝ)) ∈ 𝒦}.Finite :=
  ((Topology.IsClosedEmbedding.piMap fun _ ↦ Int.isClosedEmbedding_coe_real).isCompact_preimage
    𝒦.isCompact).finite_of_discrete

/-- The lattice points of a convex body `𝒦` in `Fin d → ℝ` are the `ℓ : Fin d → ℤ` that lie in `𝒦`.
They form a finset because `𝒦` is compact. -/
noncomputable def latticePoints (𝒦 : ConvexBody (Fin d → ℝ)) : Finset (Fin d → ℤ) :=
  𝒦.finite_setOf_intCast_mem.toFinset

@[simp]
lemma mem_latticePoints : ℓ ∈ 𝒦.latticePoints ↔ (fun i ↦ (ℓ i : ℝ)) ∈ 𝒦 := by
  simp [latticePoints]

@[simp]
lemma latticePoints_zero_smul (𝒦 : ConvexBody (Fin d → ℝ)) :
    ((0 : ℝ) • 𝒦).latticePoints = {0} := by
  ext ℓ
  rw [mem_latticePoints, ← SetLike.mem_coe, coe_smul, Set.zero_smul_set 𝒦.nonempty]
  simp [funext_iff]

lemma latticePoints_mono {𝒦₁ 𝒦₂ : ConvexBody (Fin d → ℝ)} (h : 𝒦₁ ≤ 𝒦₂) :
    𝒦₁.latticePoints ⊆ 𝒦₂.latticePoints := by
  intro ℓ hℓ
  rw [mem_latticePoints] at *
  exact h hℓ

end ConvexBody

variable [DecidableEq G] {P : Finset G}

/-- The `t`-fold sumset of the terms with base point `a` and indices in a finset `s` is the finset
of the terms with base point `t • a` and indices in the `t`-fold sumset `t • s`. -/
lemma nsmul_image_convexProgressionTerm (t : ℕ) (a : G) (v : Fin d → G)
    (s : Finset (Fin d → ℤ)) :
    t • s.image (convexProgressionTerm a v) = (t • s).image (convexProgressionTerm (t • a) v) := by
  induction t with
  | zero => ext; simp [convexProgressionTerm]
  | succ t ih =>
    rw [succ_nsmul, ih, succ_nsmul s]
    change image₂ (· + ·) (image _ _) (image _ _) = image _ (image₂ (· + ·) _ _)
    rw [image₂_image_left, image₂_image_right, image_image₂]
    simp [succ_nsmul, convexProgressionTerm_add]

/-- The convex progression in an additive commutative group `G` with base point `a`, basis vectors
`v` and convex body `𝒦` is the finset of the terms `convexProgressionTerm a v ℓ` over the lattice
points `ℓ` of `𝒦`. -/
@[expose]
noncomputable def convexProgression (a : G) (v : Fin d → G) (𝒦 : ConvexBody (Fin d → ℝ)) :
    Finset G :=
  𝒦.latticePoints.image (convexProgressionTerm a v)

@[simp]
lemma mem_convexProgression :
    x ∈ convexProgression a v 𝒦 ↔ ∃ ℓ ∈ 𝒦.latticePoints, convexProgressionTerm a v ℓ = x := by
  simp [convexProgression]

/-- The cardinality of a convex progression is the number of lattice points of its convex body if
and only if its terms with indices in the convex body are distinct. -/
lemma card_convexProgression_eq_iff :
    #(convexProgression a v 𝒦) = #𝒦.latticePoints ↔
      Set.InjOn (convexProgressionTerm a v) 𝒦.latticePoints :=
  card_image_iff

/-- A finset `P` in an additive commutative group `G` is a convex progression with convex body `𝒦`
in `Fin d → ℝ` if it is `convexProgression a v 𝒦` for some base point `a : G` and basis vectors
`v : Fin d → G`. -/
@[expose]
def IsConvexProgressionWith (𝒦 : ConvexBody (Fin d → ℝ)) (P : Finset G) : Prop :=
  ∃ (a : G) (v : Fin d → G), P = convexProgression a v 𝒦

/-- A finset `P` in an additive commutative group `G` is a convex progression of rank `d` if it is
a convex progression with some convex body `𝒦` in `Fin d → ℝ`. -/
@[expose]
def IsConvexProgression (d : ℕ) (P : Finset G) : Prop :=
  ∃ 𝒦 : ConvexBody (Fin d → ℝ), IsConvexProgressionWith 𝒦 P

/-- A finset `P` in an additive commutative group `G` is a `t`-proper convex progression with convex
body `𝒦` in `Fin d → ℝ` if it is `convexProgression a v 𝒦` for some base point `a : G` and basis
vectors `v : Fin d → G` such that the terms `convexProgressionTerm a v ℓ` over the lattice points
`ℓ` of `t • 𝒦` are distinct.

A proper convex progression is a `1`-proper one. -/
@[expose]
def IsProperConvexProgressionWith (t : ℝ) (𝒦 : ConvexBody (Fin d → ℝ)) (P : Finset G) : Prop :=
  ∃ (a : G) (v : Fin d → G),
    Set.InjOn (convexProgressionTerm a v) (t • 𝒦).latticePoints ∧ P = convexProgression a v 𝒦

/-- A finset `P` in an additive commutative group `G` is a `t`-proper convex progression of rank `d`
if it is a `t`-proper convex progression with some convex body `𝒦` in `Fin d → ℝ`. -/
@[expose]
def IsProperConvexProgression (t : ℝ) (d : ℕ) (P : Finset G) : Prop :=
  ∃ 𝒦 : ConvexBody (Fin d → ℝ), IsProperConvexProgressionWith t 𝒦 P

lemma IsConvexProgressionWith.isConvexProgression (hP : IsConvexProgressionWith 𝒦 P) :
    IsConvexProgression d P :=
  ⟨𝒦, hP⟩

lemma IsProperConvexProgressionWith.isConvexProgressionWith {t : ℝ}
    (hP : IsProperConvexProgressionWith t 𝒦 P) : IsConvexProgressionWith 𝒦 P := by
  obtain ⟨a, v, -, rfl⟩ := hP
  exact ⟨a, v, rfl⟩

lemma IsProperConvexProgressionWith.isProperConvexProgression {t : ℝ}
    (hP : IsProperConvexProgressionWith t 𝒦 P) : IsProperConvexProgression t d P :=
  ⟨𝒦, hP⟩

lemma IsProperConvexProgression.isConvexProgression {t : ℝ}
    (hP : IsProperConvexProgression t d P) : IsConvexProgression d P := by
  obtain ⟨𝒦, hP⟩ := hP
  exact ⟨𝒦, hP.isConvexProgressionWith⟩

/-- If the convex body `𝒦` contains `0`, then being `t₂`-proper with convex body `𝒦` implies being
`t₁`-proper with convex body `𝒦` for all `0 ≤ t₁ ≤ t₂`. -/
lemma IsProperConvexProgressionWith.anti {t₁ t₂ : ℝ} (h𝒦 : 0 ∈ 𝒦) (ht₁ : 0 ≤ t₁) (ht : t₁ ≤ t₂)
    (hP : IsProperConvexProgressionWith t₂ 𝒦 P) : IsProperConvexProgressionWith t₁ 𝒦 P := by
  obtain ⟨a, v, hinj, rfl⟩ := hP
  refine ⟨a, v, hinj.mono ?_, rfl⟩
  lift t₂ to NNReal using ht₁.trans ht
  lift t₁ to NNReal using ht₁
  exact coe_subset.2 <| ConvexBody.latticePoints_mono <| 𝒦.smul_le_of_le h𝒦 <|
    NNReal.coe_le_coe.1 ht

/-- Every convex progression with convex body `𝒦` is `0`-proper with convex body `𝒦`, because `0` is
the only lattice point of `0 • 𝒦`. -/
@[simp]
lemma isProperConvexProgressionWith_zero :
    IsProperConvexProgressionWith 0 𝒦 P ↔ IsConvexProgressionWith 𝒦 P := by
  simp [IsProperConvexProgressionWith, IsConvexProgressionWith, Set.InjOn]

/-- Every convex progression is `0`-proper. -/
@[simp]
lemma isProperConvexProgression_zero :
    IsProperConvexProgression 0 d P ↔ IsConvexProgression d P := by
  simp [IsProperConvexProgression, IsConvexProgression]

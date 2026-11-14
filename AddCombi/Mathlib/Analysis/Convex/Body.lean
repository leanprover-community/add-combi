/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Mathlib.Algebra.Order.Pi
public import Mathlib.Analysis.Convex.Body
public import Mathlib.Data.Pi.Interval

/-!
# Lattice points of convex bodies

The lattice points of a convex body `𝒦` in `Fin d → ℝ` are the `ℓ : Fin d → ℤ` that lie in `𝒦`.
They form a finset because `𝒦` is compact.

## Main definitions

* `ConvexBody.latticePoints 𝒦`: The finset of the lattice points `ℓ : Fin d → ℤ` of the convex body
  `𝒦` in `Fin d → ℝ`.
* `ConvexBody.box L`: The box of the `x : Fin d → ℝ` with `0 ≤ x` and `x i ≤ L i` for all `i`.

## Main statements

* `ConvexBody.latticePoints_box`: The lattice points of `ConvexBody.box L` are the `ℓ : Fin d → ℤ`
  with `0 ≤ ℓ` and `ℓ i ≤ L i` for all `i`.
* `ConvexBody.natCast_smul_box`: Scaling `ConvexBody.box L` by `t` gives `ConvexBody.box (t • L)`.
* `ConvexBody.nsmul_latticePoints_box`: The `t`-fold sumset of the lattice points of
  `ConvexBody.box L` is the finset of the lattice points of `ConvexBody.box (t • L)`.

## Tags

convex body, lattice points, box
-/

public section

open Finset
open scoped Pointwise

namespace ConvexBody

variable {d : ℕ} {𝒦 : ConvexBody (Fin d → ℝ)} {ℓ : Fin d → ℤ}

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

/-- The box with dimensions `L` is the convex body of the `x : Fin d → ℝ` with `0 ≤ x` and
`x i ≤ L i` for all `i`. -/
@[expose]
def box (L : Fin d → ℕ) : ConvexBody (Fin d → ℝ) where
  carrier := Set.Icc 0 fun i ↦ (L i : ℝ)
  convex' := convex_Icc ..
  isCompact' := isCompact_Icc
  nonempty' := Set.nonempty_Icc.2 fun _ ↦ by simp

@[simp]
lemma coe_box (L : Fin d → ℕ) : (box L : Set (Fin d → ℝ)) = Set.Icc 0 fun i ↦ (L i : ℝ) := rfl

@[simp]
lemma zero_mem_box (L : Fin d → ℕ) : 0 ∈ box L := by
  simp [← SetLike.mem_coe, Pi.le_def]

/-- The lattice points of the box with dimensions `L` are the `ℓ : Fin d → ℤ` with `0 ≤ ℓ` and
`ℓ i ≤ L i` for all `i`. -/
@[simp]
lemma latticePoints_box (L : Fin d → ℕ) : (box L).latticePoints = Icc 0 fun i ↦ (L i : ℤ) := by
  ext ℓ
  rw [mem_latticePoints, ← SetLike.mem_coe, coe_box]
  simp only [Set.mem_Icc, mem_Icc, Pi.le_def, Pi.zero_apply]
  norm_cast

/-- Scaling the box with dimensions `L` by `t` gives the box with dimensions `t • L`. -/
@[simp]
lemma natCast_smul_box (t : ℕ) (L : Fin d → ℕ) : (t : ℝ) • box L = box (t • L) := by
  ext x
  obtain rfl | ht := t.eq_zero_or_pos
  · simp [Set.zero_smul_set, Pi.le_def, ← Pi.zero_def]
  · simp [Set.mem_smul_set_iff_inv_smul_mem₀, ht.ne', Pi.le_def, inv_mul_le_iff₀, ht]

/-- The sumset of the lattice points of the boxes with dimensions `L₁` and `L₂` is the finset of the
lattice points of the box with dimensions `L₁ + L₂`. -/
lemma latticePoints_box_add (L₁ L₂ : Fin d → ℕ) :
    (box L₁).latticePoints + (box L₂).latticePoints = (box (L₁ + L₂)).latticePoints := by
  ext ℓ
  simp only [mem_add, latticePoints_box, mem_Icc, Pi.le_def, Pi.zero_apply, Pi.add_apply]
  constructor
  · rintro ⟨ℓ₁, h₁, ℓ₂, h₂, rfl⟩
    grind [Pi.add_apply]
  · rintro ⟨h₀, h⟩
    refine ⟨fun i ↦ min (ℓ i) (L₁ i), by grind, fun i ↦ ℓ i - min (ℓ i) (L₁ i), by grind, ?_⟩
    ext i
    simp

/-- The `t`-fold sumset of the lattice points of the box with dimensions `L` is the finset of the
lattice points of the box with dimensions `t • L`. -/
lemma nsmul_latticePoints_box (t : ℕ) (L : Fin d → ℕ) :
    t • (box L).latticePoints = (box (t • L)).latticePoints := by
  induction t with
  | zero => ext; simp [← Pi.zero_def]
  | succ t ih => rw [succ_nsmul, ih, succ_nsmul L, latticePoints_box_add]

end ConvexBody

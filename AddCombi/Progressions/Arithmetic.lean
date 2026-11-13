/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import AddCombi.Progressions.Convex
public import Mathlib.Algebra.Order.Pi
public import Mathlib.Data.Pi.Interval

/-!
# Generalized arithmetic progressions

We follow Definition 0.2 of Tao and Vu (see also the definition of `F_t`-progression of Bilu). A
finset in an additive commutative group `G` is a generalized arithmetic progression of rank `d` if
there exist a base point `a : G`, basis vectors `v : Fin d → G` and dimensions `L : Fin d → ℕ` such
that its elements are the sums `a + ∑ i, ℓ i • v i` with `ℓ ≤ L`. We define it as the convex
progression with base point `a`, basis vectors `v` and convex body the box `ConvexBody.box L` of
the `x : Fin d → ℝ` with `0 ≤ x` and `x i ≤ L i` for all `i`.

A finset is a proper generalized arithmetic progression if there exist such `a`, `v` and `L` for
which these sums are distinct, that is, for which its cardinality is its volume `∏ i, (L i + 1)`. It
is a `t`-proper generalized arithmetic progression if there exist such `a`, `v` and `L` for which
the sums `a + ∑ i, ℓ i • v i` with `ℓ ≤ t • L` are distinct, that is, for which the progression
remains proper after its dimensions are multiplied by `t`.

## Main definitions

* `ConvexBody.box L`: The box of the `x : Fin d → ℝ` with `0 ≤ x` and `x i ≤ L i` for all `i`.
* `generalizedAP a v L`: The generalized arithmetic progression with base point `a`, basis vectors
  `v` and dimensions `L`.
* `IsGAP d P`: The finset `P` is a generalized arithmetic progression of rank `d`.
* `IsProperGAP t d P`: The finset `P` is a `t`-proper generalized arithmetic progression of rank
  `d`.

## Main statements

* `mem_generalizedAP`: The elements of `generalizedAP a v L` are the sums `a + ∑ i, ℓ i • v i` with
  `ℓ ≤ L`.
* `card_generalizedAP_eq_iff`: The cardinality of `generalizedAP a v L` is its volume
  `∏ i, (L i + 1)` if and only if its terms with indices in `ConvexBody.box L` are distinct.
* `nsmul_generalizedAP`: The `t`-fold sumset of `generalizedAP a v L` is
  `generalizedAP (t • a) v (t • L)`.
* `isProperGAP_iff_exists_card_nsmul`: A generalized arithmetic progression `P` is `t`-proper if
  and only if its `t`-fold sumset `t • P` is proper.

## References

* T. Tao and V. H. Vu, *Additive combinatorics*, Cambridge Studies in Advanced Mathematics 105,
  Cambridge University Press, 2006, Definition 0.2.
* Y. Bilu, *Structure of sets with small sumset*, Astérisque 258 (1999), 77–108, Section 1.

## Tags

generalized arithmetic progression, proper progression, additive combinatorics
-/

public section

open Finset
open scoped Pointwise

variable {G : Type*} [AddCommGroup G] [DecidableEq G] {d t t₁ t₂ : ℕ} {a x : G} {v : Fin d → G}
  {L : Fin d → ℕ} {P : Finset G}

namespace ConvexBody

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

private lemma latticePoints_box_add (L₁ L₂ : Fin d → ℕ) :
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

private lemma nsmul_latticePoints_box (t : ℕ) (L : Fin d → ℕ) :
    t • (box L).latticePoints = (box (t • L)).latticePoints := by
  induction t with
  | zero => ext; simp [← Pi.zero_def]
  | succ t ih => rw [succ_nsmul, ih, succ_nsmul L, latticePoints_box_add]

end ConvexBody

/-- The generalized arithmetic progression in an additive commutative group `G` with base point
`a`, basis vectors `v` and dimensions `L` is the convex progression with base point `a`, basis
vectors `v` and convex body `ConvexBody.box L`. -/
@[expose]
noncomputable def generalizedAP (a : G) (v : Fin d → G) (L : Fin d → ℕ) : Finset G :=
  convexProgression a v (.box L)

/-- The elements of the generalized arithmetic progression with base point `a`, basis vectors `v`
and dimensions `L` are the sums `a + ∑ i, ℓ i • v i` with `ℓ ≤ L`. -/
@[simp]
lemma mem_generalizedAP : x ∈ generalizedAP a v L ↔ ∃ ℓ ≤ L, a + ∑ i, ℓ i • v i = x := by
  simp only [generalizedAP, mem_convexProgression, ConvexBody.latticePoints_box, mem_Icc]
  constructor
  · rintro ⟨ℓ, ⟨h₀, hℓ⟩, rfl⟩
    lift ℓ to Fin d → ℕ using h₀
    exact ⟨ℓ, by simpa [Pi.le_def] using hℓ, by simp [convexProgressionTerm]⟩
  · rintro ⟨ℓ, hℓ, rfl⟩
    exact ⟨fun i ↦ ℓ i, by simpa [Pi.le_def] using hℓ, by simp [convexProgressionTerm]⟩

/-- The cardinality of a generalized arithmetic progression is its volume `∏ i, (L i + 1)` if and
only if its terms with indices in `ConvexBody.box L` are distinct. -/
lemma card_generalizedAP_eq_iff :
    #(generalizedAP a v L) = ∏ i, (L i + 1) ↔
      Set.InjOn (convexProgressionTerm a v) (ConvexBody.box L).latticePoints := by
  rw [← card_convexProgression_eq_iff, generalizedAP]
  simp [Pi.card_Icc]

/-- A finset `P` in an additive commutative group `G` is a generalized arithmetic progression of
rank `d` if it is a convex progression with convex body `ConvexBody.box L` for some dimensions
`L : Fin d → ℕ`, that is, if it is `generalizedAP a v L` for some base point `a : G`, basis vectors
`v : Fin d → G` and dimensions `L`. -/
@[expose]
def IsGAP (d : ℕ) (P : Finset G) : Prop :=
  ∃ L : Fin d → ℕ, IsConvexProgressionWith (.box L) P

lemma IsGAP.isConvexProgression (hP : IsGAP d P) : IsConvexProgression d P := by
  obtain ⟨L, hP⟩ := hP
  exact hP.isConvexProgression

/-- A finset `P` in an additive commutative group `G` is a `t`-proper generalized arithmetic
progression of rank `d` if it is a `t`-proper convex progression with convex body
`ConvexBody.box L` for some dimensions `L : Fin d → ℕ`, that is, if it is `generalizedAP a v L` for
some base point `a : G`, basis vectors `v : Fin d → G` and dimensions `L` such that the terms
`convexProgressionTerm a v ℓ` over the lattice points `ℓ` of `t • ConvexBody.box L` are distinct.

A proper generalized arithmetic progression is a `1`-proper one. -/
@[expose]
def IsProperGAP (t d : ℕ) (P : Finset G) : Prop :=
  ∃ L : Fin d → ℕ, IsProperConvexProgressionWith t (.box L) P

lemma IsProperGAP.isGAP (hP : IsProperGAP t d P) : IsGAP d P := by
  obtain ⟨L, hP⟩ := hP
  exact ⟨L, hP.isConvexProgressionWith⟩

lemma IsProperGAP.isProperConvexProgression (hP : IsProperGAP t d P) :
    IsProperConvexProgression t d P := by
  obtain ⟨L, hP⟩ := hP
  exact hP.isProperConvexProgression

/-- If a GAP is `t₂`-proper then it is `t₁`-proper for all `t₁ ≤ t₂`. -/
lemma IsProperGAP.anti (ht : t₁ ≤ t₂) (hP : IsProperGAP t₂ d P) : IsProperGAP t₁ d P := by
  obtain ⟨L, hP⟩ := hP
  exact ⟨L, hP.anti (ConvexBody.zero_mem_box L) t₁.cast_nonneg (Nat.cast_le.2 ht)⟩

/-- Every generalized arithmetic progression is `0`-proper, because `0` is the only lattice point
of `0 • ConvexBody.box L`. -/
@[simp]
lemma isProperGAP_zero : IsProperGAP 0 d P ↔ IsGAP d P := by
  simp [IsProperGAP, IsGAP]

/-- The `t`-fold sumset of the generalized arithmetic progression with base point `a`, basis vectors
`v` and dimensions `L` is the generalized arithmetic progression with base point `t • a`, basis
vectors `v` and dimensions `t • L`. -/
lemma nsmul_generalizedAP (t : ℕ) (a : G) (v : Fin d → G) (L : Fin d → ℕ) :
    t • generalizedAP a v L = generalizedAP (t • a) v (t • L) := by
  simp only [generalizedAP, convexProgression, nsmul_image_convexProgressionTerm,
    ConvexBody.nsmul_latticePoints_box]

/-- The `t`-fold sumset of a generalized arithmetic progression of rank `d` is a generalized
arithmetic progression of rank `d`. -/
lemma IsGAP.nsmul (hP : IsGAP d P) (t : ℕ) : IsGAP d (t • P) := by
  obtain ⟨L, a, v, rfl⟩ := hP
  exact ⟨t • L, t • a, v, nsmul_generalizedAP ..⟩

/-- A finset `P` is a `t`-proper generalized arithmetic progression if and only if it is a
generalized arithmetic progression whose `t`-fold sumset `t • P` is proper.

The progression with dimensions `t • L` is a translate of the `t`-fold sumset `t • P`, which is the
set of sums `t • a + ∑ i, ℓ i • v i` with `ℓ ≤ t • L`. So `P` is `t`-proper if and only if `t • P`
is proper, that is if `#(t • P) = ∏ i, (t * L i + 1)`. -/
lemma isProperGAP_iff_exists_card_nsmul :
    IsProperGAP t d P ↔ ∃ (L : Fin d → ℕ) (a : G) (v : Fin d → G),
      #(t • P) = ∏ i, (t * L i + 1) ∧ P = generalizedAP a v L := by
  apply exists₃_congr
  intro L a v
  apply and_congr_left
  rintro rfl
  rw [← generalizedAP, nsmul_generalizedAP, ConvexBody.natCast_smul_box,
    injOn_convexProgressionTerm_iff a (t • a), ← card_generalizedAP_eq_iff]
  simp

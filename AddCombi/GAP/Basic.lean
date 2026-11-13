/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Mathlib.Data.Pi.Interval
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.Group.Pointwise.Finset.Interval
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Module.Defs
import Mathlib.Algebra.Order.Pi
import Mathlib.Algebra.Order.Sub.Prod

/-!
# Generalized arithmetic progressions

We follow Definition 0.2 of Tao and Vu (see also the definition of `F_t`-progression of Bilu). A
finset in an additive commutative monoid `G` is a generalized arithmetic progression of rank `d` if
there exist a base point `a : G`, basis vectors `v : Fin d → G` and dimensions `L : Fin d → ℕ` such
that its elements are the sums `a + ∑ i, ℓ i • v i` with `ℓ ≤ L`.

A finset is a proper generalized arithmetic progression if there exist such `a`, `v` and `L` for
which these sums are distinct, that is, for which its cardinality is its volume `∏ i, (L i + 1)`. It
is a `t`-proper generalized arithmetic progression if there exist such `a`, `v` and `L` for which
the sums `a + ∑ i, ℓ i • v i` with `ℓ ≤ t • L` are distinct, that is, for which the progression
remains proper after its dimensions are multiplied by `t`.

## Main definitions

* `generalizedAPTerm a v ℓ`: The term `a + ∑ i, ℓ i • v i` of index `ℓ` of the generalized
  arithmetic progression with base point `a` and basis vectors `v`.
* `generalizedAP a v L`: The generalized arithmetic progression with base point `a`, basis vectors
  `v` and dimensions `L`.
* `IsGAP d P`: The finset `P` is a generalized arithmetic progression of rank `d`.
* `IsProperGAP t d P`: The finset `P` is a `t`-proper generalized arithmetic progression of rank
  `d`.

## Main statements

* `card_generalizedAP_eq_iff`: The cardinality of `generalizedAP a v L` is its volume
  `∏ i, (L i + 1)` if and only if its terms with indices `ℓ ≤ L` are distinct.
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

variable {G : Type*} [AddCommMonoid G] {d t t₁ t₂ : ℕ} {a x : G} {v : Fin d → G} {L : Fin d → ℕ}

/-- The term of index `ℓ` of the generalized arithmetic progression in an additive commutative
monoid `G` with base point `a` and basis vectors `v` is the sum `a + ∑ i, ℓ i • v i`. -/
@[expose]
def generalizedAPTerm (a : G) (v : Fin d → G) (ℓ : Fin d → ℕ) : G := a + ∑ i, ℓ i • v i

lemma generalizedAPTerm_add (a b : G) (v : Fin d → G) (ℓ₁ ℓ₂ : Fin d → ℕ) :
    generalizedAPTerm (a + b) v (ℓ₁ + ℓ₂) =
      generalizedAPTerm a v ℓ₁ + generalizedAPTerm b v ℓ₂ := by
  simp [generalizedAPTerm, add_smul, sum_add_distrib, add_add_add_comm]

/-- When addition in `G` is cancellative, whether the terms with indices in `s` are distinct does
not depend on the base point. -/
lemma injOn_generalizedAPTerm_iff [IsLeftCancelAdd G] (a b : G) {s : Set (Fin d → ℕ)} :
    Set.InjOn (generalizedAPTerm a v) s ↔ Set.InjOn (generalizedAPTerm b v) s := by
  simp [Set.InjOn, generalizedAPTerm]

variable [DecidableEq G] {P : Finset G}

/-- The generalized arithmetic progression in an additive commutative monoid `G` with base point
`a`, basis vectors `v` and dimensions `L` is the finset of the terms `generalizedAPTerm a v ℓ` with
`ℓ ≤ L`. -/
@[expose]
def generalizedAP (a : G) (v : Fin d → G) (L : Fin d → ℕ) : Finset G :=
  (Iic L).image (generalizedAPTerm a v)

@[simp]
lemma mem_generalizedAP : x ∈ generalizedAP a v L ↔ ∃ ℓ ≤ L, generalizedAPTerm a v ℓ = x := by
  simp [generalizedAP]

/-- The cardinality of a generalized arithmetic progression is its volume `∏ i, (L i + 1)` if and
only if its terms with indices `ℓ ≤ L` are distinct. -/
lemma card_generalizedAP_eq_iff :
    #(generalizedAP a v L) = ∏ i, (L i + 1) ↔ Set.InjOn (generalizedAPTerm a v) (Set.Iic L) := by
  rw [generalizedAP, ← coe_Iic, ← card_image_iff, Pi.card_Iic]
  simp

/-- A finset `P` in an additive commutative monoid `G` is a generalized arithmetic progression of
rank `d` if it is `generalizedAP a v L` for some base point `a : G`, basis vectors
`v : Fin d → G` and dimensions `L : Fin d → ℕ`. -/
@[expose]
def IsGAP (d : ℕ) (P : Finset G) : Prop :=
  ∃ (a : G) (v : Fin d → G) (L : Fin d → ℕ), P = generalizedAP a v L

/-- A finset `P` in an additive commutative monoid `G` is a `t`-proper generalized arithmetic
progression of rank `d` if it is `generalizedAP a v L` for some base point `a : G`, basis vectors
`v : Fin d → G` and dimensions `L : Fin d → ℕ` such that the terms `generalizedAPTerm a v ℓ` with
`ℓ ≤ t • L` are distinct.

A proper generalized arithmetic progression is a `1`-proper one. -/
@[expose]
def IsProperGAP (t d : ℕ) (P : Finset G) : Prop :=
  ∃ (a : G) (v : Fin d → G) (L : Fin d → ℕ),
    Set.InjOn (generalizedAPTerm a v) (Set.Iic (t • L)) ∧ P = generalizedAP a v L

lemma IsProperGAP.isGAP (hP : IsProperGAP t d P) : IsGAP d P := by
  obtain ⟨a, v, L, -, rfl⟩ := hP
  exact ⟨a, v, L, rfl⟩

/-- Being `t₂`-proper implies that it is `t₁`-proper for all `t₁ ≤ t₂`. -/
lemma IsProperGAP.anti (ht : t₁ ≤ t₂) (hP : IsProperGAP t₂ d P) : IsProperGAP t₁ d P := by
  obtain ⟨a, v, L, hinj, rfl⟩ := hP
  exact ⟨a, v, L, hinj.mono <| Set.Iic_subset_Iic.2 <| smul_le_smul_of_nonneg_right ht zero_le, rfl⟩

/-- Every generalized arithmetic progression is `0`-proper, because `0` is the only `ℓ ≤ 0 • L`. -/
@[simp]
lemma isProperGAP_zero : IsProperGAP 0 d P ↔ IsGAP d P := by
  simp [IsProperGAP, IsGAP, Set.InjOn]

private lemma Iic_add_Iic (L₁ L₂ : Fin d → ℕ) : Iic L₁ + Iic L₂ = Iic (L₁ + L₂) := by
  apply (Iic_add_Iic_subset L₁ L₂).antisymm
  intro ℓ hℓ
  refine mem_add.2 ⟨ℓ ⊓ L₁, by simp, ℓ - ℓ ⊓ L₁, ?_, by simp⟩
  rw [mem_Iic] at *
  intro i
  grind [Pi.sub_apply, Pi.inf_apply, Pi.add_apply, hℓ i]

/-- The `t`-fold sumset of the generalized arithmetic progression with base point `a`, basis vectors
`v` and dimensions `L` is the generalized arithmetic progression with base point `t • a`, basis
vectors `v` and dimensions `t • L`. -/
lemma nsmul_generalizedAP (t : ℕ) (a : G) (v : Fin d → G) (L : Fin d → ℕ) :
    t • generalizedAP a v L = generalizedAP (t • a) v (t • L) := by
  induction t with
  | zero => ext; simp [generalizedAPTerm, eq_comm]
  | succ t ih =>
    rw [succ_nsmul, ih]
    unfold generalizedAP
    rw [succ_nsmul L, ← Iic_add_Iic]
    change image₂ (· + ·) (image _ _) (image _ _) = image _ (image₂ (· + ·) _ _)
    rw [image₂_image_left, image₂_image_right, image_image₂]
    simp [succ_nsmul, generalizedAPTerm_add]

/-- The `t`-fold sumset of a generalized arithmetic progression of rank `d` is a generalized
arithmetic progression of rank `d`. -/
lemma IsGAP.nsmul (hP : IsGAP d P) (t : ℕ) : IsGAP d (t • P) := by
  obtain ⟨a, v, L, rfl⟩ := hP
  exact ⟨t • a, v, t • L, nsmul_generalizedAP ..⟩

/-- When addition in `G` is cancellative, a finset `P` is a `t`-proper generalized arithmetic
progression if and only if it is a generalized arithmetic progression whose `t`-fold sumset `t • P`
is proper.

The progression with dimensions `t • L` is a translate of the `t`-fold sumset `t • P`, which is the
set of sums `t • a + ∑ i, ℓ i • v i` with `ℓ ≤ t • L`. So `P` is `t`-proper if and only if `t • P`
is proper, that is if `#(t • P) = ∏ i, (t * L i + 1)`. -/
lemma isProperGAP_iff_exists_card_nsmul [IsLeftCancelAdd G] :
    IsProperGAP t d P ↔ ∃ (a : G) (v : Fin d → G) (L : Fin d → ℕ),
      #(t • P) = ∏ i, (t * L i + 1) ∧ P = generalizedAP a v L := by
  apply exists₃_congr
  intro a v L
  apply and_congr_left
  rintro rfl
  rw [nsmul_generalizedAP, injOn_generalizedAPTerm_iff a (t • a), ← card_generalizedAP_eq_iff]
  simp

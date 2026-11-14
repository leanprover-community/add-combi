/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import AddCombi.Mathlib.Combinatorics.Additive.Progressions.Convex
public import Mathlib.Algebra.Group.Pointwise.Finset.Scalar

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
* `IsGAP.add`, `IsGAP.sum`, `IsGAP.neg`, `IsGAP.sub_self` and `IsGAP.vadd`: Sumsets, negations,
  difference sets `P - P` and translates of generalized arithmetic progressions are generalized
  arithmetic progressions.
* `isGAP_sum_pair`: The subset sums of a family `v : Fin d → G` form a generalized arithmetic
  progression of rank `d`.
* `isProperGAP_iff_exists_card_nsmul`: A generalized arithmetic progression `P` is `t`-proper if
  and only if its `t`-fold sumset `t • P` is proper.
* `injOn_convexProgressionTerm_natCast_smul_box_iff`: A generalized arithmetic progression is
  `t`-proper if and only if its basis vectors admit no nonzero relation `∑ i, ℓ i • v i = 0` with
  `|ℓ i| ≤ t * L i` for all `i`.

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

/-- The cardinality of a generalized arithmetic progression is at most its volume
`∏ i, (L i + 1)`. -/
lemma card_generalizedAP_le : #(generalizedAP a v L) ≤ ∏ i, (L i + 1) := by
  rw [generalizedAP, convexProgression]
  grw [card_image_le]
  simp [Pi.card_Icc]

/-- The sumset of `generalizedAP a v L₁` and `generalizedAP b v L₂`, which have the same basis
vectors, is `generalizedAP (a + b) v (L₁ + L₂)`. -/
lemma generalizedAP_add_generalizedAP (a b : G) (v : Fin d → G) (L₁ L₂ : Fin d → ℕ) :
    generalizedAP a v L₁ + generalizedAP b v L₂ = generalizedAP (a + b) v (L₁ + L₂) := by
  simp only [generalizedAP, convexProgression, image_convexProgressionTerm_add_image,
    ConvexBody.latticePoints_box_add]

/-- The sumset of `generalizedAP a v₁ L₁` and `generalizedAP b v₂ L₂` is
`generalizedAP (a + b) (Fin.append v₁ v₂) (Fin.append L₁ L₂)`, of rank `d₁ + d₂`. -/
lemma generalizedAP_append {d₁ d₂ : ℕ} (a b : G) (v₁ : Fin d₁ → G) (v₂ : Fin d₂ → G)
    (L₁ : Fin d₁ → ℕ) (L₂ : Fin d₂ → ℕ) :
    generalizedAP (a + b) (Fin.append v₁ v₂) (Fin.append L₁ L₂) =
      generalizedAP a v₁ L₁ + generalizedAP b v₂ L₂ := by
  ext x
  simp only [mem_generalizedAP, mem_add]
  constructor
  · rintro ⟨ℓ, hℓ, rfl⟩
    refine ⟨_, ⟨fun i ↦ ℓ (Fin.castAdd d₂ i), fun i ↦ by simpa using hℓ (Fin.castAdd d₂ i), rfl⟩,
      _, ⟨fun i ↦ ℓ (Fin.natAdd d₁ i), fun i ↦ by simpa using hℓ (Fin.natAdd d₁ i), rfl⟩, ?_⟩
    simp [Fin.sum_univ_add, add_add_add_comm]
  · rintro ⟨_, ⟨ℓ₁, hℓ₁, rfl⟩, _, ⟨ℓ₂, hℓ₂, rfl⟩, rfl⟩
    refine ⟨Fin.append ℓ₁ ℓ₂, ?_, ?_⟩
    · refine Fin.addCases ?_ ?_
      · simpa [Pi.le_def] using hℓ₁
      · simpa [Pi.le_def] using hℓ₂
    · simp [Fin.sum_univ_add, add_add_add_comm]

/-- The negation of the generalized arithmetic progression with base point `a`, basis vectors `v`
and dimensions `L` is the generalized arithmetic progression with base point
`-(a + ∑ i, L i • v i)`, basis vectors `v` and dimensions `L`. -/
lemma neg_generalizedAP (a : G) (v : Fin d → G) (L : Fin d → ℕ) :
    -generalizedAP a v L = generalizedAP (-(a + ∑ i, L i • v i)) v L := by
  ext x
  simp only [generalizedAP, mem_neg', mem_convexProgression, ConvexBody.latticePoints_box, mem_Icc]
  constructor
  · rintro ⟨ℓ, ⟨h₀, hL⟩, h⟩
    obtain rfl := neg_eq_iff_eq_neg.1 h.symm
    refine ⟨(fun i ↦ (L i : ℤ)) - ℓ, ⟨sub_nonneg.2 hL, sub_le_self _ h₀⟩, ?_⟩
    simp [convexProgressionTerm, sub_smul, sum_sub_distrib]
    abel
  · rintro ⟨ℓ, ⟨h₀, hL⟩, rfl⟩
    refine ⟨(fun i ↦ (L i : ℤ)) - ℓ, ⟨sub_nonneg.2 hL, sub_le_self _ h₀⟩, ?_⟩
    simp [convexProgressionTerm, sub_smul, sum_sub_distrib]
    abel

/-- The translate by `c` of the generalized arithmetic progression with base point `a`, basis
vectors `v` and dimensions `L` is the generalized arithmetic progression with base point `c + a`,
basis vectors `v` and dimensions `L`. -/
lemma vadd_generalizedAP (c a : G) (v : Fin d → G) (L : Fin d → ℕ) :
    c +ᵥ generalizedAP a v L = generalizedAP (c + a) v L := by
  ext x
  simp [mem_vadd_finset, add_assoc]

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

lemma isGAP_iff_exists_eq_generalizedAP :
    IsGAP d P ↔ ∃ (L : Fin d → ℕ) (a : G) (v : Fin d → G), P = generalizedAP a v L :=
  .rfl

lemma isGAP_generalizedAP (a : G) (v : Fin d → G) (L : Fin d → ℕ) :
    IsGAP d (generalizedAP a v L) :=
  ⟨L, a, v, rfl⟩

/-- A singleton is a generalized arithmetic progression of rank `0`. -/
lemma isGAP_singleton (x : G) : IsGAP 0 {x} := by
  refine ⟨0, x, 0, ?_⟩
  ext y
  rw [← generalizedAP, mem_generalizedAP]
  simp [eq_comm, Unique.exists_iff]

/-- The pair `{0, a}` is a generalized arithmetic progression of rank `1`. -/
lemma isGAP_pair (a : G) : IsGAP 1 {0, a} := by
  refine ⟨1, 0, fun _ ↦ a, ?_⟩
  ext x
  rw [← generalizedAP, mem_generalizedAP, mem_insert, mem_singleton]
  constructor
  · rintro (rfl | rfl)
    · exact ⟨0, zero_le, by simp⟩
    · exact ⟨1, le_rfl, by simp⟩
  · rintro ⟨ℓ, hℓ, rfl⟩
    obtain h | h := Nat.le_one_iff_eq_zero_or_eq_one.1 (hℓ 0) <;> simp [h]

/-- The sumset of generalized arithmetic progressions of ranks `d₁` and `d₂` is a generalized
arithmetic progression of rank `d₁ + d₂`. -/
lemma IsGAP.add {d₁ d₂ : ℕ} {Q : Finset G} (hP : IsGAP d₁ P) (hQ : IsGAP d₂ Q) :
    IsGAP (d₁ + d₂) (P + Q) := by
  obtain ⟨L₁, a, v₁, rfl⟩ := isGAP_iff_exists_eq_generalizedAP.1 hP
  obtain ⟨L₂, b, v₂, rfl⟩ := isGAP_iff_exists_eq_generalizedAP.1 hQ
  rw [← generalizedAP_append]
  exact isGAP_generalizedAP ..

/-- The sum of generalized arithmetic progressions `Q i` of ranks `r i` over a finset `s` is a
generalized arithmetic progression of rank `∑ i ∈ s, r i`. -/
lemma IsGAP.sum {ι : Type*} {s : Finset ι} {r : ι → ℕ} {Q : ι → Finset G}
    (hQ : ∀ i ∈ s, IsGAP (r i) (Q i)) : IsGAP (∑ i ∈ s, r i) (∑ i ∈ s, Q i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [sum_empty, sum_empty, ← singleton_zero]
    exact isGAP_singleton 0
  | insert i s hi ih =>
    rw [sum_insert hi, sum_insert hi]
    exact (hQ i (mem_insert_self ..)).add (ih fun j hj ↦ hQ j (mem_insert_of_mem hj))

/-- The subset sums `∑ i, ({0, v i} : Finset G)` of a family `v : Fin d → G` form a generalized
arithmetic progression of rank `d`. -/
lemma isGAP_sum_pair (v : Fin d → G) : IsGAP d (∑ i, ({0, v i} : Finset G)) := by
  simpa using IsGAP.sum fun i (_ : i ∈ univ) ↦ isGAP_pair (v i)

/-- The negation of a generalized arithmetic progression of rank `d` is a generalized arithmetic
progression of rank `d`. -/
lemma IsGAP.neg (hP : IsGAP d P) : IsGAP d (-P) := by
  obtain ⟨L, a, v, rfl⟩ := isGAP_iff_exists_eq_generalizedAP.1 hP
  rw [neg_generalizedAP]
  exact isGAP_generalizedAP ..

/-- The difference set `P - P` of a generalized arithmetic progression `P` of rank `d` is a
generalized arithmetic progression of rank `d`, with the same basis vectors and twice the
dimensions. -/
lemma IsGAP.sub_self (hP : IsGAP d P) : IsGAP d (P - P) := by
  obtain ⟨L, a, v, rfl⟩ := isGAP_iff_exists_eq_generalizedAP.1 hP
  rw [sub_eq_add_neg, neg_generalizedAP, generalizedAP_add_generalizedAP]
  exact isGAP_generalizedAP ..

/-- A translate of a generalized arithmetic progression of rank `d` is a generalized arithmetic
progression of rank `d`. -/
lemma IsGAP.vadd (hP : IsGAP d P) (c : G) : IsGAP d (c +ᵥ P) := by
  obtain ⟨L, a, v, rfl⟩ := isGAP_iff_exists_eq_generalizedAP.1 hP
  rw [vadd_generalizedAP]
  exact isGAP_generalizedAP ..

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

omit [DecidableEq G] in
/-- The terms over the lattice points of `t • ConvexBody.box L` are distinct if and only if the
basis vectors `v` admit no nonzero relation `∑ i, ℓ i • v i = 0` with `|ℓ i| ≤ t * L i` for all
`i`. -/
lemma injOn_convexProgressionTerm_natCast_smul_box_iff :
    Set.InjOn (convexProgressionTerm a v) ((t : ℝ) • ConvexBody.box L).latticePoints ↔
      ∀ ℓ : Fin d → ℤ, (∀ i, |ℓ i| ≤ t * L i) → ∑ i, ℓ i • v i = 0 → ℓ = 0 := by
  simp only [ConvexBody.natCast_smul_box, ConvexBody.latticePoints_box, coe_Icc, Set.InjOn,
    Set.mem_Icc, Pi.le_def, Pi.zero_apply, Pi.smul_apply, smul_eq_mul, Nat.cast_mul]
  constructor
  · intro h ℓ hℓ hv
    have hpn : (fun i ↦ max (ℓ i) 0) = fun i ↦ max (-ℓ i) 0 := by
      refine h ?_ ?_ ?_
      · grind [abs_le]
      · grind [abs_le]
      · simp only [convexProgressionTerm, add_right_inj]
        rw [← sub_eq_zero, ← sum_sub_distrib]
        simpa [← sub_smul, max_zero_sub_max_neg_zero_eq_self] using hv
    ext i
    have hi := congr_fun hpn i
    rw [Pi.zero_apply]
    grind
  · intro h ℓ₁ hℓ₁ ℓ₂ hℓ₂ he
    rw [← sub_eq_zero]
    apply h
    · grind [abs_le, Pi.sub_apply]
    · simp only [convexProgressionTerm, add_right_inj] at he
      simp [sub_smul, sum_sub_distrib, he]

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

A generalized arithmetic progression (GAP) in an abelian group `G` is given by an `origin : G`,
steps `step : Fin dim → G` and bounds `bound : Fin dim → ℕ`, and its points are the
`origin + ∑ i, w i • step i` with `w ≤ bound` (Definition 0.2 of Tao and Vu). These are the points
of the convex progression with homomorphism `GAP.stepsHom step` and body `ConvexBody.box bound`,
so `GAP G` extends `ConvexProgression G` with the steps and the bounds, and the fields `hom_eq` and
`body_eq` tie them to the homomorphism and the body. The points, the finset `P.toFinset` and the
`t`-properness `P.Proper t` of a GAP are then those of its convex progression.

## Main definitions

* `GAP.stepsHom`: the homomorphism from `Fin d → ℤ` to `G` given by a family of steps.
* `GAP G`: a generalized arithmetic progression in `G`, not necessarily proper.
* `GAP.eval`: the point with given coefficients.
* `GAP.size`: the number `∏ i, (P.bound i + 1)` of coefficient vectors.
* `GAP.append`: the concatenation of two progressions.
* `GAP.cons a P`: the progression `P` with the step `a` of length `2` added in front.
* `GAP.difference P`: the progression with the steps of `P`, the bound `2 • P.bound` and the origin
  `-∑ i, P.bound i • P.step i`.
* `GAP.relations`: the kernel of the homomorphism of a progression.

## Main statements

* `GAP.mem_iff_exists_eval`: the points of `P` are the `P.eval w` with `w ≤ P.bound`.
* `GAP.proper_natCast_iff_card_eq_size`: for a natural number `t`, a GAP `P` is `t`-proper if and
  only if `t • P` has `(t • P).size` elements.
* `GAP.proper_nsmul_iff`: the multiple `s • P` is `t`-proper if and only if `P` is `s * t`-proper.
* `GAP.mem_append` and `GAP.toFinset_append`: the points of `GAP.append P Q` are the sums of a
  point of `P` and a point of `Q`.
* `GAP.mem_succ_nsmul` and `GAP.toFinset_nsmul`: the points of `t • P` are the sums of `t` points
  of `P`.
* `GAP.mem_vadd` and `GAP.toFinset_vadd`: the points of `c +ᵥ P` are the translates by `c` of the
  points of `P`.
* `GAP.mem_cons` and `GAP.toFinset_cons`: the points of `GAP.cons a P` are `{0, a} + P`.
* `GAP.mem_difference` and `GAP.toFinset_difference`: the points of `P.difference` are `P - P`.
* `GAP.proper_natCast_iff_relations`: for a natural number `t`, a progression is `t`-proper if and
  only if no nonzero relation `v` has `|v i| ≤ t * P.bound i` for all `i`.

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

namespace GAP

variable {G : Type*} [AddCommGroup G]

/-- The homomorphism `(Fin d → ℤ) →+ G` given by steps `step : Fin d → G`: the integer linear
combination `Fintype.linearCombination ℤ step`. -/
def stepsHom {d : ℕ} (step : Fin d → G) : (Fin d → ℤ) →+ G :=
  (Fintype.linearCombination ℤ step).toAddMonoidHom

lemma stepsHom_apply {d : ℕ} (step : Fin d → G) (v : Fin d → ℤ) :
    stepsHom step v = ∑ i, v i • step i :=
  Fintype.linearCombination_apply ℤ step v

end GAP

/-- A generalized arithmetic progression: the convex progression with homomorphism
`GAP.stepsHom step` and body `ConvexBody.box bound`, whose points are the
`origin + ∑ i, w i • step i` with `w ≤ bound`. -/
structure GAP (G : Type*) [AddCommGroup G] extends ConvexProgression G where
  /-- The steps. -/
  step : Fin dim → G
  /-- The largest coefficient of each step. The length of the step `i` is `bound i + 1`. -/
  bound : Fin dim → ℕ
  hom := GAP.stepsHom step
  body := .box bound
  /-- The homomorphism of the convex progression is given by the steps. -/
  hom_eq : hom = GAP.stepsHom step := by rfl
  /-- The body of the convex progression is the box of the bounds. -/
  body_eq : body = .box bound := by rfl

namespace GAP

attribute [simp] hom_eq body_eq

variable {G : Type*} [AddCommGroup G]

/-- The point `origin + ∑ i, w i • step i`. -/
@[expose]
def eval (P : GAP G) (w : Fin P.dim → ℕ) : G := P.origin + ∑ i, w i • P.step i

/-- The points of a progression are those of its convex progression. -/
instance : Membership G (GAP G) where
  mem P x := x ∈ P.toConvexProgression

/-- The number `∏ i, (P.bound i + 1)` of coefficient vectors `w ≤ P.bound` of a GAP. -/
@[expose]
def size (P : GAP G) : ℕ := ∏ i, (P.bound i + 1)

/-- The multiple `t • P` of a progression multiplies the origin and the bound by `t`, so that its
points are the sums of `t` points of `P`. -/
instance : SMul ℕ (GAP G) where
  smul t P :=
    { dim := P.dim, origin := t • P.origin, hom := P.hom, step := P.step, bound := t • P.bound,
      hom_eq := P.hom_eq }

/-- The concatenation of two progressions adds the origins and concatenates the steps and the
bounds, so that its points are the sums of a point of `P` and a point of `Q`. -/
@[expose]
def append (P Q : GAP G) : GAP G :=
  { dim := P.dim + Q.dim, origin := P.origin + Q.origin, step := Fin.append P.step Q.step,
    bound := Fin.append P.bound Q.bound }

/-- The translate `c +ᵥ P` of a progression adds `c` to the origin. -/
instance : VAdd G (GAP G) where
  vadd c P := { P with origin := c + P.origin }

/-! ### Points -/

@[simp] lemma dim_nsmul (t : ℕ) (P : GAP G) : (t • P).dim = P.dim := rfl

@[simp]
lemma mem_toConvexProgression {P : GAP G} {x : G} : x ∈ P.toConvexProgression ↔ x ∈ P := .rfl

/-- The point of a GAP with prescribed coefficients, read through its homomorphism. -/
lemma eval_eq_hom (P : GAP G) (w : Fin P.dim → ℕ) :
    P.eval w = P.origin + P.hom fun i ↦ (w i : ℤ) := by
  simp [eval, stepsHom_apply]

/-- The points of a progression are the `P.eval w` with `w ≤ P.bound`. -/
lemma mem_iff_exists_eval {P : GAP G} {x : G} : x ∈ P ↔ ∃ w ≤ P.bound, P.eval w = x := by
  rw [← mem_toConvexProgression, ConvexProgression.mem_def, P.body_eq,
    ConvexBody.latticePoints_box]
  simp only [mem_Icc, Pi.le_def, Pi.zero_apply]
  constructor
  · rintro ⟨v, ⟨h₀, hv⟩, rfl⟩
    refine ⟨fun i ↦ (v i).toNat, fun i ↦ by grind [h₀ i, hv i], ?_⟩
    rw [eval_eq_hom]
    congr with i
    grind [h₀ i]
  · rintro ⟨w, hw, rfl⟩
    exact ⟨fun i ↦ (w i : ℤ), ⟨fun i ↦ by simp, fun i ↦ by grind [hw i]⟩, (eval_eq_hom ..).symm⟩

lemma origin_mem (P : GAP G) : P.origin ∈ P := mem_iff_exists_eval.2 ⟨0, zero_le, by simp [eval]⟩

/-! ### The size of a progression -/

private lemma card_latticePoints_body (P : GAP G) : #P.body.latticePoints = P.size := by
  rw [P.body_eq, ConvexBody.latticePoints_box]
  simp [size, Pi.card_Icc]

/-- A GAP `P` has at most `P.size` elements. -/
lemma card_le_size [DecidableEq G] (P : GAP G) : #P.toFinset ≤ P.size :=
  P.card_toFinset_le.trans_eq P.card_latticePoints_body

/-! ### Concatenation -/

@[simp] lemma dim_append (P Q : GAP G) : (append P Q).dim = P.dim + Q.dim := rfl

/-- The point of `GAP.append P Q` with coefficients `Fin.append u v` is the sum of the points of `P`
and of `Q` with coefficients `u` and `v`. -/
private lemma eval_append (P Q : GAP G) (u : Fin P.dim → ℕ) (v : Fin Q.dim → ℕ) :
    (append P Q).eval (Fin.append u v) = P.eval u + Q.eval v := by
  unfold append
  simp only [eval, Fin.sum_univ_add, Fin.append_left, Fin.append_right]
  exact add_add_add_comm _ _ _ _

/-- A function `w ≤ Fin.append a b` is the concatenation of functions below `a` and `b`. -/
private lemma le_append_iff {m n : ℕ} {a : Fin m → ℕ} {b : Fin n → ℕ} {w : Fin (m + n) → ℕ} :
    w ≤ Fin.append a b ↔ (fun i ↦ w (Fin.castAdd n i)) ≤ a ∧ (fun i ↦ w (Fin.natAdd m i)) ≤ b := by
  simp [Pi.le_def, Fin.forall_fin_add]

/-- The points of `GAP.append P Q` are the sums of a point of `P` and a point of `Q`. -/
lemma mem_append {P Q : GAP G} {x : G} : x ∈ append P Q ↔ ∃ y ∈ P, ∃ z ∈ Q, y + z = x := by
  simp only [mem_iff_exists_eval]
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨u, v, rfl⟩ : ∃ u v, Fin.append u v = w := ⟨_, _, Fin.append_castAdd_natAdd⟩
    obtain ⟨hu, hv⟩ := le_append_iff.1 hw
    exact ⟨_, ⟨u, by simpa using hu, rfl⟩, _, ⟨v, by simpa using hv, rfl⟩, (eval_append ..).symm⟩
  · rintro ⟨_, ⟨u, hu, rfl⟩, _, ⟨v, hv, rfl⟩, rfl⟩
    exact ⟨Fin.append u v, le_append_iff.2 (by simpa using ⟨hu, hv⟩), eval_append ..⟩

@[simp]
lemma toFinset_append [DecidableEq G] (P Q : GAP G) :
    (append P Q).toFinset = P.toFinset + Q.toFinset := by
  ext
  simp [mem_append, mem_add]

lemma size_append (P Q : GAP G) : (append P Q).size = P.size * Q.size := by
  unfold append
  simp [size, Fin.prod_univ_add]

/-! ### Multiples -/

private lemma mem_nsmul {t : ℕ} {P : GAP G} {x : G} :
    x ∈ t • P ↔ ∃ w ≤ t • P.bound, t • P.origin + ∑ i, w i • P.step i = x :=
  mem_iff_exists_eval

@[simp]
lemma mem_zero_nsmul {P : GAP G} {x : G} : x ∈ 0 • P ↔ x = 0 := by
  simp [mem_nsmul, eq_comm]

/-- The points of `(t + 1) • P` are the sums of a point of `t • P` and a point of `P`. -/
lemma mem_succ_nsmul {t : ℕ} {P : GAP G} {x : G} :
    x ∈ (t + 1) • P ↔ ∃ y ∈ t • P, ∃ z ∈ P, y + z = x := by
  simp only [mem_nsmul]
  simp only [mem_iff_exists_eval, eval]
  constructor
  · rintro ⟨w, hw : ∀ i, w i ≤ (t + 1) * P.bound i, rfl⟩
    refine ⟨_, ⟨fun i ↦ min (w i) (t * P.bound i), fun i ↦ min_le_right _ _, rfl⟩, _,
      ⟨fun i ↦ w i - min (w i) (t * P.bound i), fun i ↦ by grind [hw i], rfl⟩, ?_⟩
    rw [add_add_add_comm, ← succ_nsmul, ← sum_add_distrib]
    simp [← add_nsmul, Nat.add_sub_cancel' (min_le_left _ _)]
  · rintro ⟨_, ⟨u, hu : ∀ i, u i ≤ t * P.bound i, rfl⟩, _, ⟨v, hv, rfl⟩, rfl⟩
    refine ⟨u + v, fun i ↦ (by grind [Pi.add_apply, hu i, hv i] : _ ≤ (t + 1) * P.bound i), ?_⟩
    simp [succ_nsmul, add_nsmul, sum_add_distrib, add_add_add_comm]

/-- The points of `t • P` are the sums of `t` points of `P`. -/
@[simp]
lemma toFinset_nsmul [DecidableEq G] (t : ℕ) (P : GAP G) : (t • P).toFinset = t • P.toFinset := by
  induction t with
  | zero =>
    ext
    simp
  | succ t ih =>
    ext
    simp [mem_succ_nsmul, succ_nsmul, mem_add, ← ih]

/-! ### Translates -/

@[simp] lemma dim_vadd (c : G) (P : GAP G) : (c +ᵥ P).dim = P.dim := rfl

/-- The points of `c +ᵥ P` are the translates by `c` of the points of `P`. -/
lemma mem_vadd {c x : G} {P : GAP G} : x ∈ c +ᵥ P ↔ ∃ y ∈ P, c + y = x := by
  simp only [mem_iff_exists_eval]
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨_, ⟨w, hw, rfl⟩, (add_assoc ..).symm⟩
  · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    exact ⟨w, hw, add_assoc ..⟩

@[simp]
lemma toFinset_vadd [DecidableEq G] (c : G) (P : GAP G) : (c +ᵥ P).toFinset = c +ᵥ P.toFinset := by
  ext
  simp [mem_vadd, mem_vadd_finset]

/-! ### Progressions of subset sums -/

/-- The progression `P` with the step `a` of length `2` added in front. Its points are
`{0, a} + P`. -/
@[expose]
def cons (a : G) (P : GAP G) : GAP G :=
  { dim := P.dim + 1, origin := P.origin, step := Fin.cons a P.step, bound := Fin.cons 1 P.bound }

@[simp] lemma dim_cons (a : G) (P : GAP G) : (cons a P).dim = P.dim + 1 := rfl

private lemma eval_cons (a : G) (P : GAP G) (n : ℕ) (w : Fin P.dim → ℕ) :
    (cons a P).eval (Fin.cons n w) = n • a + P.eval w := by
  unfold cons
  simp only [eval, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
  exact add_left_comm _ _ _

/-- The points of `GAP.cons a P` are the points of `P` and their translates by `a`. -/
lemma mem_cons {a x : G} {P : GAP G} : x ∈ cons a P ↔ x ∈ P ∨ ∃ y ∈ P, a + y = x := by
  simp only [mem_iff_exists_eval]
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨n, u, rfl⟩ : ∃ (n : ℕ) (u : Fin P.dim → ℕ), Fin.cons n u = w :=
      ⟨_, _, Fin.cons_self_tail w⟩
    obtain ⟨hn, hu⟩ := Fin.cons_le_cons.1 hw
    rw [eval_cons]
    obtain rfl | rfl := Nat.le_one_iff_eq_zero_or_eq_one.1 hn
    · left
      exact ⟨u, hu, by simp⟩
    · right
      exact ⟨_, ⟨u, hu, rfl⟩, by simp⟩
  · rintro (⟨w, hw, rfl⟩ | ⟨_, ⟨w, hw, rfl⟩, rfl⟩)
    · exact ⟨Fin.cons 0 w, Fin.cons_le_cons.2 ⟨zero_le_one, hw⟩, (eval_cons ..).trans (by simp)⟩
    · exact ⟨Fin.cons 1 w, Fin.cons_le_cons.2 ⟨le_rfl, hw⟩, (eval_cons ..).trans (by simp)⟩

@[simp]
lemma toFinset_cons [DecidableEq G] (a : G) (P : GAP G) :
    (cons a P).toFinset = {0, a} + P.toFinset := by
  ext
  simp [mem_cons, mem_add]

lemma size_cons (a : G) (P : GAP G) : (cons a P).size = 2 * P.size := by
  unfold cons
  simp [size, Fin.prod_univ_succ]

/-! ### The progression of differences -/

/-- The progression with the steps of `P`, the bound `2 • P.bound` and the origin
`-∑ i, P.bound i • P.step i`. Its points are `P - P`. -/
@[expose]
def difference (P : GAP G) : GAP G :=
  { dim := P.dim, origin := -∑ i, P.bound i • P.step i, hom := P.hom, step := P.step,
    bound := 2 • P.bound, hom_eq := P.hom_eq }

@[simp] lemma dim_difference (P : GAP G) : P.difference.dim = P.dim := rfl

/-- The point of `P.difference` with coefficients `w` is the difference of the points of `P` with
coefficients `u` and `v` when `w + v = u + P.bound`. -/
private lemma eval_difference_eq_sub (P : GAP G) {u v w : Fin P.dim → ℕ}
    (h : ∀ i, w i + v i = u i + P.bound i) : P.difference.eval w = P.eval u - P.eval v := by
  unfold difference
  simp only [eval]
  rw [add_sub_add_left_eq_sub, neg_add_eq_sub, sub_eq_sub_iff_add_eq_add]
  simp only [← sum_add_distrib, ← add_nsmul, h]

/-- The points of `P.difference` are the differences of two points of `P`. -/
lemma mem_difference {P : GAP G} {x : G} : x ∈ P.difference ↔ ∃ y ∈ P, ∃ z ∈ P, y - z = x := by
  simp only [mem_iff_exists_eval]
  constructor
  · rintro ⟨w, hw : ∀ i, w i ≤ 2 * P.bound i, rfl⟩
    refine ⟨_, ⟨fun i ↦ min (w i) (P.bound i), fun i ↦ min_le_right _ _, rfl⟩, _,
      ⟨fun i ↦ P.bound i + min (w i) (P.bound i) - w i, fun i ↦ by grind, rfl⟩,
      (eval_difference_eq_sub P fun i ↦ by grind [hw i]).symm⟩
  · rintro ⟨_, ⟨u, hu, rfl⟩, _, ⟨v, hv, rfl⟩, rfl⟩
    exact ⟨u + (P.bound - v),
      fun i ↦ (by grind [Pi.add_apply, Pi.sub_apply, hu i, hv i] : _ ≤ 2 * P.bound i),
      eval_difference_eq_sub P fun i ↦ by grind [Pi.add_apply, Pi.sub_apply, hv i]⟩

@[simp]
lemma toFinset_difference [DecidableEq G] (P : GAP G) :
    P.difference.toFinset = P.toFinset - P.toFinset := by
  ext
  simp [mem_difference, mem_sub]

lemma size_difference_le (P : GAP G) : P.difference.size ≤ 2 ^ P.dim * P.size := by
  dsimp only [difference, size]
  rw [← Fin.prod_const, ← prod_mul_distrib]
  gcongr
  simp [mul_add]

/-! ### Properness and the lattice of relations -/

/-- The multiple `s • P` is `t`-proper if and only if `P` is `s * t`-proper. For `s = 2` and
`t = 1` this says that `2 • P` is `1`-proper, as in the condition `F₂` of Bilu and in Tao and Vu. -/
lemma proper_nsmul_iff (s : ℕ) (t : ℝ) (P : GAP G) : (s • P).Proper t ↔ P.Proper (s * t) := by
  rw [ConvexProgression.Proper, ConvexProgression.Proper, P.body_eq, mul_comm, mul_smul,
    ConvexBody.natCast_smul_box]
  rfl

/-- For a natural number `t`, a GAP `P` is `t`-proper if and only if `t • P` has `(t • P).size`
elements. -/
lemma proper_natCast_iff_card_eq_size [DecidableEq G] (t : ℕ) (P : GAP G) :
    P.Proper t ↔ #(t • P).toFinset = (t • P).size := by
  rw [← card_latticePoints_body, ← ConvexProgression.proper_one_iff_card_toFinset, proper_nsmul_iff,
    mul_one]

/-- The lattice of relations among the steps of a GAP: the kernel of its homomorphism, that is, the
integer vectors `v` with `∑ i, v i • P.step i = 0`. -/
@[expose]
def relations (P : GAP G) : AddSubgroup (Fin P.dim → ℤ) := P.hom.ker

/-- A homomorphism from `Fin d → ℤ` is injective on the box `0 ≤ v ≤ B` if and only if its kernel
contains no nonzero `v` with `|v i| ≤ B i` for all `i`. -/
private lemma _root_.AddMonoidHom.injOn_Icc_iff {d : ℕ} (f : (Fin d → ℤ) →+ G) (B : Fin d → ℕ) :
    Set.InjOn f (Set.Icc 0 fun i ↦ (B i : ℤ)) ↔ ∀ v ∈ f.ker, (∀ i, |v i| ≤ B i) → v = 0 := by
  simp only [Set.InjOn, Set.mem_Icc, Pi.le_def, Pi.zero_apply, AddMonoidHom.mem_ker]
  constructor
  · intro h v hv hvB
    have hpn : (fun i ↦ max (v i) 0) = fun i ↦ max (-v i) 0 := by
      refine h ?_ ?_ ?_
      · grind [abs_le]
      · grind [abs_le]
      · rw [← sub_eq_zero, ← map_sub, ← hv]
        congr with i
        grind [Pi.sub_apply]
    funext i
    rw [Pi.zero_apply]
    grind [congr_fun hpn i]
  · intro h v₁ hv₁ v₂ hv₂ he
    rw [← sub_eq_zero]
    apply h
    · rw [map_sub, he, sub_self]
    · grind [abs_le, Pi.sub_apply]

/-- For a natural number `t`, a progression is `t`-proper if and only if its steps admit no nonzero
relation `v` with `|v i| ≤ t * P.bound i` for all `i`. -/
lemma proper_natCast_iff_relations (t : ℕ) (P : GAP G) :
    P.Proper t ↔ ∀ v ∈ P.relations, (∀ i, |v i| ≤ t * P.bound i) → v = 0 := by
  rw [ConvexProgression.Proper, P.body_eq, ConvexBody.natCast_smul_box,
    ConvexBody.latticePoints_box, coe_Icc, AddMonoidHom.injOn_Icc_iff]
  rfl

/-- A translate of a progression is `t`-proper if and only if the progression is. -/
lemma proper_vadd_iff (t : ℝ) (c : G) (P : GAP G) : (c +ᵥ P).Proper t ↔ P.Proper t :=
  .rfl

end GAP

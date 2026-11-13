/-
Copyright (c) 2023 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
module

public import Mathlib.Probability.IdentDistrib

import AddCombi.Mathlib.Probability.IdentDistrib
import AddCombi.Mathlib.Probability.Independence.Basic
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.Positivity.Finset

/-!
# The Marcinkiewicz-Zygmund inequality

This file proves the Marcinkiewicz-Zygmund inequality.

The Marcinkiewicz-Zygmund inequality states that, if `X₁, ... Xₐ ∈ L^p` are independent random
variables of mean zero valued in some inner product space, then the `L^p`-norm of `X₁ + ... + Xₐ` is
at most `Cₚ` times the `L^(p/2)`-norm of `|X₁|² + ... + |Xₐ|²`, where `Cₚ` is a constant depending
on `p` alone.

## Notation

Throughout this file, `A ^^ n` denotes `A × ... × A` (with `n` factors). Formally, this is
`Fintype.piFinset fun _ : Fin n ↦ A`.

## Main declarations

* `marcinkiewicz_zygmund_symmetric_two_mul`: The Marcinkiewicz-Zygmund inequality for symmetric
  random variables and `p = 2 * m` an even natural number.
* `marcinkiewicz_zygmund_symmetric`: The Marcinkiewicz-Zygmund inequality for symmetric random
  variables and general `p ≥ 0`.
* `marcinkiewicz_zygmund`: The Marcinkiewicz-Zygmund inequality for random variables of mean zero
  and general `p ≥ 1`.
* `marcinkiewicz_zygmund_two_mul`: The Marcinkiewicz-Zygmund inequality for random variables of mean
  zero and `p = 2 * m` an even natural number.

## Proof strategy

We first prove the symmetric case for `p = 2 * m` by expanding out the `2m`-th power and noticing
that most terms cancel out.

The symmetric case for general `p` is then obtained from the even case by nesting of Lp norms:
Multiplying each `Xᵢ` by an independent uniform random sign `εᵢ` does not change the distribution
of `(X₁, ..., Xₐ)`. Conditionally on the `Xᵢ`, Lyapunov's inequality and the even case with
`2 * m ≥ p` bound the `L^p`-norm in the `εᵢ` of `ε₁X₁ + ... + εₐXₐ` by
`⌈p / 2⌉ ^ (1 / 2) * (|X₁|² + ... + |Xₐ|²) ^ (1 / 2)`.

The mean zero case is then obtained from the symmetric case by symmetrisation.
-/

public section

open Finset Fintype Function Nat MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal

variable {ι Ω E : Type*} {A : Finset ι} {m n : ℕ} [MeasurableSpace Ω] {μ : Measure Ω}
  [IsFiniteMeasure μ] [mE : MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [BorelSpace E] [SecondCountableTopology E] {X : ι → Ω → E}

local notation:70 A:70 " ^^ " n:71 => Fintype.piFinset fun _ : Fin n ↦ A

/-- Counting families of pairs of indices `i₁, ..., iₘ, j₁, ..., jₘ` according to how many times
each index appears among them. -/
private lemma sum_piFinset_product_eq_sum_piAntidiag [DecidableEq ι] (A : Finset ι) (m : ℕ)
    (g : (ι → ℕ) → ℝ) :
    ∑ I ∈ A ×ˢ A ^^ m, g (fun i ↦ #{k | (I k).1 = i} + #{k | (I k).2 = i}) =
      ∑ w ∈ piAntidiag A (2 * m), multinomial A w * g w := by
  -- We compare the coefficients of `(∑ i ∈ A, xᵢ) ^ (2 * m)` expanded in two different ways.
  let x (i : ι) : AddMonoidAlgebra ℕ (ι → ℕ) := .single (Pi.single i 1) 1
  let Φ : AddMonoidAlgebra ℕ (ι → ℕ) →+ ℝ :=
    (Finsupp.liftAddHom fun w ↦ (AddMonoidHom.mulRight (g w)).comp (Nat.castAddMonoidHom ℝ)).comp
      AddMonoidAlgebra.coeffAddEquiv.toAddMonoidHom
  have hΦ w k : Φ (.single w k) = k * g w := by simp [Φ, AddMonoidAlgebra.coeff_single]
  have lhs (I : Fin m → ι × ι) : ∏ k, x (I k).1 * x (I k).2 =
      .single (fun i ↦ #{k | (I k).1 = i} + #{k | (I k).2 = i}) 1 := by
    simp only [x, AddMonoidAlgebra.single_mul_single, AddMonoidAlgebra.prod_single, mul_one,
      prod_const_one]
    congr 1
    ext i
    simp [Finset.sum_apply, Pi.single_apply, sum_add_distrib, eq_comm]
  have rhs w (hw : w ∈ piAntidiag A (2 * m)) : ∏ i ∈ A, x i ^ w i = .single w 1 := by
    simp only [x, AddMonoidAlgebra.single_pow, AddMonoidAlgebra.prod_single, one_pow,
      prod_const_one]
    congr 1
    ext j
    rw [mem_piAntidiag] at hw
    have : w j = if j ∈ A then w j else 0 := by
      split_ifs with hj
      · rfl
      · exact not_imp_comm.1 (hw.2 j) hj
    rw [this]
    simp [Finset.sum_apply, Pi.single_apply]
  have key := congr(Φ $(calc
    ∑ I ∈ A ×ˢ A ^^ m, ∏ k, x (I k).1 * x (I k).2 = (∑ i ∈ A, x i) ^ (2 * m) := by
      rw [pow_mul, sq, Finset.sum_mul_sum, ← sum_product', Finset.sum_pow']
    _ = ∑ w ∈ piAntidiag A (2 * m), multinomial A w • ∏ i ∈ A, x i ^ w i := by
      simp_rw [sum_pow_eq_sum_piAntidiag, nsmul_eq_mul]))
  simp only [map_sum, map_nsmul, lhs, hΦ, Nat.cast_one, one_mul] at key
  rw [key]
  refine sum_congr rfl fun w hw ↦ ?_
  rw [rhs w hw, hΦ, nsmul_eq_mul, Nat.cast_one, one_mul]

omit mE [InnerProductSpace ℝ E] [BorelSpace E] [SecondCountableTopology E] in
private lemma integrable_sum_norm_sq_pow (memLp_X : ∀ i ∈ A, MemLp (X i) (2 * m) μ) :
    Integrable (fun ω ↦ (∑ i ∈ A, ‖X i ω‖ ^ 2) ^ m) μ := by
  have : MemLp (fun ω ↦ ∑ i ∈ A, ‖X i ω‖ ^ 2) m μ := by
    refine memLp_finsetSum A fun i hi ↦ ?_
    have := (memLp_X i hi).norm_rpow_div 2
    simp only [ENNReal.toReal_ofNat, Real.rpow_two] at this
    rwa [mul_comm, ENNReal.mul_div_cancel_right two_ne_zero ENNReal.ofNat_ne_top] at this
  refine this.integrable_norm_pow'.congr (.of_forall fun ω ↦ ?_)
  simp only [Real.norm_of_nonneg (Finset.sum_nonneg fun i _ ↦ sq_nonneg ‖X i ω‖)]

omit mE [InnerProductSpace ℝ E] [BorelSpace E] [SecondCountableTopology E] in
private lemma integrable_prod_norm_pow [DecidableEq ι] (memLp_X : ∀ i ∈ A, MemLp (X i) (2 * m) μ)
    {w : ι → ℕ} (hw : w ∈ piAntidiag A m) :
    Integrable (fun ω ↦ ∏ i ∈ A, ‖X i ω‖ ^ (2 * w i)) μ := by
  refine (integrable_sum_norm_sq_pow memLp_X).mono'
    (Finset.aestronglyMeasurable_fun_prod _ fun i hi ↦
      (memLp_X i hi).aestronglyMeasurable.norm.pow _)
    (.of_forall fun ω ↦ ?_)
  rw [Real.norm_of_nonneg (by positivity), sum_pow_eq_sum_piAntidiag]
  simp_rw [pow_mul]
  refine le_trans ?_ (single_le_sum (f := fun w ↦ (multinomial A w : ℝ) *
    ∏ i ∈ A, (‖X i ω‖ ^ 2) ^ w i) (fun w _ ↦ by positivity) hw)
  exact le_mul_of_one_le_left (by positivity) (mod_cast multinomial_pos ..)

omit mE [InnerProductSpace ℝ E] [BorelSpace E] [SecondCountableTopology E] in
private lemma integrable_sum_norm_sq_rpow {p : ℝ≥0} (memLp_X : ∀ i ∈ A, MemLp (X i) p μ) :
    Integrable (fun ω ↦ (∑ i ∈ A, ‖X i ω‖ ^ 2) ^ (p / 2 : ℝ)) μ := by
  have : MemLp (fun ω ↦ ∑ i ∈ A, ‖X i ω‖ ^ 2) (p / 2) μ := by
    refine memLp_finsetSum A fun i hi ↦ ?_
    simpa [Real.rpow_two] using (memLp_X i hi).norm_rpow_div 2
  refine this.integrable_norm_rpow'.congr (.of_forall fun ω ↦ ?_)
  simp [Real.norm_of_nonneg (Finset.sum_nonneg fun i _ ↦ sq_nonneg ‖X i ω‖)]

private lemma rpow_add_le_two_rpow_mul_add_rpow {a b q : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hq : 0 ≤ q) : (a + b) ^ q ≤ 2 ^ (max q 1 - 1) * (a ^ q + b ^ q) := by
  obtain hq₁ | hq₁ := le_total q 1
  · simpa [max_eq_right hq₁] using Real.rpow_add_le_add_rpow ha hb hq hq₁
  · lift a to ℝ≥0 using ha
    lift b to ℝ≥0 using hb
    rw [max_eq_left hq₁]
    exact_mod_cast NNReal.rpow_add_le_mul_rpow_add_rpow a b hq₁

/-- The constant appearing in the Marcinkiewicz-Zygmund inequality for symmetric random variables.
-/
noncomputable def marcinkiewiczZygmundSymmConst (p : ℝ≥0) : ℝ := ⌈p / 2⌉₊ ^ (p / 2 : ℝ)

lemma marcinkiewiczZygmundSymmConst_nonneg (p : ℝ≥0) : 0 ≤ marcinkiewiczZygmundSymmConst p := by
  unfold marcinkiewiczZygmundSymmConst; positivity

lemma marcinkiewiczZygmundSymmConst_two_mul (m : ℕ) :
    marcinkiewiczZygmundSymmConst (2 * m) = m ^ m := by
  simp [marcinkiewiczZygmundSymmConst, ← Real.rpow_natCast]

/-- The **Marcinkiewicz-Zygmund inequality** for symmetric random variables and `p = 2 * m` an even
natural number, with a slightly better constant than `marcinkiewicz_zygmund_two_mul`. -/
theorem marcinkiewicz_zygmund_symmetric_two_mul (iIndepFun_X : iIndepFun X μ)
    (identDistrib_neg_X : ∀ i, IdentDistrib (X i) (-X i) μ μ)
    (memLp_X : ∀ i ∈ A, MemLp (X i) (2 * m) μ) :
    ∫ ω, ‖∑ i ∈ A, X i ω‖ ^ (2 * m) ∂μ ≤
      marcinkiewiczZygmundSymmConst (2 * m) * ∫ ω, (∑ i ∈ A, ‖X i ω‖ ^ 2) ^ m ∂μ := by
  have : DecidableEq ι := Classical.decEq _
  -- Turn the `L^p` assumption on the `X i` into various integrability conditions.
  have integrable_prod_norm_X I (hI : I ∈ A ×ˢ A ^^ m) :
    Integrable (fun ω ↦ ∏ k, ‖X (I k).1 ω‖ * ‖X (I k).2 ω‖) μ := by
    obtain rfl | hm := eq_or_ne m 0
    · simp
    simp_rw [Finset.prod_mul_distrib]
    rw [← memLp_one_iff_integrable]
    have aux : (∑ _k : Fin m, (2 * (m : ℝ≥0∞))⁻¹)⁻¹ = 2 := by
      rw [ENNReal.mul_inv (a := 2) (.inl <| by norm_num) (.inl <| by norm_num)]
      simp [hm, mul_comm, ← mul_assoc, ENNReal.mul_inv_cancel]
    refine .fun_mul (p := 2) (q := 2) ?_ ?_ <;>
    · rw [← aux]
      exact MemLp.fun_prod fun k _ ↦ (memLp_X _ <| by simp_all).norm
  have integrable_prod_inner_X I (hI : I ∈ A ×ˢ A ^^ m) :
    Integrable (fun ω ↦ ∏ k, inner ℝ (X (I k).1 ω) (X (I k).2 ω)) μ := by
    have hIA k : (I k).1 ∈ A ∧ (I k).2 ∈ A := by simpa using mem_piFinset.1 hI k
    refine (integrable_prod_norm_X I hI).mono'
      (Finset.aestronglyMeasurable_fun_prod _ fun k _ ↦
        (memLp_X _ (hIA k).1).aestronglyMeasurable.inner
          (memLp_X _ (hIA k).2).aestronglyMeasurable) (.of_forall fun ω ↦ ?_)
    simp only [norm_prod, Real.norm_eq_abs]
    gcongr with k
    exact abs_real_inner_le_norm ..
  -- Call a family of indices `i₁, ..., iₙ, j₁, ..., jₙ` *even* if each `i ∈ A` appears an even
  -- number of times among the `2n` indices.
  let EvenIndex (I : Fin m → ι × ι) : Prop :=
    ∀ i ∈ A, Even (#{k | (I k).1 = i} + #{k | (I k).2 = i})
  -- Now, let the calculation begin...
  calc
    ∫ ω, ‖∑ i ∈ A, X i ω‖ ^ (2 * m) ∂μ
    -- Expand out the power of the sum into a sum over families of indices
    -- `i₁, ..., iₙ, j₁, ..., jₙ` of `∏ k, ⟨X iₖ, X jₖ⟩`. Push the integral inside the sum.
    _ = ∑ I ∈ A ×ˢ A ^^ m, ∫ ω, ∏ k, inner ℝ (X (I k).1 ω) (X (I k).2 ω) ∂μ := by
      simp_rw [pow_mul, ← real_inner_self_eq_norm_sq, sum_inner, inner_sum, ← sum_product',
        Finset.sum_pow', integral_finsetSum _ integrable_prod_inner_X]
    -- Show that the terms coming from odd families of indices `i₁, ..., iₙ, j₁, ..., jₙ` integrate
    -- to zero.
    _ = ∑ I ∈ A ×ˢ A ^^ m with EvenIndex I, ∫ ω, ∏ k, inner ℝ (X (I k).1 ω) (X (I k).2 ω) ∂μ := by
      rw [Finset.sum_filter_of_ne]
      -- Assume that `I = (i₁, ..., iₙ, j₁, ..., jₙ)` is an odd family.
      -- Say `i` appears an odd number of times in it.
      rintro I hI hI' i hi
      contrapose hI'
      replace hI' : Odd (#{k | (I k).1 = i} + #{k | (I k).2 = i}) := by simpa using hI'
      -- Let `Y` be the family of random variables `X` where `X i` has been replaced by `-X i`.
      let Y : ι → Ω → E := update X i (-X i)
      -- By the assumption that `X i` is symmetric, we get that `X j` and `Y j` are identically
      -- distributed for all `j`.
      have identDistrib_X_Y j : IdentDistrib (X j) (Y j) μ μ := by
        obtain rfl | hji := eq_or_ne j i
        · simpa [Y] using identDistrib_neg_X _
        · simpa [Y, hji] using .refl (identDistrib_neg_X _).aemeasurable_fst
      -- To show that `𝔼 ∏ k, ⟨X iₖ, X jₖ⟩ = 0`, we will show
      -- `𝔼 ∏ k, ⟨X iₖ, X jₖ⟩ = 𝔼 ∏ k, ⟨Y iₖ, Y jₖ⟩ = -𝔼 ∏ k, ⟨X iₖ, X jₖ⟩`.
      rw [← neg_eq_self, ← integral_neg, eq_comm]
      calc
        -- `𝔼 ∏ k, ⟨X iₖ, X jₖ⟩ = 𝔼 ∏ k, ⟨Y iₖ, Y jₖ⟩` because `𝔼 ∏ k, ⟨X iₖ, X jₖ⟩` and
        -- `∏ k, ⟨Y iₖ, Y jₖ⟩` are identically distributed.
        ∫ ω, ∏ k, inner ℝ (X (I k).1 ω) (X (I k).2 ω) ∂μ
        _ = ∫ ω, ∏ k, inner ℝ (Y (I k).1 ω) (Y (I k).2 ω) ∂μ := by
          refine IdentDistrib.integral_eq ?_
          have hIA k : (I k).1 ∈ A ∧ (I k).2 ∈ A := by simpa using mem_piFinset.1 hI k
          -- `Y` is an independent family, since it is obtained from `X` by applying a measurable
          -- function to each coordinate.
          have iIndepFun_Y : iIndepFun Y μ := by
            have : Y = fun j ↦ (if j = i then (-·) else id) ∘ X j := by
              ext j ω; obtain rfl | hji := eq_or_ne j i <;> simp [Y, *]
            rw [this]
            exact iIndepFun_X.comp _ fun j ↦ by split_ifs <;> fun_prop
          -- Hence the vectors `(X j)_{j ∈ A}` and `(Y j)_{j ∈ A}` are identically distributed.
          exact (IdentDistrib.pi (fun j : A ↦ identDistrib_X_Y j)
            (iIndepFun_X.precomp Subtype.val_injective)
            (iIndepFun_Y.precomp Subtype.val_injective)).comp
              (u := fun x : A → E ↦ ∏ k, inner ℝ (x ⟨(I k).1, (hIA k).1⟩) (x ⟨(I k).2, (hIA k).2⟩))
              (Finset.measurable_fun_prod _ fun k _ ↦
                (measurable_pi_apply _).inner (measurable_pi_apply _))
        -- `𝔼 ∏ k, ⟨Y iₖ, Y jₖ⟩ = -𝔼 ∏ k, ⟨X iₖ, X jₖ⟩` by the assumption that `i` appears an odd
        -- number of times in `I`.
        _ = ∫ ω, -∏ k, inner ℝ (X (I k).1 ω) (X (I k).2 ω) ∂μ := by
          congr with ω
          calc
            ∏ k, inner ℝ (Y (I k).1 ω) (Y (I k).2 ω)
            _ = ∏ k, (if (I k).1 = i then -1 else 1) * (if (I k).2 = i then -1 else 1) *
                inner ℝ (X (I k).1 ω) (X (I k).2 ω) := by
              congr! with k; split_ifs with hk₁ hk₂ hk₂ <;> simp [hk₁, hk₂, Y]
            _ = -∏ k, inner ℝ (X (I k).1 ω) (X (I k).2 ω) := by
              rw [prod_mul_distrib, prod_mul_distrib]
              simp [prod_ite, ← pow_add, hI']
    -- Upper bound the sum by its absolute value and push the absolute value inside.
    _ ≤ |∑ I ∈ A ×ˢ A ^^ m with EvenIndex I, ∫ ω, ∏ k, inner ℝ (X (I k).1 ω) (X (I k).2 ω) ∂μ| :=
      le_abs_self _
    _ ≤ ∑ I ∈ A ×ˢ A ^^ m with EvenIndex I, |∫ ω, ∏ k, inner ℝ (X (I k).1 ω) (X (I k).2 ω) ∂μ| :=
      abs_sum_le_sum_abs ..
    _ ≤ ∑ I ∈ A ×ˢ A ^^ m with EvenIndex I, ∫ ω, |∏ k, inner ℝ (X (I k).1 ω) (X (I k).2 ω)| ∂μ := by
      gcongr with I; exact abs_integral_le_integral_abs
    _ = ∑ I ∈ A ×ˢ A ^^ m with EvenIndex I, ∫ ω, ∏ k, |inner ℝ (X (I k).1 ω) (X (I k).2 ω)| ∂μ := by
      simp_rw [abs_prod]
    -- Finish pushing the absolute value inside using Cauchy-Schwarz.
    _ ≤ ∑ I ∈ A ×ˢ A ^^ m with EvenIndex I, ∫ ω, ∏ k, ‖X (I k).1 ω‖ * ‖X (I k).2 ω‖ ∂μ := by
      gcongr with I hI
      · simpa [abs_prod] using (integrable_prod_inner_X I <| filter_subset _ _ hI).abs
      · exact integrable_prod_norm_X I <| filter_subset _ _ hI
      rintro ω
      dsimp
      gcongr with k
      exact abs_real_inner_le_norm ..
    -- Rewrite the sum of `𝔼 ∏ k, ‖X iₖ ω‖ * ‖X jₖ ω‖` over even families of indices
    -- `i₁, ..., iₙ, j₁, ..., jₙ` into the sum over `w₁ + ... + wₐ = m` of
    -- `(2m choose 2w₁, ..., 2wₐ) * 𝔼 ∏ i, ‖X i‖ ^ wᵢ`.
    _ = ∑ I ∈ A ×ˢ A ^^ m with EvenIndex I,
          ∫ ω, ∏ i ∈ A, ‖X i ω‖ ^ (#{k | (I k).1 = i} + #{k | (I k).2 = i}) ∂μ := by
      congr! with I hI ω
      simp only [mem_filter, mem_piFinset, mem_product, forall_and] at hI
      simp_rw [pow_add, prod_mul_distrib, ← prod_const]
      rw [prod_fiberwise_of_maps_to', prod_fiberwise_of_maps_to']
      · simpa using hI.1.2
      · simpa using hI.1.1
    _ = ∑ w ∈ piAntidiag A (2 * m) with ∀ i ∈ A, 2 ∣ w i,
          multinomial A w * ∫ ω, ∏ i ∈ A, ‖X i ω‖ ^ w i ∂μ := by
      rw [sum_filter, sum_filter]
      convert sum_piFinset_product_eq_sum_piAntidiag A m
        (fun w ↦ if ∀ i ∈ A, 2 ∣ w i then ∫ ω, ∏ i ∈ A, ‖X i ω‖ ^ w i ∂μ else 0) using 2 with I hI
      · simp [EvenIndex, even_iff_two_dvd]
      · simp [mul_ite]
    _ = ∑ w ∈ (piAntidiag A m).map
          ⟨(2 • ·), fun _ _ h ↦ funext fun i ↦ mul_right_injective₀ two_ne_zero (congr_fun h i)⟩,
        multinomial A w * ∫ ω, ∏ i ∈ A, ‖X i ω‖ ^ w i ∂μ := by
      rw [map_nsmul_piAntidiag _ _ two_ne_zero]
    _ = ∑ w ∈ piAntidiag A m, multinomial A (2 • w) * ∫ ω, ∏ i ∈ A, ‖X i ω‖ ^ (2 * w i) ∂μ := by
      simp
    -- Use the fact that `(2m choose 2w₁, ..., 2wₐ) ≤ m ^ m * (m choose w₁, ..., wₐ)`.
    _ ≤ ∑ w ∈ piAntidiag A m, marcinkiewiczZygmundSymmConst (2 * m) * multinomial A w *
          ∫ ω, ∏ i ∈ A, ‖X i ω‖ ^ (2 * w i) ∂μ := by
      gcongr with w hw
      calc
        (multinomial A (2 • w) : ℝ)
        _ ≤ ((∑ i ∈ A, w i) ^ ∑ i ∈ A, w i) * multinomial A w :=
          mod_cast multinomial_two_mul_le_mul_multinomial
        _ = marcinkiewiczZygmundSymmConst (2 * m) * multinomial A w := by
          simp [(mem_piAntidiag.1 hw).1, marcinkiewiczZygmundSymmConst_two_mul]
    -- Put the sum back together.
    _ = marcinkiewiczZygmundSymmConst (2 * m) * ∫ ω, (∑ i ∈ A, ‖X i ω‖ ^ 2) ^ m ∂μ := by
      simp_rw [sum_pow_eq_sum_piAntidiag, ← pow_mul, ← integral_const_mul, mul_sum, ← mul_assoc]
      rw [integral_finsetSum]
      rintro w hw
      exact .const_mul (integrable_prod_norm_pow memLp_X hw) _

/-- The **Marcinkiewicz-Zygmund inequality** for symmetric random variables, with a slightly better
constant than `marcinkiewicz_zygmund`. -/
theorem marcinkiewicz_zygmund_symmetric {p : ℝ≥0} (iIndepFun_X : iIndepFun X μ)
    (identDistrib_neg_X : ∀ i, IdentDistrib (X i) (-X i) μ μ)
    (memLp_X : ∀ i ∈ A, MemLp (X i) p μ) :
    ∫ ω, ‖∑ i ∈ A, X i ω‖ ^ (p : ℝ) ∂μ ≤
      marcinkiewiczZygmundSymmConst p * ∫ ω, (∑ i ∈ A, ‖X i ω‖ ^ 2) ^ (p / 2 : ℝ) ∂μ := by
  have := iIndepFun_X.isProbabilityMeasure
  obtain rfl | hp := eq_or_ne p 0
  · simp [marcinkiewiczZygmundSymmConst]
  -- Let `m` be the smallest natural number such that `p ≤ 2 * m`.
  set m := ⌈p / 2⌉₊ with hm
  have hm₀ : 0 < m := Nat.ceil_pos.2 (by positivity)
  have hpm : (p : ℝ) / (2 * m) ≤ 1 := by
    have : (p : ℝ) / 2 ≤ m := mod_cast Nat.le_ceil (p / 2)
    rw [div_le_one (by positivity)]
    linarith
  -- Let `ε : A → Bool` be a family of independent uniform random signs, under the measure `ν`.
  let σ (b : Bool) : ℝ := if b then 1 else -1
  have abs_σ b : |σ b| = 1 := by cases b <;> simp [σ]
  have σ_not b : σ (!b) = -σ b := by cases b <;> simp [σ]
  let ν₀ : Measure Bool := (2⁻¹ : ℝ≥0∞) • (.dirac true + .dirac false)
  have : IsProbabilityMeasure ν₀ := ⟨by simp [ν₀, ENNReal.inv_two_add_inv_two]⟩
  have map_not_ν₀ : ν₀.map not = ν₀ := by
    simp only [ν₀]
    rw [Measure.map_smul, Measure.map_add _ _ (measurable_of_finite not),
      Measure.map_dirac' (measurable_of_finite not), Measure.map_dirac' (measurable_of_finite not),
      Bool.not_true, Bool.not_false, add_comm]
    exact (measurable_of_finite _).aemeasurable
  let ν : Measure (A → Bool) := .pi fun _ ↦ ν₀
  -- For fixed vectors `xᵢ`, the `L^p` norm of `ε₁x₁ + ... + εₐxₐ` is bounded using Lyapunov's
  -- inequality and the Marcinkiewicz-Zygmund inequality for `2 * m`.
  have key (x : A → E) :
      ∫ ε, ‖∑ i, σ (ε i) • x i‖ ^ (p : ℝ) ∂ν ≤
        m ^ (p / 2 : ℝ) * (∑ i, ‖x i‖ ^ 2) ^ (p / 2 : ℝ) := by
    have iIndepFun_εx : iIndepFun (fun i ε ↦ σ (ε i) • x i) ν :=
      iIndepFun_pi (X := fun i b ↦ σ b • x i) fun _ ↦ (measurable_of_finite _).aemeasurable
    have identDistrib_neg_εx i :
        IdentDistrib (fun ε ↦ σ (ε i) • x i) (-fun ε ↦ σ (ε i) • x i) ν ν := by
      have : MeasurePreserving (fun ε : A → Bool ↦ fun j ↦ !ε j) ν ν :=
        measurePreserving_pi (f := fun _ ↦ not) _ _ fun _ ↦ ⟨measurable_of_finite _, map_not_ν₀⟩
      convert this.identDistrib (X := fun ε ↦ σ (ε i) • x i)
        (measurable_of_finite _).aemeasurable using 1
      ext ε
      simp [σ_not]
    let f (ε : A → Bool) := ‖∑ i, σ (ε i) • x i‖ ^ (2 * m)
    calc
      ∫ ε, ‖∑ i, σ (ε i) • x i‖ ^ (p : ℝ) ∂ν
      _ = ∫ ε, f ε ^ ((p : ℝ) / (2 * m)) ∂ν := by
        congr with ε
        simp only [f]
        rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
        push_cast
        field_simp
      _ ≤ (∫ ε, f ε ∂ν) ^ ((p : ℝ) / (2 * m)) :=
        (concaveOn_rpow (by positivity) hpm).le_map_integral
          (continuousOn_id.rpow_const fun _ _ ↦ .inr (by positivity)) isClosed_Ici
          (.of_forall fun _ ↦ Set.mem_Ici.2 (by positivity)) .of_finite .of_finite
      _ ≤ (marcinkiewiczZygmundSymmConst (2 * m) *
            ∫ ε, (∑ i, ‖σ (ε i) • x i‖ ^ 2) ^ m ∂ν) ^ ((p : ℝ) / (2 * m)) := by
        gcongr
        exact marcinkiewicz_zygmund_symmetric_two_mul (A := .univ) iIndepFun_εx
            identDistrib_neg_εx fun _ _ ↦ .of_discrete
      _ = m ^ (p / 2 : ℝ) * (∑ i, ‖x i‖ ^ 2) ^ (p / 2 : ℝ) := by
        simp only [marcinkiewiczZygmundSymmConst_two_mul, norm_smul, Real.norm_eq_abs, abs_σ,
          one_mul, integral_const, probReal_univ, one_smul]
        rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast,
          ← Real.rpow_natCast _ m, ← Real.rpow_mul (by positivity), ← Real.rpow_mul (by positivity)]
        congr 2 <;> field_simp
  -- Multiplying the `Xᵢ` by fixed signs does not change their joint distribution.
  have integral_eq (ε : A → Bool) :
      ∫ ω, ‖∑ i ∈ A, X i ω‖ ^ (p : ℝ) ∂μ = ∫ ω, ‖∑ i, σ (ε i) • X i ω‖ ^ (p : ℝ) ∂μ := by
    have identDistrib_X (i : A) : IdentDistrib (X i) ((σ (ε i) • ·) ∘ X i) μ μ := by
      cases h : ε i
      · simpa [h, σ, Function.comp_def, Pi.neg_def] using identDistrib_neg_X i
      · simpa [h, σ, Function.comp_def] using
          IdentDistrib.refl (identDistrib_neg_X i).aemeasurable_fst
    have iIndepFun_X' := iIndepFun_X.precomp (g := ((↑) : A → ι)) Subtype.val_injective
    simp_rw [← Finset.sum_coe_sort A]
    exact ((IdentDistrib.pi identDistrib_X iIndepFun_X'
      (iIndepFun_X'.comp _ fun i ↦ measurable_const_smul _)).comp
        (u := fun x : A → E ↦ ‖∑ i, x i‖ ^ (p : ℝ)) (by fun_prop)).integral_eq
  have integrable_εX (ε : A → Bool) :
      Integrable (fun ω ↦ ‖∑ i, σ (ε i) • X i ω‖ ^ (p : ℝ)) μ := by
    have : MemLp (fun ω ↦ ∑ i : A, σ (ε i) • X i ω) p μ :=
      memLp_finsetSum _ fun i _ ↦ (memLp_X i i.2).const_smul _
    simpa using this.integrable_norm_rpow'
  calc
    ∫ ω, ‖∑ i ∈ A, X i ω‖ ^ (p : ℝ) ∂μ
    _ = ∫ ε, ∫ ω, ‖∑ i, σ (ε i) • X i ω‖ ^ (p : ℝ) ∂μ ∂ν := by
      simp_rw [← integral_eq, integral_const, probReal_univ, one_smul]
    _ = ∫ ω, ∫ ε, ‖∑ i, σ (ε i) • X i ω‖ ^ (p : ℝ) ∂ν ∂μ := by
      classical
      have (g : (A → Bool) → ℝ) : ∫ ε, g ε ∂ν = ∑ ε, ν.real {ε} • g ε := integral_fintype .of_finite
      simp_rw [this]
      rw [integral_finsetSum]
      · simp_rw [integral_smul]
      · exact fun ε _ ↦ (integrable_εX ε).smul (ν.real {ε})
    _ ≤ ∫ ω, m ^ (p / 2 : ℝ) * (∑ i ∈ A, ‖X i ω‖ ^ 2) ^ (p / 2 : ℝ) ∂μ := by
      refine integral_mono_of_nonneg (.of_forall fun _ ↦ integral_nonneg fun _ ↦ by positivity)
        ((integrable_sum_norm_sq_rpow memLp_X).const_mul _) (.of_forall fun ω ↦ ?_)
      simpa [← Finset.sum_coe_sort A] using key fun i ↦ X i ω
    _ = marcinkiewiczZygmundSymmConst p * ∫ ω, (∑ i ∈ A, ‖X i ω‖ ^ 2) ^ (p / 2 : ℝ) ∂μ := by
      rw [integral_const_mul]; rfl

/-- The constant appearing in the Marcinkiewicz-Zygmund inequality for random variables with zero
mean. -/
noncomputable def marcinkiewiczZygmundConst (p : ℝ≥0) : ℝ :=
  2 ^ (p / 2 + max (p / 2 : ℝ) 1) * marcinkiewiczZygmundSymmConst p

/-- The **Marcinkiewicz-Zygmund inequality** for random variables with zero mean.

For symmetric random variables, `marcinkiewicz_zygmund_symmetric` provides a better constant. -/
theorem marcinkiewicz_zygmund [CompleteSpace E] {p : ℝ≥0} (hp : 1 ≤ p) (iIndepFun_X : iIndepFun X μ)
    (integral_X : ∀ i, ∫ ω, X i ω ∂μ = 0) (memLp_X : ∀ i ∈ A, MemLp (X i) p μ) :
    ∫ ω, ‖∑ i ∈ A, X i ω‖ ^ (p : ℝ) ∂μ ≤
      marcinkiewiczZygmundConst p * ∫ ω, (∑ i ∈ A, ‖X i ω‖ ^ 2) ^ (p / 2 : ℝ) ∂μ := by
  have := iIndepFun_X.isProbabilityMeasure
  have one_le_p : (1 : ℝ≥0∞) ≤ p := mod_cast hp
  -- Restrict to the finite index type `A`.
  let Z (i : A) : Ω → E := X i
  have memLp_Z (i : A) : MemLp (Z i) p μ := memLp_X i i.2
  -- Symmetrise: Let `Z' i (ω, ω') = Z i ω - Z i ω'`.
  let Z' (i : A) (ω : Ω × Ω) : E := Z i ω.1 - Z i ω.2
  have memLp_Z' (i : A) : MemLp (Z' i) p (μ.prod μ) :=
    ((memLp_Z i).comp_fst μ).sub ((memLp_Z i).comp_snd μ)
  have memLp_sum_Z' : MemLp (fun ω ↦ ∑ i, Z' i ω) p (μ.prod μ) :=
    memLp_finsetSum _ fun i _ ↦ memLp_Z' i
  have iIndepFun_Z' : iIndepFun Z' (μ.prod μ) := by
    have h := iIndepFun_X.precomp (g := ((↑) : A → ι)) Subtype.val_injective
    have hZ i := (memLp_Z i).aestronglyMeasurable.aemeasurable
    exact (iIndepFun.prodMap hZ hZ h h).comp (fun _ p ↦ p.1 - p.2) fun _ ↦ measurable_sub
  have identDistrib_neg_Z' (i : A) : IdentDistrib (Z' i) (-Z' i) (μ.prod μ) (μ.prod μ) := by
    convert Measure.measurePreserving_swap.identDistrib
      (memLp_Z' i).aestronglyMeasurable.aemeasurable using 1
    ext ω
    simp [Z']
  -- `x ↦ ‖x‖ ^ p` is convex since `p ≥ 1`.
  have convexOn_norm_rpow : ConvexOn ℝ .univ fun x : E ↦ ‖x‖ ^ (p : ℝ) := by
    refine ⟨convex_univ, fun x _ y _ a b ha hb hab ↦ ?_⟩
    calc
      ‖a • x + b • y‖ ^ (p : ℝ)
      _ ≤ (a * ‖x‖ + b * ‖y‖) ^ (p : ℝ) := by
        gcongr
        refine (norm_add_le _ _).trans_eq ?_
        rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
      _ ≤ a * ‖x‖ ^ (p : ℝ) + b * ‖y‖ ^ (p : ℝ) :=
        (convexOn_rpow (mod_cast hp)).2 (norm_nonneg x) (norm_nonneg y) ha hb hab
  let S ω := ∑ i ∈ A, ‖X i ω‖ ^ 2
  have integrable_S : Integrable (fun ω ↦ S ω ^ (p / 2 : ℝ)) μ :=
    integrable_sum_norm_sq_rpow memLp_X
  calc
    ∫ ω, ‖∑ i ∈ A, X i ω‖ ^ (p : ℝ) ∂μ
    _ = ∫ ω, ‖∑ i, Z i ω‖ ^ (p : ℝ) ∂μ := by congr with ω; rw [← Finset.sum_coe_sort A]
    -- By Jensen's inequality, `‖∑ i, Z i ω‖ ^ p ≤ 𝔼_ω' ‖∑ i, Z' i (ω, ω')‖ ^ p`.
    _ ≤ ∫ ω, ‖∑ i, Z' i ω‖ ^ (p : ℝ) ∂μ.prod μ := by
      have := memLp_sum_Z'.integrable_norm_rpow'
      simp only [ENNReal.coe_toReal] at this
      rw [integral_prod _ this]
      refine integral_mono_of_nonneg (.of_forall fun _ ↦ by positivity)
        this.integral_prod_left (.of_forall fun ω ↦ ?_)
      have memLp_sum : MemLp (fun ω' ↦ ∑ i, Z' i (ω, ω')) p μ :=
        memLp_finsetSum _ fun i _ ↦ (memLp_const (Z i ω)).sub (memLp_Z i)
      have integral_sum : ∫ ω', ∑ i, Z' i (ω, ω') ∂μ = ∑ i, Z i ω := by
        simp only [Z']
        rw [integral_finsetSum _ fun i _ ↦ ?_]
        · refine sum_congr rfl fun i _ ↦ ?_
          rw [integral_sub (integrable_const _) ((memLp_Z i).integrable one_le_p)]
          simp [Z, integral_X]
        · exact (integrable_const _).sub ((memLp_Z i).integrable one_le_p)
      calc
        ‖∑ i, Z i ω‖ ^ (p : ℝ)
        _ = ‖∫ ω', ∑ i, Z' i (ω, ω') ∂μ‖ ^ (p : ℝ) := by rw [integral_sum]
        _ ≤ ∫ ω', ‖∑ i, Z' i (ω, ω')‖ ^ (p : ℝ) ∂μ :=
          convexOn_norm_rpow.map_integral_le (g := fun x : E ↦ ‖x‖ ^ (p : ℝ))
            (continuous_norm.rpow_const fun _ ↦ .inr p.2).continuousOn isClosed_univ
            (.of_forall fun _ ↦ Set.mem_univ _) (memLp_sum.integrable one_le_p)
            (by simpa [Function.comp_def] using memLp_sum.integrable_norm_rpow')
    -- Apply the Marcinkiewicz-Zygmund inequality for symmetric random variables to `Z'`.
    _ ≤ marcinkiewiczZygmundSymmConst p * ∫ ω, (∑ i, ‖Z' i ω‖ ^ 2) ^ (p / 2 : ℝ) ∂μ.prod μ :=
      marcinkiewicz_zygmund_symmetric iIndepFun_Z' identDistrib_neg_Z' fun i _ ↦ memLp_Z' i
    -- Bound `‖Z' i (ω, ω')‖ ^ 2` by `2 * (‖Z i ω‖ ^ 2 + ‖Z i ω'‖ ^ 2)`.
    _ ≤ marcinkiewiczZygmundSymmConst p * ∫ ω, 2 ^ (p / 2 : ℝ) * 2 ^ (max (p / 2 : ℝ) 1 - 1) *
          (S ω.1 ^ (p / 2 : ℝ) + S ω.2 ^ (p / 2 : ℝ)) ∂μ.prod μ := by
      refine mul_le_mul_of_nonneg_left ?_ (marcinkiewiczZygmundSymmConst_nonneg _)
      refine integral_mono_of_nonneg (.of_forall fun _ ↦ by positivity)
        (((integrable_S.comp_fst μ).add (integrable_S.comp_snd μ)).const_mul _)
        (.of_forall fun ω ↦ ?_)
      calc
        (∑ i, ‖Z' i ω‖ ^ 2) ^ (p / 2 : ℝ)
        _ ≤ (2 * (S ω.1 + S ω.2)) ^ (p / 2 : ℝ) := by
          gcongr
          rw [mul_add, mul_sum, mul_sum, ← sum_add_distrib, ← Finset.sum_coe_sort A]
          gcongr with i
          calc
            ‖Z' i ω‖ ^ 2
            _ ≤ (‖X i ω.1‖ + ‖X i ω.2‖) ^ 2 := by gcongr; exact norm_sub_le ..
            _ ≤ 2 * ‖X i ω.1‖ ^ 2 + 2 * ‖X i ω.2‖ ^ 2 := by
              rw [← mul_add]
              exact (add_pow_le (norm_nonneg _) (norm_nonneg _) 2).trans_eq (by norm_num)
        _ = 2 ^ (p / 2 : ℝ) * (S ω.1 + S ω.2) ^ (p / 2 : ℝ) :=
          Real.mul_rpow (by norm_num) (by positivity)
        _ ≤ 2 ^ (p / 2 : ℝ) *
              (2 ^ (max (p / 2 : ℝ) 1 - 1) * (S ω.1 ^ (p / 2 : ℝ) + S ω.2 ^ (p / 2 : ℝ))) := by
          gcongr
          exact rpow_add_le_two_rpow_mul_add_rpow (by positivity) (by positivity) (by positivity)
        _ = _ := by ring
    _ = marcinkiewiczZygmundConst p * ∫ ω, (∑ i ∈ A, ‖X i ω‖ ^ 2) ^ (p / 2 : ℝ) ∂μ := by
      rw [integral_const_mul, integral_add (integrable_S.comp_fst μ) (integrable_S.comp_snd μ),
        integral_fun_fst (f := fun ω ↦ S ω ^ (p / 2 : ℝ)),
        integral_fun_snd (f := fun ω ↦ S ω ^ (p / 2 : ℝ))]
      simp only [probReal_univ, one_smul, marcinkiewiczZygmundConst, S]
      rw [Real.rpow_add two_pos, Real.rpow_sub_one two_ne_zero]
      ring

/-- The **Marcinkiewicz-Zygmund inequality** for random variables with zero mean and `p = 2 * m` an
even natural number.

For symmetric random variables, `marcinkiewicz_zygmund_symmetric_two_mul` provides a better
constant. -/
theorem marcinkiewicz_zygmund_two_mul [CompleteSpace E] (iIndepFun_X : iIndepFun X μ)
    (integral_X : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (memLp_X : ∀ i ∈ A, MemLp (X i) (2 * m) μ) :
    ∫ ω, ‖∑ i ∈ A, X i ω‖ ^ (2 * m) ∂μ ≤
      marcinkiewiczZygmundConst (2 * m) * ∫ ω, (∑ i ∈ A, ‖X i ω‖ ^ 2) ^ m ∂μ := by
  have := iIndepFun_X.isProbabilityMeasure
  obtain rfl | hm := eq_or_ne m 0
  · norm_num [marcinkiewiczZygmundConst, marcinkiewiczZygmundSymmConst]
  have := marcinkiewicz_zygmund (p := 2 * m) (by norm_cast; omega) iIndepFun_X integral_X
    (by simpa using memLp_X)
  have h₁ : ((2 * m : ℝ≥0) : ℝ) = (2 * m : ℕ) := by push_cast; rfl
  have h₂ : ((2 * m : ℝ≥0) : ℝ) / 2 = m := by push_cast; ring
  rw [h₂] at this
  simpa only [h₁, Real.rpow_natCast] using this

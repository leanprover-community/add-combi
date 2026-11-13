/-
Copyright (c) 2026 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import AddCombi.VCDim.SetFamily.Defs
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

import AddCombi.Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic.Positivity.Finset

/-!
# Haussler's packing lemma

This file proves Haussler's packing lemma in a probability space, which is the statement
that a family of measurable sets of VC dimension at most `d` whose pairwise symmetric differences
all have measure at least `ε` has size at most `(16 * exp 1 / ε ^ 2) ^ d`.

## Main statements

* `SetFamily.exists_card_le_injOn_inter`: Dimension reduction. A finite family of measurable sets
  that are pairwise `ε`-far in measure has pairwise distinct traces on some set of
  `O(ε⁻¹ log #𝓕)` points.
* `SetFamily.haussler_packing`: Haussler's packing lemma (with a weaker exponent) over a
  probability space.

## Implementation notes

Vershynin proves dimension reduction with Hoeffding's inequality, which needs `n ≳ ε⁻⁴ log #𝓕`
samples (with `ε` the `L²` distance). We only need two sets to have distinct traces on the sample,
not to stay `ε / 2`-separated. So we bound the probability that the traces agree directly by
`(1 - μ (A ∆ B)) ^ n`, which dispenses us needing a concentration inequality.

## References

* *Sphere Packing Numbers for Subsets of the Boolean n-Cube with Bounded
  Vapnik-Chervonenkis Dimension*, David Haussler
* Write-up by Thomas Bloom: http://www.thomasbloom.org/notes/vc.html
* *High-Dimensional Probability*, Roman Vershynin, 2nd edition, Section 8.3.5
-/

public section

open Fintype MeasureTheory Metric Real
open scoped Finset NNReal symmDiff

namespace SetFamily
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {𝓕 : Finset (Set Ω)} {d n : ℕ} {ε : ℝ}

/-- **Dimension reduction**, after Lemma 8.3.14 in Vershynin's *High-Dimensional Probability*.

If `𝓕` is a finite family of measurable sets which are pairwise `ε`-far apart in measure (namely
`ε ≤ μ (A ∆ B)` for distinct `A, B ∈ 𝓕`) and `n` is such that `#𝓕 ^ 2 ≤ exp (ε * n)`, then there
are at most `n` points of `Ω` on which all the sets in `𝓕` have pairwise distinct traces.

This is proved by sampling `n` points independently according to `μ`: two distinct sets
`A, B ∈ 𝓕` have the same trace on the sample with probability `(1 - μ (A ∆ B)) ^ n ≤ exp (-ε * n)`,
so a union bound shows that with positive probability no two sets of `𝓕` have the same trace. -/
lemma exists_card_le_injOn_inter (h𝓕 : ∀ A ∈ 𝓕, MeasurableSet A)
    (hsep : (𝓕 : Set (Set Ω)).Pairwise fun A B ↦ ε ≤ μ.real (A ∆ B))
    (hn : (#𝓕 : ℝ) ^ 2 ≤ exp (ε * n)) :
    ∃ S : Finset Ω, #S ≤ n ∧ Set.InjOn ((S : Set Ω) ∩ ·) 𝓕 := by
  classical
  obtain rfl | h𝓕₀ := 𝓕.eq_empty_or_nonempty
  · exact ⟨∅, by simp⟩
  -- The set of samples on which two distinct sets of `𝓕` have the same trace.
  set bad : Set (Fin n → Ω) := ⋃ p ∈ 𝓕.offDiag, Set.univ.pi fun _ ↦ (p.1 ∆ p.2)ᶜ with hbad
  have hbad_lt := calc
      (Measure.pi fun _ : Fin n ↦ μ).real bad
        ≤ ∑ p ∈ 𝓕.offDiag, (Measure.pi fun _ : Fin n ↦ μ).real
            (Set.univ.pi fun _ ↦ (p.1 ∆ p.2)ᶜ) := measureReal_biUnion_finset_le ..
      _ ≤ ∑ p ∈ 𝓕.offDiag, exp (-(ε * n)) := by
        gcongr with p hp
        obtain ⟨hA, hB, hAB⟩ := Finset.mem_offDiag.1 hp
        rw [Measure.real, Measure.pi_pi, ENNReal.toReal_prod, Finset.prod_const, Finset.card_univ,
          Fintype.card_fin, ← Measure.real, ← neg_mul,
          probReal_compl_eq_one_sub ((h𝓕 _ hA).symmDiff (h𝓕 _ hB)), mul_comm, exp_nat_mul]
        gcongr
        · linarith [measureReal_le_one (μ := μ) (s := p.1 ∆ p.2)]
        · linarith [hsep hA hB hAB, one_sub_le_exp_neg ε]
      _ = #𝓕.offDiag * exp (-(ε * n)) := by simp
      _ < #𝓕 ^ 2 * exp (-(ε * n)) := by
        grw [Finset.offDiag_card, sq, Nat.sub_lt, Nat.cast_mul] <;> positivity
      _ ≤ 1 := by rwa [exp_neg, ← div_eq_mul_inv, div_le_one (by positivity)]
  obtain ⟨x, hx⟩ : ∃ x, x ∉ bad := by
    by_contra! h
    rw [Set.eq_univ_of_forall h, probReal_univ] at hbad_lt
    exact hbad_lt.false
  refine ⟨Finset.univ.image x, Finset.card_image_le.trans (by simp), ?_⟩
  rintro A hA B hB hAB
  by_contra hne
  refine hx <| Set.mem_biUnion (x := (A, B)) (by simpa [Finset.mem_offDiag] using ⟨hA, hB, hne⟩) ?_
  simp only [Set.mem_pi, Set.mem_univ, Set.mem_compl_iff, forall_const, Set.mem_symmDiff]
  intro i hi
  have := congr(x i ∈ $hAB)
  simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_inter_iff,
    Set.mem_range, exists_apply_eq_apply, true_and] at this
  simp_all

/-- **Haussler's packing lemma** for probability spaces, after Theorem 8.3.13 in Vershynin's
*High-Dimensional Probability*.

If `𝓕` is a finite family of measurable sets of VC dimension at most `d` which are pairwise
`ε`-far apart in measure (namely `ε ≤ μ (A ∆ B)` for distinct `A, B ∈ 𝓕`), then
`#𝓕 ≤ (16 * exp 1 / ε ^ 2) ^ d`.

Note that `μ (A ∆ B) = ‖𝟭_A - 𝟭_B‖_{L¹(μ)} = ‖𝟭_A - 𝟭_B‖_{L²(μ)} ^ 2`. -/
theorem haussler_packing (hd : HasVCDimLE d (𝓕 : Set (Set Ω))) (h𝓕 : ∀ A ∈ 𝓕, MeasurableSet A)
    (hε₀ : 0 < ε) (hε₁ : ε ≤ 1) (hsep : (𝓕 : Set (Set Ω)).Pairwise fun A B ↦ ε ≤ μ.real (A ∆ B)) :
    #𝓕 ≤ (16 * exp 1 / ε ^ 2) ^ d := by
  obtain h𝓕₀ | h𝓕₀ := 𝓕.eq_empty_or_nonempty
  · simp only [h𝓕₀, Finset.card_empty, CharP.cast_eq_zero]
    positivity
  set N := #𝓕 with hN
  have hN₀ : (0 : ℝ) < N := by positivity
  set L := log N with hL
  have hL₀ : 0 ≤ L := log_nonneg <| Nat.one_le_cast.2 h𝓕₀.card_pos
  -- Sample `n ≈ 2 * log N / ε` points.
  set n := ⌈2 * L / ε⌉₊ + d with hn
  have hn' : n ≤ 2 * L / ε + 1 + d := by
    rw [hn]; push_cast; linarith [Nat.ceil_lt_add_one (a := 2 * L / ε) (by positivity)]
  obtain ⟨S, hSn, hinj⟩ := exists_card_le_injOn_inter h𝓕 hsep (n := n) <| calc
    N ^ 2 = exp (2 * L) := by rw [exp_ofNat_mul, hL, exp_log hN₀]
    _ ≤ exp (ε * n) := by grw [hn, Nat.cast_add, ← Nat.le_ceil]; field_simp; grw [← hε₀]; simp
  -- By the Sauer-Shelah lemma, `N ≤ (e * n / d) ^ d`.
  have hNn := calc
      (N : ℝ) = (((S : Set Ω) ∩ ·) '' 𝓕).ncard := by
        rw [hinj.ncard_image, Set.ncard_coe_finset]
      _ ≤ vcGrowth n (𝓕 : Set (Set Ω)) := by
        gcongr
        exact ncard_image_inter_le_vcGrowth S.finite_toSet (by rwa [Set.ncard_coe_finset])
      _ ≤ (exp 1 * (n / d)) ^ d := by grw [hd.vcGrowth_le_exp (by lia)]; field_simp; rfl
  obtain rfl | hd₀ := d.eq_zero_or_pos
  · simpa using hNn
  have hd₀' : (0 : ℝ) < d := by positivity
  -- It remains to show `N ≤ (e * n / d) ^ d` for `N`.
  have hNL := calc
    N ≤ (exp 1 * (2 / ε * (L / d + 1))) ^ d := by
      grw [hNn, hn']; gcongr; field_simp; grw [hε₁]; simp [mul_add, add_assoc]; norm_cast; lia
    _ = (2 * exp 1 / ε * (L / d + 1)) ^ d := by ring
  have hlog : log (L / d + 1) ≤ log 2 + (L / d - 1) / 2 := by
    have := log_le_sub_one_of_pos (x := (L / d + 1) / 2) (by positivity)
    rw [log_div (by positivity) (by norm_num)] at this
    linarith
  rw [← exp_log hN₀, ← hL, ← exp_log (x := (_ / _) ^ d) (by positivity), exp_le_exp, log_pow,
    log_div (by positivity) (by positivity), log_mul (by norm_num) (by positivity), log_exp,
    log_pow, show (16 : ℝ) = 2 ^ 4 by norm_num, log_pow]
  replace hNL := log_le_log hN₀ hNL
  rw [← hL, log_pow, log_mul (by positivity) (by positivity), log_div (by positivity) hε₀.ne',
    log_mul (by norm_num) (by positivity), log_exp] at hNL
  have : d * (L / d) = L := mul_div_cancel₀ _ hd₀'.ne'
  push_cast
  nlinarith

end SetFamily

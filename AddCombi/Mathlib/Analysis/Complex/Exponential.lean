module

public import Mathlib.Analysis.Complex.Exponential

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.Positivity

public section

open Real

variable {d m : ℕ}

private lemma sum_choose_mul_pow_le_add_one_pow {t : ℝ} (ht : 0 ≤ t) (hdm : d ≤ m) :
    ∑ i ∈ .range (d + 1), (m.choose i : ℝ) * t ^ i ≤ (1 + t) ^ m :=
  calc ∑ i ∈ .range (d + 1), (m.choose i : ℝ) * t ^ i
      ≤ ∑ i ∈ .range (m + 1), (m.choose i : ℝ) * t ^ i := by gcongr with i hi
    _ = (1 + t) ^ m := by
        rw [add_comm 1 t, add_pow]
        congr! 1 with i
        ring

lemma one_add_div_pow_le_exp {x : ℝ} (hx : -m ≤ x) : (1 + x / m) ^ m ≤ exp x := by
  simpa [neg_div, sub_neg_eq_add]
    using Real.one_sub_div_pow_le_exp_neg (n := m) (t := -x) (neg_le.1 hx)

private lemma sum_choose_le_mul_sum_choose_mul_pow (hd : (0 : ℝ) < d) (hm : (0 : ℝ) < m)
    (hdm : (d : ℝ) ≤ m) :
    ∑ i ∈ .range (d + 1), (m.choose i : ℝ) ≤
      (m / d : ℝ) ^ d * ∑ i ∈ .range (d + 1), (m.choose i : ℝ) * (d / m : ℝ) ^ i := by
  calc ∑ i ∈ .range (d + 1), (m.choose i : ℝ)
    _ = ∑ i ∈ .range (d + 1), (m.choose i : ℝ) * (d / m : ℝ) ^ i * (m / d : ℝ) ^ i :=
        Finset.sum_congr rfl fun i _ ↦ by
          rw [mul_assoc, ← mul_pow, show (d : ℝ) / m * (m / d) = 1 by field_simp, one_pow,
            mul_one]
    _ ≤ ∑ i ∈ .range (d + 1), (m.choose i : ℝ) * (d / m : ℝ) ^ i * (m / d : ℝ) ^ d := by
        gcongr with i hi
        · exact (one_le_div₀ hd).2 hdm
        · exact Finset.mem_range_succ_iff.1 hi
    _ = (m / d : ℝ) ^ d * ∑ i ∈ .range (d + 1), (m.choose i : ℝ) * (d / m : ℝ) ^ i := by
        rw [← Finset.sum_mul, mul_comm]

/-- For `0 < d ≤ m`, the number of subsets of size at most `d` of an `m`-element set,
`∑ i ≤ d, m.choose i`, is at most `(exp 1 / d * m) ^ d`. -/
lemma sum_choose_le_exp_pow (d m : ℕ) (hd : 0 < d) (hdm : d ≤ m) :
    ∑ i ∈ .range (d + 1), (m.choose i : ℝ) ≤ (exp 1 / d * m) ^ d := by
  have hm : (0 : ℝ) < m := mod_cast hd.trans_le hdm
  calc ∑ i ∈ .range (d + 1), (m.choose i : ℝ)
      ≤ (m / d : ℝ) ^ d * ∑ i ∈ .range (d + 1), (m.choose i : ℝ) * (d / m : ℝ) ^ i :=
        sum_choose_le_mul_sum_choose_mul_pow (mod_cast hd) hm (mod_cast hdm)
    _ ≤ (m / d : ℝ) ^ d * (1 + d / m : ℝ) ^ m := by
        gcongr; exact sum_choose_mul_pow_le_add_one_pow (by positivity) hdm
    _ ≤ (m / d : ℝ) ^ d * exp 1 ^ d := by
        gcongr
        simpa [← Real.exp_nat_mul]
          using one_add_div_pow_le_exp ((neg_nonpos.2 m.cast_nonneg).trans d.cast_nonneg)
    _ = (exp 1 / d * m) ^ d := by ring

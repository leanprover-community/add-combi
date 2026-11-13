module

public import Mathlib.Analysis.Complex.Exponential

public section

namespace Complex

lemma exp_ofNat_mul (x : ℂ) (n : ℕ) [n.AtLeastTwo] : exp (ofNat(n) * x) = exp x ^ ofNat(n) :=
  exp_nat_mul x n

lemma exp_mul_ofNat (x : ℂ) (n : ℕ) [n.AtLeastTwo] : exp (x * ofNat(n)) = exp x ^ ofNat(n) := by
  rw [mul_comm, exp_ofNat_mul]

end Complex

namespace Real

lemma exp_ofNat_mul (x : ℝ) (n : ℕ) [n.AtLeastTwo] : exp (ofNat(n) * x) = exp x ^ ofNat(n) :=
  exp_nat_mul x n

lemma exp_mul_ofNat (x : ℝ) (n : ℕ) [n.AtLeastTwo] : exp (x * ofNat(n)) = exp x ^ ofNat(n) := by
  rw [mul_comm, exp_ofNat_mul]

end Real

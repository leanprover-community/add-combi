module

public import Mathlib.Combinatorics.Additive.ApproximateSubgroup

import AddCombi.Mathlib.Algebra.Group.Pointwise.Set.Basic
import AddCombi.Mathlib.Combinatorics.Additive.CovBySMul
import AddCombi.Mathlib.Data.Set.Prod

public section

variable {G : Type*} [Group G] {A B : Set G} {K L : ℝ} {m n : ℕ}

namespace IsApproximateSubgroup

@[to_additive]
lemma prod {H : Type*} [Group H] {B : Set H} (hA : IsApproximateSubgroup K A)
    (hB : IsApproximateSubgroup L B) : IsApproximateSubgroup (K * L) (A ×ˢ B) where
  one_mem := by simp [hA.one_mem, hB.one_mem]
  inv_eq_self := by simp [hA.inv_eq_self, hB.inv_eq_self]
  sq_covBySMul := by rw [Set.prod_pow]; exact hA.sq_covBySMul.prod hB.sq_covBySMul

open Set in
@[to_additive]
lemma pi {ι : Type*} {G : ι → Type*} {s : Finset ι} [∀ i, Group (G i)] {A : ∀ i, Set (G i)}
    {K : ι → ℝ} (hA : ∀ i ∈ s, IsApproximateSubgroup (K i) (A i)) :
    IsApproximateSubgroup (∏ i ∈ s, K i) (.pi s A) where
  one_mem i hi := (hA _ hi).one_mem
  inv_eq_self := by rw [inv_pi]; congr! with i hi; exact (hA _ hi).inv_eq_self
  sq_covBySMul := by rw [pi_pow _ _ two_ne_zero]; exact .pi fun i hi ↦ (hA i hi).sq_covBySMul

end IsApproximateSubgroup

module

public import Mathlib.Algebra.Order.BigOperators.Group.LocallyFinite
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Set.Finite.Powerset
public import AddCombi.Mathlib.Data.Set.Card
public import AddCombi.Mathlib.Order.Interval.Finset.Basic

public section

namespace Set
variable {α : Type*} {A : Set α}

/-- A finite set `A` has `∑ k ≤ d, A.ncard.choose k` subsets of size at most `d`. See also
`Set.ncard_powerset_ncard`. -/
lemma ncard_ofPred_ncard_le (hA : A.Finite) (d : ℕ) :
    {B ⊆ A | B.ncard ≤ d}.ncard = ∑ k ∈ .Iic d, A.ncard.choose k := by
  induction d with
  | zero => simpa using ncard_powerset_ncard hA 0
  | succ d ihd =>
    simp_rw [Nat.le_add_one_iff, and_or_left, ofPred_or]
    rw [ncard_union_eq ?_ ?_ ?_, ihd, ncard_powerset_ncard hA, Finset.sum_Iic_add_zero]
    · grind
    · exact hA.finite_subsets.subset fun _B hB ↦ hB.1
    · exact hA.finite_subsets.subset fun _B hB ↦ hB.1

end Set

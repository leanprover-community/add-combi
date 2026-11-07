module

public import Mathlib.Algebra.Order.BigOperators.Group.LocallyFinite
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Set.Finite.Powerset
public import AddCombi.Mathlib.Data.ENat.Choose
public import AddCombi.Mathlib.Data.Set.Card
public import AddCombi.Mathlib.Order.Interval.Finset.Basic

public section

namespace Set
variable {α : Type*} {A : Set α}

/-- A finite set `A` of size `n` has `∑ k ≤ d, n.choose k` subsets of size at most `d`. See also
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

/-- A finite set `A` has `A.encard.choose k` subsets of size `k`. -/
private lemma Finite.encard_powerset_encard (hA : A.Finite) (k : ℕ) :
    {B ⊆ A | B.encard = k}.encard = A.encard.choose k := by
  rw [← hA.cast_ncard_eq, ← ENat.natCast_choose, ← ncard_powerset_ncard hA,
    Finite.cast_ncard_eq ?_]
  · congr 1
    ext B
    exact and_congr_right fun hBA ↦ by rw [← (hA.subset hBA).cast_ncard_eq, Nat.cast_inj]
  · exact hA.finite_subsets.subset fun _B hB ↦ hB.1

/-- Every set `A`, finite or infinite, has `A.encard.choose k` subsets of size `k`. See also
`Set.ncard_powerset_ncard`. -/
lemma encard_powerset_encard (A : Set α) (k : ℕ) :
    {B ⊆ A | B.encard = k}.encard = A.encard.choose k := by
  refine le_antisymm (encard_le_iff_forall_finite_subset.2 fun ℬ hℬ hℬfin ↦ ?_)
    (ENat.choose_le_iff.2 fun m hm ↦ ?_)
  · calc ℬ.encard
        ≤ {B ⊆ ⋃₀ ℬ | B.encard = k}.encard :=
          encard_le_encard fun B hB ↦ ⟨subset_sUnion_of_mem hB, (hℬ hB).2⟩
      _ = (⋃₀ ℬ).encard.choose k :=
          (hℬfin.sUnion fun B hB ↦ finite_of_encard_eq_coe (hℬ hB).2).encard_powerset_encard k
      _ ≤ A.encard.choose k :=
          ENat.choose_le_choose (encard_le_encard (sUnion_subset fun B hB ↦ (hℬ hB).1))
  · obtain ⟨C, hCA, hC⟩ := exists_subset_encard_eq hm
    calc (m.choose k : ℕ∞)
        = C.encard.choose k := by rw [hC, ENat.natCast_choose]
      _ = {B ⊆ C | B.encard = k}.encard :=
          ((finite_of_encard_eq_coe hC).encard_powerset_encard k).symm
      _ ≤ {B ⊆ A | B.encard = k}.encard :=
          encard_le_encard fun B hB ↦ ⟨hB.1.trans hCA, hB.2⟩

/-- Every set `A`, finite or infinite, has `∑ k ≤ d, A.encard.choose k` subsets of size at most
`d`. See also `Set.ncard_ofPred_ncard_le`. -/
lemma encard_ofPred_encard_le (A : Set α) (d : ℕ) :
    {B ⊆ A | B.encard ≤ d}.encard = ∑ k ∈ .Iic d, A.encard.choose k := by
  induction d with
  | zero => simpa using encard_powerset_encard A 0
  | succ d ihd =>
    simp_rw [Nat.cast_add_one, le_iff_lt_or_eq (b := (d : ℕ∞) + 1),
      ENat.lt_add_one_iff (ENat.natCast_ne_top d), and_or_left, ofPred_or]
    rw [encard_union_eq ?_, ihd, ← Nat.cast_add_one, encard_powerset_encard,
      Finset.sum_Iic_add_zero]
    exact disjoint_left.2 fun B hB hB' ↦ (ENat.lt_add_one_iff (ENat.natCast_ne_top d)).2 le_rfl
      |>.not_ge (hB'.2 ▸ hB.2)

end Set

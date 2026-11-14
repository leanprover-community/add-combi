module

public import Mathlib.Data.Set.Card

public section

namespace Set
variable {α : Type*} {s : Set α}

/-- A set has `encard` at most `c` if and only if all its finite subsets do. -/
lemma encard_le_iff_forall_finite_subset {c : ℕ∞} :
    s.encard ≤ c ↔ ∀ u ⊆ s, u.Finite → u.encard ≤ c where
  mp h _ hus _ := (encard_le_encard hus).trans h
  mpr h := ENat.forall_natCast_le_iff_le.1 fun _ hm ↦ by
    obtain ⟨u, hus, hu⟩ := exists_subset_encard_eq hm
    exact hu ▸ h u hus (finite_of_encard_eq_coe hu)

end Set

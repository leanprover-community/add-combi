module

public import Mathlib.Data.Set.Image

public section

namespace Set
variable {α : Type*}

/-- `· ∪ s` is injective on sets disjoint from `s`. -/
lemma disjoint_injOn_union_left (s : Set α) : {t | Disjoint s t}.InjOn (· ∪ s) := by
  grind [InjOn, union_sdiff_cancel_right, Disjoint.symm]

/-- `· \ s` is injective on sets containing `s`. -/
lemma superset_injOn_sdiff (s : Set α) : {t | s ⊆ t}.InjOn (· \ s) := by
  grind [InjOn, sdiff_union_of_subset]

/-- `insert a` is injective on sets not containing `a`. -/
lemma insert_injOn_notMem (a : α) : InjOn (insert a) {s : Set α | a ∉ s} := by
  simpa [InjOn] using disjoint_injOn_union_left {a}

/-- `· \ {a}` is injective on sets containing `a`. -/
lemma sdiff_singleton_injOn_mem (a : α) : InjOn (· \ {a}) {s : Set α | a ∈ s} := by
  simpa [InjOn] using superset_injOn_sdiff {a}

end Set

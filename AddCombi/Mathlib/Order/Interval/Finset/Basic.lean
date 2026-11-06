module

public import Mathlib.Order.Interval.Finset.Basic

public section

namespace Finset
variable {α : Type*} [PartialOrder α] [LocallyFiniteOrderBot α]

@[to_additive (attr := simp)]
lemma Iic_one [One α] [IsBotOneClass α] : Iic (1 : α) = {1} := by ext; simp

end Finset

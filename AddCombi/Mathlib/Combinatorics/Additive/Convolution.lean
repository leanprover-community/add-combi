module

public import Mathlib.Combinatorics.Additive.Convolution

public section

open scoped Pointwise

namespace Finset
variable {G : Type*} [Group G] [DecidableEq G]

@[to_additive]
lemma card_inter_smul_inv (A B : Finset G) (x : G) : #(A ∩ (x • B⁻¹)) = A.convolution B x := by
  simp [card_inter_smul]

@[to_additive]
lemma card_mul_eq (A B : Finset G) (x : G) :
    #{ab ∈ A ×ˢ B | ab.1 * ab.2 = x} = A.convolution B x := rfl

@[to_additive]
lemma card_div_eq (A B : Finset G) (x : G) :
    #{ab ∈ A ×ˢ B | ab.1 / ab.2 = x} = A.convolution B⁻¹ x :=
  Finset.card_equiv ((Equiv.refl _).prodCongr (.inv _)) (by simp [div_eq_mul_inv])

variable [Fintype G]

@[to_additive (attr := simp) univ_addConvolution]
lemma univ_convolution (B : Finset G) (a : G) : univ.convolution B a = #B := by
  simp [← card_inter_smul_inv]

@[to_additive (attr := simp) addConvolution_univ]
lemma convolution_univ (A : Finset G) (a : G) : A.convolution univ a = #A := by
  simp [← card_inter_smul_inv]

end Finset

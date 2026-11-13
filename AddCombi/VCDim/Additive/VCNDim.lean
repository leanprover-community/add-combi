/-
Copyright (c) 2026 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import AddCombi.VCDim.Additive.Defs

/-!
# VCₙ dimension

This file defines VCₙ of a set in an abelian group.

We say a set `A` in an abelian group has VCₙ dimension at least `d` if one can find two sequences
`x` and `y` of elements indexed by `[n] × [d]` and `2 ^ [d]ⁿ` respectively such that
`y s * ∏ k, x (k, i k) ∈ A ↔ i ∈ s` for all `i ∈ [d]ⁿ`, `s ⊆ [d]ⁿ`.
-/

@[expose] public section

open scoped Pointwise

variable {G : Type*} [CommGroup G] {A B : Set G} {n d d' : ℕ}

variable (A n d) in
/-- A set `A` in an abelian group has VCₙ dimension at most `d` iff one cannot find two sequences
`x` and `y` of elements indexed by `[n] × [d + 1]` and `2 ^ [d + 1]ⁿ` respectively such that
`y s * ∏ k, x (k, i k) ∈ A ↔ i ∈ s` for all `i ∈ [d + 1]ⁿ`, `s ⊆ [d + 1]ⁿ`. -/
@[to_additive
/-- A set `A` in an abelian group has VCₙ dimension at most `d` iff one cannot find two sequences
`x` and `y` of elements indexed by `[n] × [d + 1]` and `2 ^ [d + 1]ⁿ` respectively such that
`y s + ∑ k, x (k, i k) ∈ A ↔ i ∈ s` for all `i ∈ [d + 1]ⁿ`, `s ⊆ [d + 1]ⁿ`. -/]
def HasMulVCNDimLE : Prop :=
  ∀ (x : Fin n → Fin (d + 1) → G) (y : Set (Fin n → Fin (d + 1)) → G),
    ¬ ∀ i s, y s * ∏ k, x k (i k) ∈ A ↔ i ∈ s

@[to_additive]
lemma HasMulVCNDimLE.mono (h : d ≤ d') (hd : HasMulVCNDimLE A n d) :
    HasMulVCNDimLE A n d' := by
  rintro x y hxy
  replace h : d + 1 ≤ d' + 1 := by lia
  exact hd (x · ∘ Fin.castLE h) (y ∘ Set.image (Fin.castLE h ∘ ·)) fun i s ↦
    (hxy ..).trans <| by simp [funext_iff]; simp [← funext_iff]

@[to_additive (attr := simp)]
lemma hasMulVCNDimLE_compl : HasMulVCNDimLE Aᶜ n d ↔ HasMulVCNDimLE A n d :=
  forall_congr' fun x ↦ (compl_involutive.toPerm.arrowCongr <| .refl _).forall_congr fun y ↦
    not_congr <| forall_congr' fun i ↦ compl_involutive.toPerm.forall_congr <| by simp; tauto

@[to_additive]
protected alias ⟨HasMulVCNDimLE.of_compl, HasMulVCNDimLE.compl⟩ := hasMulVCNDimLE_compl

@[to_additive (attr := simp)]
protected lemma HasMulVCNDimLE.empty : HasMulVCNDimLE (∅ : Set G) n d := by
  simpa [HasMulVCNDimLE] using ⟨default, .univ, by simp⟩

@[to_additive (attr := simp)]
protected lemma HasMulVCNDimLE.univ : HasMulVCNDimLE (.univ : Set G) n d := by
  simpa [HasMulVCNDimLE] using ⟨default, ∅, by simp⟩

@[to_additive (attr := simp)]
lemma hasMulVCNDimLE_zero : HasMulVCNDimLE A 0 d ↔ A = ∅ ∨ A = .univ where
  mp hA := by
    rw [Set.eq_univ_iff_forall]
    simp only [HasMulVCNDimLE, Finset.univ_eq_empty, Finset.prod_empty, mul_one,
      Fin.forall_fin_zero_pi, not_forall, forall_const] at hA
    contrapose! hA
    obtain ⟨⟨x, hx⟩, y, hy⟩ := hA
    refine ⟨fun s ↦ if s = ∅ then y else x, fun s ↦ ?_⟩
    beta_reduce
    split_ifs with hs
    · simp_all
    · rw [← ne_eq, ← Set.nonempty_iff_ne_empty] at hs
      obtain ⟨z, hz⟩ := hs
      simp_all [Subsingleton.elim z finZeroElim]
  mpr := by simp +contextual [or_imp]

@[to_additive (attr := simp) hasAddVCNDimLE_one]
lemma hasMulVCNDimLE_one : HasMulVCNDimLE A 1 d ↔ HasMulVCDimLE d A := by
  rw [hasMulVCDimLE_iff_forall_not]
  symm
  refine (Equiv.funUnique ..).symm.forall_congr fun x ↦
    ((Equiv.funUnique ..).setCongr.arrowCongr <| .refl _).symm.forall_congr fun y ↦
    not_congr <| (Equiv.funUnique ..).symm.forall_congr fun i ↦
    (Equiv.funUnique ..).setCongr.symm.forall_congr fun s ↦ ?_
  simp [Set.image_image, funext_iff]

/-
Copyright (c) 2026 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import AddCombi.VCDim.SetFamily.Defs
public import Mathlib.Algebra.Group.Action.Pointwise.Finset

/-!
# VC dimension of a set in a group

This file defines the VC dimension of a set in a group as the VC dimension of its set of translates.
We prove that sets of small VC dimension are closed under lattice operations.
-/

public section

open scoped Pointwise

variable {G : Type*} [Group G] {A B : Set G} {d d₁ d₂ : ℕ}

/-- A set `A` in a group `G` has VC dimension at most `d` if all the sets that `{t • A | t : G}`
shatters have size at most `d`. -/
@[expose, to_additive
/-- A set `A` in a group `G` has VC dimension at most `d` if all the sets that `{t +ᵥ A | t : G}`
shatters have size at most `d`. -/]
def HasMulVCDimLE (d : ℕ) (A : Set G) : Prop := HasVCDimLE d {t • A | t : G}

@[to_additive (attr := gcongr)]
lemma HasMulVCDimLE.mono (hd : d₁ ≤ d₂) (hA : HasMulVCDimLE d₁ A) : HasMulVCDimLE d₂ A :=
  HasVCDimLE.mono hd hA

@[to_additive]
lemma HasMulVCDimLE.inter (hA : HasMulVCDimLE d₁ A) (hB : HasMulVCDimLE d₂ B) :
    HasMulVCDimLE (5 * (d₁ + d₂)) (A ∩ B) := by
  refine (hA.infs hB).anti ?_
  rintro _ ⟨t, rfl⟩
  exact ⟨t • A, ⟨t, rfl⟩, t • B, ⟨t, rfl⟩, (Set.smul_set_inter ..).symm⟩

@[to_additive]
lemma HasMulVCDimLE.union (hA : HasMulVCDimLE d₁ A) (hB : HasMulVCDimLE d₂ B) :
    HasMulVCDimLE (5 * (d₁ + d₂)) (A ∪ B) := by
  refine (hA.sups hB).anti ?_
  rintro _ ⟨t, rfl⟩
  exact ⟨t • A, ⟨t, rfl⟩, t • B, ⟨t, rfl⟩, (Set.smul_set_union ..).symm⟩

@[to_additive (attr := simp)]
lemma hasMulVCDimLE_compl : HasMulVCDimLE d Aᶜ ↔ HasMulVCDimLE d A := by
  have : {t • Aᶜ | t : G} = (·ᶜ) '' {t • A | t : G} := by ext; simp [Set.smul_set_compl]
  rw [HasMulVCDimLE, HasMulVCDimLE, this, hasVCDimLE_image_compl]

@[to_additive] alias ⟨HasMulVCDimLE.of_compl, HasMulVCDimLE.compl⟩ := hasMulVCDimLE_compl

/-- A set `A` in a group has VC dimension at most `d` iff one cannot find two sequences `x` and `y`
of elements indexed by `[d + 1]` and `2 ^ [d + 1]` respectively such that `y s * x i ∈ A ↔ i ∈ s`
for all `i ∈ [d + 1]`, `s ⊆ [d + 1]`. -/
@[to_additive
/-- A set `A` in a group has VC dimension at most `d` iff one cannot find two sequences `x` and `y`
of elements indexed by `[d + 1]` and `2 ^ [d + 1]` respectively such that `y s + x i ∈ A ↔ i ∈ s`
for all `i ∈ [d + 1]`, `s ⊆ [d + 1]`. -/]
lemma hasMulVCDimLE_iff_forall_not :
    HasMulVCDimLE d A ↔ ∀ (x : Fin (d + 1) → G) (y : Set (Fin (d + 1)) → G),
      ¬ ∀ i s, y s * x i ∈ A ↔ i ∈ s where
  mp h x y hxy := by
    have hinj : x.Injective := fun j j' hjj' ↦ by
      simpa [eq_comm] using (hxy j' {j}).symm.trans <| (iff_of_eq <| by rw [hjj']).trans (hxy j {j})
    have hS : Shatters {t • A | t : G} (.range x) := fun B hB ↦ by
      refine ⟨(y (x ⁻¹' B))⁻¹ • A, ⟨_, rfl⟩, ?_⟩
      ext z
      simp only [Set.mem_inter_iff, Set.mem_range, Set.mem_smul_set_iff_inv_smul_mem, inv_inv,
        smul_eq_mul]
      constructor
      · rintro ⟨⟨j, rfl⟩, hj⟩
        exact (hxy j _).1 hj
      · intro hz
        obtain ⟨j, rfl⟩ := hB hz
        exact ⟨⟨j, rfl⟩, (hxy j _).2 hz⟩
    have := h (Set.finite_range _) hS
    rw [Set.ncard_range_of_injective hinj, Nat.card_eq_fintype_card, Fintype.card_fin] at this
    lia
  mpr h S hSfin hS := by
    by_contra! hlt
    obtain ⟨T, hTS, hT⟩ := Set.exists_subset_card_eq hlt
    have : Finite T := (hSfin.subset hTS).to_subtype
    let x : Fin (d + 1) → G := (↑) ∘ (Finite.equivFinOfCardEq (α := T) <| by simp [hT]).symm
    have hx : x.Injective := Subtype.val_injective.comp (Equiv.injective _)
    have (s : Set (Fin (d + 1))) : ∃ t : G, ∀ i, t * x i ∈ A ↔ i ∈ s := by
      obtain ⟨_, ⟨t, rfl⟩, hD⟩ := (hS.anti hTS) (show x '' s ⊆ T by
        rintro _ ⟨j, -, rfl⟩; exact Subtype.coe_prop _)
      refine ⟨t⁻¹, fun j ↦ ?_⟩
      simpa [Set.mem_smul_set_iff_inv_smul_mem, show x j ∈ T from Subtype.coe_prop _,
        hx.mem_set_image] using congr(x j ∈ $hD)
    choose y hy using this
    exact h x y fun i s ↦ hy s i

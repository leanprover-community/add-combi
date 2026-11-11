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

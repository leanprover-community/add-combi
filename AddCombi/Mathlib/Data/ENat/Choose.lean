/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
module

public import Mathlib.Data.ENat.Lattice
public import Mathlib.Data.Nat.Choose.Basic

/-!
# Binomial coefficients of extended natural numbers

This file defines `ENat.choose n k`, the supremum of the binomial coefficients `m.choose k` over the
natural numbers `m ≤ n`. It counts the `k`-element subsets of a set of size `n`, finite or
infinite: see `Set.encard_powerset_encard`.
-/

public section

namespace ENat
variable {m n : ℕ∞} {k : ℕ}

/-- The binomial coefficient of an extended natural number: `n.choose k` is the supremum of the
binomial coefficients `m.choose k` over the natural numbers `m ≤ n`. -/
noncomputable def choose (n : ℕ∞) (k : ℕ) : ℕ∞ := ⨆ (m : ℕ) (_ : (m : ℕ∞) ≤ n), (m.choose k : ℕ∞)

lemma choose_le_iff {c : ℕ∞} : n.choose k ≤ c ↔ ∀ m : ℕ, m ≤ n → m.choose k ≤ c := iSup₂_le_iff

lemma natCast_choose_le_choose {m : ℕ} (h : m ≤ n) : m.choose k ≤ n.choose k :=
  le_iSup₂_of_le m h le_rfl

@[gcongr]
lemma choose_le_choose (h : m ≤ n) : m.choose k ≤ n.choose k :=
  choose_le_iff.2 fun _ hm ↦ natCast_choose_le_choose (hm.trans h)

lemma choose_mono (k : ℕ) : Monotone (choose · k) := fun _ _ ↦ choose_le_choose

@[simp, norm_cast]
lemma natCast_choose (n k : ℕ) : (n.choose k : ℕ∞) = (n : ℕ∞).choose k :=
  le_antisymm (natCast_choose_le_choose le_rfl)
    (choose_le_iff.2 fun _ hm ↦ mod_cast Nat.choose_le_choose k (mod_cast hm))

@[simp]
lemma choose_zero_right (n : ℕ∞) : n.choose 0 = 1 :=
  le_antisymm (choose_le_iff.2 fun _ _ ↦ by simp)
    (by simpa using natCast_choose_le_choose (m := 0) (k := 0) (by simp))

@[simp]
lemma choose_one_right (n : ℕ∞) : n.choose 1 = n :=
  le_antisymm (choose_le_iff.2 fun _ hm ↦ by simpa using hm)
    (forall_natCast_le_iff_le.1 fun _ hm ↦ by simpa using natCast_choose_le_choose (k := 1) hm)

/-- An infinite set has infinitely many subsets of each positive size. -/
@[simp]
lemma top_choose (hk : k ≠ 0) : (⊤ : ℕ∞).choose k = ⊤ :=
  top_le_iff.1 <| forall_natCast_le_iff_le.1 fun a _ ↦
    le_trans (mod_cast le_trans (by rw [Nat.choose_succ_self_right]; lia)
        ((Nat.choose_le_choose a (by lia : a + 1 ≤ a + k)).trans_eq Nat.choose_symm_add))
      (natCast_choose_le_choose le_top)

/-- **Pascal's rule** for extended natural numbers. -/
lemma choose_succ_succ (n : ℕ∞) (k : ℕ) :
    (n + 1).choose (k + 1) = n.choose k + n.choose (k + 1) := by
  induction n using ENat.recTopCoe with
  | top => simp
  | coe n => exact_mod_cast Nat.choose_succ_succ n k

end ENat

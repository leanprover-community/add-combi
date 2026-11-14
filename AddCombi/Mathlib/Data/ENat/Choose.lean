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

This file defines `ENat.choose n k`, the binomial coefficient of an extended natural number. It
agrees with `Nat.choose` on natural numbers, and `⊤.choose k = ⊤` for `k ≠ 0`. Equivalently,
`n.choose k` is the supremum of the binomial coefficients `m.choose k` over the natural numbers
`m ≤ n`: see `ENat.choose_eq_iSup`. It counts the `k`-element subsets of a set of size `n`, finite
or infinite: see `Set.encard_powerset_encard`.
-/

public section

namespace ENat
variable {m n : ℕ∞} {k : ℕ}

/-- The binomial coefficient of an extended natural number: `n.choose 0 = 1`, and for `k ≠ 0`,
`n.choose k` is `Nat.choose` on natural numbers and `⊤` at `⊤`. See `ENat.choose_eq_iSup` for
`n.choose k` as a supremum of binomial coefficients of natural numbers. -/
@[expose]
def choose (n : ℕ∞) : (k : ℕ) → ℕ∞
  | 0 => 1
  | k + 1 => n.map (fun n ↦ n.choose (k + 1))

@[simp]
lemma choose_zero_right (n : ℕ∞) : n.choose 0 = 1 := rfl

@[simp, norm_cast]
lemma natCast_choose (n k : ℕ) : (n.choose k : ℕ∞) = (n : ℕ∞).choose k := by
  cases k with
  | zero => simp
  | succ k => rfl

/-- An infinite set has infinitely many subsets of each positive size. -/
@[simp]
lemma top_choose (hk : k ≠ 0) : (⊤ : ℕ∞).choose k = ⊤ := by
  cases k with
  | zero => contradiction
  | succ k => rfl

@[gcongr]
lemma choose_le_choose (h : m ≤ n) : m.choose k ≤ n.choose k := by
  obtain rfl | hk := eq_or_ne k 0
  · simp
  induction n using ENat.recTopCoe with
  | top => simp [hk]
  | coe n =>
    lift m to ℕ using ne_top_of_le_ne_top (natCast_ne_top n) h
    exact_mod_cast Nat.choose_le_choose k (mod_cast h)

lemma choose_mono (k : ℕ) : Monotone (choose · k) := fun _ _ ↦ choose_le_choose

lemma natCast_choose_le_choose {m : ℕ} (h : m ≤ n) : m.choose k ≤ n.choose k :=
  (natCast_choose m k).trans_le (choose_le_choose h)

lemma choose_le_iff {c : ℕ∞} : n.choose k ≤ c ↔ ∀ m : ℕ, m ≤ n → m.choose k ≤ c := by
  refine ⟨fun h m hm ↦ (natCast_choose_le_choose hm).trans h, fun h ↦ ?_⟩
  induction n using ENat.recTopCoe with
  | coe n => simpa using h n le_rfl
  | top =>
    obtain rfl | hk := eq_or_ne k 0
    · simpa using h 0 le_top
    rw [top_choose hk]
    exact forall_natCast_le_iff_le.1 fun a _ ↦
      le_trans (mod_cast le_trans (by rw [Nat.choose_succ_self_right]; lia)
          ((Nat.choose_le_choose a (by lia : a + 1 ≤ a + k)).trans_eq Nat.choose_symm_add))
        (h (a + k) le_top)

/-- `n.choose k` is the supremum of the binomial coefficients `m.choose k` over the natural numbers
`m ≤ n`. -/
lemma choose_eq_iSup (n : ℕ∞) (k : ℕ) :
    n.choose k = ⨆ (m : ℕ) (_ : (m : ℕ∞) ≤ n), (m.choose k : ℕ∞) :=
  le_antisymm (choose_le_iff.2 fun m hm ↦ le_iSup₂_of_le m hm le_rfl)
    (iSup₂_le fun _ ↦ natCast_choose_le_choose)

@[simp]
lemma choose_one_right (n : ℕ∞) : n.choose 1 = n := by
  induction n using ENat.recTopCoe with
  | top => simp
  | coe n => exact_mod_cast Nat.choose_one_right n

/-- **Pascal's rule** for extended natural numbers. -/
lemma choose_succ_succ (n : ℕ∞) (k : ℕ) :
    (n + 1).choose (k + 1) = n.choose k + n.choose (k + 1) := by
  induction n using ENat.recTopCoe with
  | top => simp
  | coe n => exact_mod_cast Nat.choose_succ_succ n k

end ENat

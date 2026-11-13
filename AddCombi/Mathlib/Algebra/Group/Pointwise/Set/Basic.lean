module

public import Mathlib.Algebra.Group.Pointwise.Set.Basic

import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Tactic.ToFun

public section

open scoped Pointwise

namespace Set
variable {ι : Type*} {M : ι → Type*} [∀ i, Monoid (M i)]

@[to_additive]
lemma pi_mul (s : Set ι) (t u : ∀ i, Set (M i)) : s.pi (fun i ↦ t i * u i) = s.pi t * s.pi u := by
  classical
  ext x
  simp only [mem_pi, mem_mul]
  refine ⟨fun h ↦ ?_, ?_⟩
  · choose! y hy z hz hyz using h
    exact ⟨fun i ↦ if i ∈ s then y i else x i, by simpa +contextual,
      fun i ↦ if i ∈ s then z i else 1, by simpa +contextual, by ext; dsimp; grind⟩
  · rintro ⟨y, hy, z, hz, rfl⟩ i hi
    exact ⟨y i, hy _ hi, z i, hz _ hi, rfl⟩

@[to_additive nsmul_pi]
lemma pi_pow (s : Set ι) (t : ∀ i, Set (M i)) :
    ∀ {n : ℕ}, n ≠ 0 → s.pi t ^ n = s.pi (fun i ↦ t i ^ n)
  | 1, _ => by simp
  | n + 2, _ => by simp [pow_succ _ (n + 1), pi_mul, ← pi_pow]

@[to_additive nsmul_univ_pi]
lemma univ_pi_pow (t : ∀ i, Set (M i)) : ∀ n : ℕ, univ.pi t ^ n = univ.pi (fun i ↦ t i ^ n)
  | 0 => by simp [← Set.singleton_one, ← Set.univ_pi_singleton]
  | n + 1 => by simp [pi_pow]

end Set

namespace Set
variable {α M : Type*} [Mul M] {f g : α → M}

@[to_fun (attr := to_additive) range_fun_mul_subset]
lemma range_mul_subset : range (f * g) ⊆ range f * range g := by
  simp [range_subset_iff, Set.mul_mem_mul]

end Set

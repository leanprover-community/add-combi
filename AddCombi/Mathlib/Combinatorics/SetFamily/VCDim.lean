/-
Copyright (c) 2025 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Order.Interval.Set.Basic
public import AddCombi.Mathlib.Analysis.Complex.Exponential
public import AddCombi.Mathlib.Data.Set.Basic
public import AddCombi.Mathlib.Data.Set.Card
public import AddCombi.Mathlib.Data.Set.Card.Arithmetic
public import AddCombi.Mathlib.Data.Set.Image

import Mathlib.Order.Lattice.Nat
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Simproc.ExistsAndEq

/-!
# VC dimension

This file defines shattering and the VC dimension of set families, and proves Pajor's inequality
and the Sauer-Shelah lemma for arbitrary set families.

## Main definitions

* `Shatters`: a set family shatters a set.
* `vcGrowth`: the growth function of a set family.
* `HasVCDimLE`: a set family has VC dimension at most `d`.

## Main statements

* `encard_image_inter_le_encard_shatters`: Pajor's inequality.
* `HasVCDimLE.ncard_image_inter_le`, `HasVCDimLE.vcGrowth_le`: the Sauer-Shelah lemma.
* `HasVCDimLE.vcGrowth_le_exp`: `vcGrowth n 𝒜 ≤ (exp 1 / d * n) ^ d`.

## References

* V. N. Vapnik and A. Ya. Chervonenkis, *On the uniform convergence of relative frequencies of
  events to their probabilities*, Theory Probab. Appl. 16 (1971), 264–280.
* N. Sauer, *On the density of families of sets*, J. Combin. Theory Ser. A 13 (1972), 145–147.
* S. Shelah, *A combinatorial problem; stability and order for models and theories in infinitary
  languages*, Pacific J. Math. 41 (1972), 247–261.
* A. Pajor, *Sous-espaces `ℓ₁ⁿ` des espaces de Banach*, Travaux en Cours 16, Hermann, Paris,
  1985.
-/

open Real

public section

variable {α : Type*}

section SemilatticeInf
variable [SemilatticeInf α] {𝒜 ℬ : Set α} {A B : α}

/-- A set family `𝒜` shatters a set `A` if all subsets of `A` can be obtained as the intersection
of `A` with some element of the set family. We also say that `A` is *traced* by `𝒜`. -/
@[expose]
def Shatters (𝒜 : Set α) (A : α) : Prop := ∀ ⦃B⦄, B ≤ A → ∃ C ∈ 𝒜, A ⊓ C = B

@[gcongr]
lemma Shatters.mono (h : 𝒜 ⊆ ℬ) (h𝒜 : Shatters 𝒜 A) : Shatters ℬ A :=
  fun _B hBA ↦ let ⟨C, hC, hCB⟩ := h𝒜 hBA; ⟨C, h hC, hCB⟩

@[gcongr]
lemma Shatters.anti (h : A ≤ B) (hB : Shatters 𝒜 B) : Shatters 𝒜 A := fun C hCA ↦ by
  obtain ⟨D, hD, rfl⟩ := hB (hCA.trans h); exact ⟨D, hD, inf_congr_right hCA <| inf_le_of_left_le h⟩

lemma Shatters.exists_ge (h : Shatters 𝒜 A) : ∃ B ∈ 𝒜, A ≤ B := by simpa using h le_rfl

lemma Shatters.of_forall_le (h : ∀ B ≤ A, B ∈ 𝒜) : Shatters 𝒜 A :=
  fun B hBA ↦ ⟨B, h _ hBA, inf_eq_right.2 hBA⟩

protected lemma Shatters.nonempty (h : Shatters 𝒜 A) : 𝒜.Nonempty :=
  let ⟨B, hB, _⟩ := h le_rfl; ⟨B, hB⟩

protected lemma Shatters.le_iff (h : Shatters 𝒜 A) : B ≤ A ↔ ∃ C ∈ 𝒜, A ⊓ C = B :=
  ⟨fun ht ↦ h ht, by rintro ⟨u, _, rfl⟩; exact inf_le_left⟩

lemma shatters_iff_image_inf_eq_Iic : Shatters 𝒜 A ↔ (A ⊓ ·) '' 𝒜 = .Iic A := by
  aesop (add simp [Set.ext_iff, Shatters])

protected lemma Shatters.univ : Shatters .univ A := .of_forall_le <| by simp

@[simp] lemma shatters_bot [OrderBot α] : Shatters 𝒜 ⊥ ↔ 𝒜.Nonempty :=
  ⟨Shatters.nonempty, fun ⟨A, hA⟩ B hB ↦ ⟨A, hA, by simpa [eq_comm] using hB⟩⟩

@[simp] lemma shatters_top [OrderTop α] : Shatters 𝒜 ⊤ ↔ 𝒜 = .univ := by
  simp [shatters_iff_image_inf_eq_Iic]

end SemilatticeInf

section BooleanAlgebra
variable [BooleanAlgebra α] {𝒜 : Set α} {A : α}

lemma Shatters.preimage_compl (hA : Shatters 𝒜 A) : Shatters ((·ᶜ) ⁻¹' 𝒜) A := by
  rintro B hBA
  obtain ⟨C, hC, hABC⟩ : ∃ C ∈ 𝒜, A ⊓ C = A \ B := hA sdiff_le
  exact ⟨Cᶜ, by simpa, by simpa [← sdiff_eq, hBA] using congr(A \ $hABC)⟩

@[simp] lemma shatters_preimage_compl : Shatters ((·ᶜ) ⁻¹' 𝒜) A ↔ Shatters 𝒜 A where
  mp hA := by simpa [Set.preimage_preimage] using hA.preimage_compl
  mpr := .preimage_compl

@[simp] lemma shatters_image_compl : Shatters ((·ᶜ) '' 𝒜) A ↔ Shatters 𝒜 A := by
  simp [← Set.preimage_compl_eq_image_compl]

alias ⟨_, Shatters.image_compl⟩ := shatters_image_compl

end BooleanAlgebra

section Finset
variable [DecidableEq α] {𝒜 ℬ : Finset (Finset α)}

instance : DecidablePred (Shatters (𝒜 : Set (Finset α))) :=
  fun _s ↦ Finset.decidableForallOfDecidableSubsets

end Finset

section Set
variable {m n d d₁ d₂ : ℕ} {𝒜 ℬ : Set (Set α)} {A B : Set α} {x : α}

@[gcongr]
lemma Shatters.subset (h : A ⊆ B) (hB : Shatters 𝒜 B) : Shatters 𝒜 A := hB.anti h

/-- `𝒜` shatters the singleton `{x}` exactly when some member of `𝒜` contains `x` and some
member of `𝒜` misses it. -/
@[simp] lemma shatters_singleton : Shatters 𝒜 {x} ↔ (∃ C ∈ 𝒜, x ∉ C) ∧ ∃ C ∈ 𝒜, x ∈ C := by
  simp [Shatters, -Set.subset_singleton_iff, Set.subset_singleton_iff_eq]

open scoped Finset

lemma shatters_iff_le_ncard_image_inter (hA : A.Finite) :
    Shatters 𝒜 A ↔ 2 ^ A.ncard ≤ ((A ∩ ·) '' 𝒜).ncard := by
  have hsub : (A ∩ ·) '' 𝒜 ⊆ 𝒫 A := by grind
  rw [shatters_iff_image_inf_eq_Iic, ← Set.ncard_powerset _ hA]
  exact ⟨fun h ↦ (congrArg Set.ncard h).ge, fun h ↦ Set.eq_of_subset_of_ncard_le hsub h hA.powerset⟩

variable (n 𝒜) in
/-- The growth of a set family is the maximum number of sets it cuts out from any set of size at
most `n`. -/
noncomputable def vcGrowth : ℕ :=
  ⨆ A : {A : Set α // A.Finite ∧ A.ncard ≤ n}, ((↑A ∩ ·) '' 𝒜).ncard

private lemma bddAbove_range :
    BddAbove (.range fun A : {A : Set α // A.Finite ∧ A.ncard ≤ n} ↦ ((↑A ∩ ·) '' 𝒜).ncard) := by
  use 2 ^ n
  simp only [mem_upperBounds, Set.mem_range, Subtype.exists, exists_prop, forall_exists_index,
    and_imp, forall_comm (α := ℕ), forall_apply_eq_imp_iff₂]
  rintro A hA hAn
  grw [← hAn, ← Set.ncard_powerset _ hA]
  gcongr
  · exact hA.powerset
  · grind

private lemma finite_image_inter (hA : A.Finite) : ((A ∩ ·) '' 𝒜).Finite :=
  hA.powerset.subset (by grind)

lemma vcGrowth_le_iff {d : ℕ} :
    vcGrowth n 𝒜 ≤ d ↔ ∀ ⦃A : Set α⦄, A.Finite → A.ncard ≤ n → ((A ∩ ·) '' 𝒜).ncard ≤ d := by
  simp [vcGrowth, ciSup_le_iff' bddAbove_range]

lemma vcGrowth_lt_iff {d : ℕ} :
    vcGrowth n 𝒜 < d ↔ ∀ ⦃A : Set α⦄, A.Finite → A.ncard ≤ n → ((A ∩ ·) '' 𝒜).ncard < d := by
  obtain _ | d := d
  · simp only [not_lt_zero, imp_false, not_le, false_iff, not_forall, not_lt]
    exact ⟨∅, by simp⟩
  · simp [vcGrowth_le_iff]

lemma ncard_image_inter_le_vcGrowth (hA : A.Finite) (hAn : A.ncard ≤ n) :
    ((A ∩ ·) '' 𝒜).ncard ≤ vcGrowth n 𝒜 := vcGrowth_le_iff.1 le_rfl hA hAn

@[gcongr]
lemma vcGrowth_mono (h𝒜ℬ : 𝒜 ⊆ ℬ) (hmn : m ≤ n) : vcGrowth m 𝒜 ≤ vcGrowth n ℬ := by
  grw [vcGrowth_le_iff, h𝒜ℬ, hmn, ← vcGrowth_le_iff]; exact finite_image_inter ‹_›

lemma vcGrowth_union_le : vcGrowth n (𝒜 ∪ ℬ) ≤ vcGrowth n 𝒜 + vcGrowth n ℬ := by
  rw [vcGrowth_le_iff]
  rintro A hA hAn
  grw [Set.image_union, Set.ncard_union_le, ncard_image_inter_le_vcGrowth hA hAn,
    ncard_image_inter_le_vcGrowth hA hAn]

lemma vcGrowth_image2_inter_le :
    vcGrowth n (.image2 (· ∩ ·) 𝒜 ℬ) ≤ vcGrowth n 𝒜 * vcGrowth n ℬ := by
  rw [vcGrowth_le_iff]
  rintro A hA hAn
  grw [Set.image_image2_distrib (Set.inter_inter_distrib_left _), Set.ncard_image2_le,
    ncard_image_inter_le_vcGrowth hA hAn, ncard_image_inter_le_vcGrowth hA hAn] <;>
      exact finite_image_inter hA

/-- A set family `𝒜` has VC dimension at most `d` if all the sets it shatters have size at most
`d`. -/
@[expose]
def HasVCDimLE (d : ℕ) (𝒜 : Set (Set α)) : Prop :=
  ∀ ⦃A : Set α⦄, A.Finite → Shatters 𝒜 A → A.ncard ≤ d

@[gcongr]
lemma HasVCDimLE.anti (hℬ𝒜 : ℬ ⊆ 𝒜) (hd : HasVCDimLE d 𝒜) : HasVCDimLE d ℬ :=
  fun _A hA h𝒜A ↦ hd hA <| h𝒜A.mono hℬ𝒜

@[gcongr]
lemma HasVCDimLE.mono (hd : d₁ ≤ d₂) : HasVCDimLE d₁ 𝒜 → HasVCDimLE d₂ 𝒜 := by
  grw [HasVCDimLE, HasVCDimLE, hd]; exact id

private lemma trace_sep_union :
    (A ∩ ·) '' {C ∈ 𝒜 | x ∉ C} ∪ (A ∩ ·) '' {C ∈ 𝒜 | x ∈ C} = (A ∩ ·) '' 𝒜 := by
  rw [← Set.image_union]; congr 1; ext C; grind

private lemma trace_sep_disjoint (hxA : x ∈ A) :
    Disjoint ((A ∩ ·) '' {C ∈ 𝒜 | x ∉ C}) ((A ∩ ·) '' {C ∈ 𝒜 | x ∈ C}) := by
  rw [Set.disjoint_left]
  rintro t ⟨C, hC, rfl⟩ ⟨C', hC', htC⟩
  have := Set.ext_iff.1 htC x
  grind

/-- A family whose members all avoid `x` shatters only sets avoiding `x`. -/
lemma notMem_of_forall_notMem (h𝒜 : ∀ C ∈ 𝒜, x ∉ C) (hB : Shatters 𝒜 B) : x ∉ B :=
  let ⟨C, hC, hBC⟩ := hB.exists_ge; fun hxB ↦ h𝒜 C hC (hBC hxB)

/-- A family whose members all contain `x` shatters only sets avoiding `x`. -/
lemma notMem_of_forall_mem (h𝒜 : ∀ C ∈ 𝒜, x ∈ C) (hB : Shatters 𝒜 B) : x ∉ B :=
  notMem_of_forall_notMem (fun C hC ↦ h𝒜 Cᶜ hC) hB.preimage_compl

/-- If `B` is shattered both by the members of `𝒜` avoiding `x` and by the members of `𝒜`
containing `x`, then `𝒜` shatters `insert x B`. -/
protected lemma Shatters.insert (h₀ : Shatters {C ∈ 𝒜 | x ∉ C} B)
    (h₁ : Shatters {C ∈ 𝒜 | x ∈ C} B) : Shatters 𝒜 (insert x B) := by
  intro B' hB'
  by_cases hxB' : x ∈ B'
  · obtain ⟨C, ⟨hC, hxC⟩, hBC⟩ := h₁ (show B' \ {x} ≤ B by grind)
    refine ⟨C, hC, ?_⟩
    simp only [Set.inf_eq_inter] at hBC ⊢
    rw [Set.insert_inter_of_mem hxC, hBC, Set.insert_sdiff_singleton, Set.insert_eq_of_mem hxB']
  · obtain ⟨C, ⟨hC, hxC⟩, hBC⟩ := h₀ (show B' ≤ B by grind)
    refine ⟨C, hC, ?_⟩
    simp only [Set.inf_eq_inter] at hBC ⊢
    rw [Set.insert_inter_of_notMem hxC, hBC]

private lemma exists_splitter (h : ((A ∩ ·) '' 𝒜).Nontrivial) :
    ∃ x ∈ A, (∃ C ∈ 𝒜, x ∉ C) ∧ ∃ C ∈ 𝒜, x ∈ C := by
  obtain ⟨t₁, ⟨C₁, hC₁, rfl⟩, t₂, ⟨C₂, hC₂, rfl⟩, hne⟩ := h
  grind [Set.Subset.antisymm]

private lemma pajor_encard_aux (hfin : ((A ∩ ·) '' 𝒜).Finite) :
    ((A ∩ ·) '' 𝒜).encard ≤ {B | B ⊆ A ∧ Shatters 𝒜 B}.encard := by
  induction hn : ((A ∩ ·) '' 𝒜).ncard using Nat.strong_induction_on generalizing 𝒜 with
  | _ N ih =>
  obtain hsub | hnt := ((A ∩ ·) '' 𝒜).subsingleton_or_nontrivial
  · obtain rfl | ⟨C, hC⟩ := 𝒜.eq_empty_or_nonempty
    · simp
    · exact (Set.encard_le_one_iff_subsingleton.2 hsub).trans <|
        Set.one_le_encard_iff_nonempty.2 ⟨∅, Set.empty_subset A, shatters_bot.2 ⟨C, hC⟩⟩
  · obtain ⟨x, hxA, ⟨C₂, hC₂, hxC₂⟩, C₁, hC₁, hxC₁⟩ := exists_splitter hnt
    have hfin₀ : ((A ∩ ·) '' {C ∈ 𝒜 | x ∉ C}).Finite :=
      hfin.subset (Set.image_mono (Set.sep_subset _ _))
    have hfin₁ : ((A ∩ ·) '' {C ∈ 𝒜 | x ∈ C}).Finite :=
      hfin.subset (Set.image_mono (Set.sep_subset _ _))
    have hpos₀ : 0 < ((A ∩ ·) '' {C ∈ 𝒜 | x ∉ C}).ncard :=
      (Set.ncard_pos hfin₀).2 ⟨A ∩ C₂, C₂, ⟨hC₂, hxC₂⟩, rfl⟩
    have hpos₁ : 0 < ((A ∩ ·) '' {C ∈ 𝒜 | x ∈ C}).ncard :=
      (Set.ncard_pos hfin₁).2 ⟨A ∩ C₁, C₁, ⟨hC₁, hxC₁⟩, rfl⟩
    rw [← trace_sep_union (x := x), Set.ncard_union_eq (trace_sep_disjoint hxA) hfin₀ hfin₁]
      at hn
    set 𝒮₀ := {B | B ⊆ A ∧ Shatters {C ∈ 𝒜 | x ∉ C} B}
    set 𝒮₁ := {B | B ⊆ A ∧ Shatters {C ∈ 𝒜 | x ∈ C} B}
    calc ((A ∩ ·) '' 𝒜).encard
        = ((A ∩ ·) '' {C ∈ 𝒜 | x ∉ C}).encard + ((A ∩ ·) '' {C ∈ 𝒜 | x ∈ C}).encard := by
          rw [← trace_sep_union (x := x), Set.encard_union_eq (trace_sep_disjoint hxA)]
      _ ≤ 𝒮₀.encard + 𝒮₁.encard := by gcongr ?_ + ?_ <;> exact ih _ (by lia) ‹_› rfl
      _ = (𝒮₀ ∪ 𝒮₁).encard + (𝒮₀ ∩ 𝒮₁).encard :=
          (Set.encard_union_add_encard_inter 𝒮₀ 𝒮₁).symm
      _ = (𝒮₀ ∪ 𝒮₁).encard + (insert x '' (𝒮₀ ∩ 𝒮₁)).encard := by
          rw [((Set.insert_injOn_notMem x).mono ?_).encard_image]
          exact fun B hB ↦ notMem_of_forall_notMem (fun _ ↦ And.right) hB.1.2
      _ = ((𝒮₀ ∪ 𝒮₁) ∪ insert x '' (𝒮₀ ∩ 𝒮₁)).encard :=
          (Set.encard_union_eq <| Set.disjoint_left.2 <| by
            rintro B (⟨-, hB⟩ | ⟨-, hB⟩) ⟨B', -, rfl⟩
            exacts [notMem_of_forall_notMem (fun _ ↦ And.right) hB (Set.mem_insert x B'),
              notMem_of_forall_mem (fun _ ↦ And.right) hB (Set.mem_insert x B')]).symm
      _ ≤ {B | B ⊆ A ∧ Shatters 𝒜 B}.encard := Set.encard_le_encard <| by
          rintro B ((⟨hBA, hB⟩ | ⟨hBA, hB⟩) | ⟨B', ⟨⟨hB'A, hB'₀⟩, -, hB'₁⟩, rfl⟩)
          · exact ⟨hBA, hB.mono (Set.sep_subset _ _)⟩
          · exact ⟨hBA, hB.mono (Set.sep_subset _ _)⟩
          · exact ⟨Set.insert_subset hxA hB'A, hB'₀.insert hB'₁⟩

/-- A trace of `𝒜` on `A` is determined by its restriction to the points whose singleton `𝒜`
shatters: off those points, all traces agree. -/
private lemma injOn_inter_ofPred_shatters_singleton :
    Set.InjOn (· ∩ {x ∈ A | Shatters 𝒜 {x}}) ((A ∩ ·) '' 𝒜) := by
  rintro t ⟨C, hC, rfl⟩ t' ⟨C', hC', rfl⟩ hIt
  ext y
  simp only [Set.ext_iff, Set.mem_inter_iff, Set.mem_ofPred_eq, shatters_singleton] at hIt
  grind

/-- A family shattering finitely many singletons in `A` has finitely many traces on `A`. -/
private lemma finite_image_inter_of_finite_ofPred_shatters_singleton
    (h : {x ∈ A | Shatters 𝒜 {x}}.Finite) : ((A ∩ ·) '' 𝒜).Finite :=
  .of_finite_image (h.powerset.subset (by grind [-Set.image_image]))
    injOn_inter_ofPred_shatters_singleton

/-- A family with infinitely many traces on `A` shatters infinitely many subsets of `A`. -/
lemma infinite_ofPred_shatters (h : ((A ∩ ·) '' 𝒜).Infinite) :
    {B | B ⊆ A ∧ Shatters 𝒜 B}.Infinite :=
  .mono (by grind) <| .image Set.singleton_injective.injOn fun hfin ↦
    h (finite_image_inter_of_finite_ofPred_shatters_singleton hfin)

/-- If only finitely many, say `k`, points of `A` have their singleton shattered by `𝒜`, then `𝒜`
has at most `2 ^ k` traces on `A`. -/
lemma ncard_image_inter_le_two_pow_ncard_shatters_singleton
    (h : {x ∈ A | Shatters 𝒜 {x}}.Finite) :
    ((A ∩ ·) '' 𝒜).ncard ≤ 2 ^ {x ∈ A | Shatters 𝒜 {x}}.ncard := by
  rw [← Set.ncard_powerset _ h]
  exact Set.ncard_le_ncard_of_injOn _ (fun _ _ ↦ Set.inter_subset_right)
    injOn_inter_ofPred_shatters_singleton h.powerset

/-- **Pajor's inequality**: the traces of `𝒜` on `A` are at most
as many as the subsets of `A` shattered by `𝒜`. Since `encard` counts every infinite set as `⊤`,
when there are infinitely many traces this says only that `𝒜` shatters infinitely many subsets
of `A`. -/
lemma encard_image_inter_le_encard_shatters :
    ((A ∩ ·) '' 𝒜).encard ≤ {B | B ⊆ A ∧ Shatters 𝒜 B}.encard := by
  by_cases h : ((A ∩ ·) '' 𝒜).Finite
  · exact pajor_encard_aux h
  · simp [(infinite_ofPred_shatters h).encard_eq]

/-- **Pajor's inequality** on a finite set `A`: the traces of `𝒜` on `A` are at most as many as
the subsets of `A` that `𝒜` shatters. -/
lemma ncard_image_inter_le_ncard_shatters (hA : A.Finite) :
    ((A ∩ ·) '' 𝒜).ncard ≤ {B | B ⊆ A ∧ Shatters 𝒜 B}.ncard :=
  (Set.encard_le_coe_iff_finite_ncard_le.1 <| encard_image_inter_le_encard_shatters.trans_eq
    (hA.finite_subsets.subset fun _B ↦ And.left).cast_ncard_eq.symm).2

/-- A family of VC dimension at most `d` shatters no infinite set. -/
lemma HasVCDimLE.finite_of_shatters (h𝒜 : HasVCDimLE d 𝒜) (hB : Shatters 𝒜 B) : B.Finite := by
  by_contra! hinf
  obtain ⟨B', hB'B, hB'fin, hB'card⟩ := hinf.exists_subset_ncard_eq (d + 1)
  exact absurd (h𝒜 hB'fin (hB.subset hB'B)) (by lia)

/-- A family of VC dimension at most `d` shatters only sets of size at most `d`. -/
lemma HasVCDimLE.ncard_le_of_shatters (h𝒜 : HasVCDimLE d 𝒜) (hB : Shatters 𝒜 B) :
    B.ncard ≤ d := h𝒜 (h𝒜.finite_of_shatters hB) hB

/-- The Sauer-Shelah count, from a bound on the shattered subsets of `A` alone. -/
private lemma ncard_image_inter_le_of_forall_ncard_le (hA : A.Finite) (hAn : A.ncard ≤ n)
    (h : ∀ B ⊆ A, Shatters 𝒜 B → B.ncard ≤ d) :
    ((A ∩ ·) '' 𝒜).ncard ≤ ∑ k ∈ .Iic d, n.choose k :=
  calc ((A ∩ ·) '' 𝒜).ncard
      ≤ {B | B ⊆ A ∧ Shatters 𝒜 B}.ncard := ncard_image_inter_le_ncard_shatters hA
    _ ≤ {B | B ⊆ A ∧ B.ncard ≤ d}.ncard :=
        Set.ncard_le_ncard (fun _B hB ↦ ⟨hB.1, h _ hB.1 hB.2⟩)
          (hA.finite_subsets.subset fun _B hB ↦ hB.1)
    _ = ∑ k ∈ .Iic d, A.ncard.choose k := Set.ncard_ofPred_ncard_le hA d
    _ ≤ ∑ k ∈ .Iic d, n.choose k := by gcongr

/-- **The Sauer-Shelah inequality**: a family of VC dimension at most `d` traces at most
`∑ k ≤ d, n.choose k` sets on any finite set of size at most `n`. -/
lemma HasVCDimLE.ncard_image_inter_le (h𝒜 : HasVCDimLE d 𝒜) (hA : A.Finite)
    (hAn : A.ncard ≤ n) :
    ((A ∩ ·) '' 𝒜).ncard ≤ ∑ k ∈ .Iic d, n.choose k :=
  ncard_image_inter_le_of_forall_ncard_le hA hAn fun _B _ hB ↦ h𝒜.ncard_le_of_shatters hB

/-- The extraction form of the Sauer-Shelah inequality: a family tracing more than
`∑ k ≤ d, n.choose k` sets on a finite `A` of size at most `n` shatters a subset of `A` of size
greater than `d`. -/
lemma exists_shatters_of_lt_ncard_image_inter (hA : A.Finite) (hAn : A.ncard ≤ n)
    (h : ∑ k ∈ .Iic d, n.choose k < ((A ∩ ·) '' 𝒜).ncard) :
    ∃ B ⊆ A, d < B.ncard ∧ Shatters 𝒜 B := by
  by_contra! hc
  exact absurd h (not_lt.2 (ncard_image_inter_le_of_forall_ncard_le hA hAn
    fun _B hBA hB ↦ not_lt.1 fun hlt ↦ hc _ hBA hlt hB))

/-- **The Sauer-Shelah lemma** for the growth function: if `𝒜` has VC dimension at most `d`, then
`vcGrowth n 𝒜`, the largest number of sets `𝒜` cuts out from a set of size at most `n`, is at most
`∑ k ≤ d, n.choose k`. -/
lemma HasVCDimLE.vcGrowth_le (h𝒜 : HasVCDimLE d 𝒜) :
    vcGrowth n 𝒜 ≤ ∑ k ∈ .Iic d, n.choose k :=
  vcGrowth_le_iff.2 fun _A hA hAn ↦ h𝒜.ncard_image_inter_le hA hAn

/-- The Sauer-Shelah bound: the growth function of a family of VC dimension at
most `d` is at most `(exp 1 / d * n) ^ d`, for `d ≤ n`. -/
lemma HasVCDimLE.vcGrowth_le_exp (h𝒜 : HasVCDimLE d 𝒜) (hdn : d ≤ n) :
    (vcGrowth n 𝒜 : ℝ) ≤ (exp 1 / d * n) ^ d := by
  obtain rfl | hd := Nat.eq_zero_or_pos d
  · rw [pow_zero]
    exact mod_cast (h𝒜.vcGrowth_le (n := n)).trans_eq (by simp)
  · calc (vcGrowth n 𝒜 : ℝ)
        ≤ ((∑ k ∈ .Iic d, n.choose k : ℕ) : ℝ) := Nat.cast_le.2 h𝒜.vcGrowth_le
      _ = ∑ k ∈ Finset.range (d + 1), (n.choose k : ℝ) := by
          rw [Nat.range_succ_eq_Iic]; push_cast; rfl
      _ ≤ (exp 1 / d * n) ^ d := sum_choose_le_exp_pow d n hd hdn

variable [Infinite α]

lemma vcGrowth_le_iff' {d : ℕ} :
    vcGrowth n 𝒜 ≤ d ↔ ∀ ⦃A : Set α⦄, A.Finite → A.ncard = n → ((A ∩ ·) '' 𝒜).ncard ≤ d := by
  rw [vcGrowth_le_iff]
  constructor
  · rintro h A hA hAn
    exact h hA hAn.le
  · rintro h A hA hAn
    obtain ⟨B, hB, hAB, -, rfl⟩ := Set.exists_superset_ncard_eq hA hAn
    grw [← h hB rfl]
    simpa [Set.image_image, hAB, ← Set.inter_assoc]
      using Set.ncard_image_le (finite_image_inter hB) (f := (A ∩ ·))

lemma vcGrowth_lt_iff' {d : ℕ} :
    vcGrowth n 𝒜 < d ↔ ∀ ⦃A : Set α⦄, A.Finite → A.ncard = n → ((A ∩ ·) '' 𝒜).ncard < d := by
  obtain _ | d := d
  · simpa [not_lt_zero, imp_false, false_iff, not_forall, Classical.not_imp, Decidable.not_not]
      using Set.exists_ncard_eq α n
  · simp [vcGrowth_le_iff']

lemma hasVCDimLE_iff_vcGrowth : HasVCDimLE d 𝒜 ↔ vcGrowth (d + 1) 𝒜 < 2 ^ (d + 1) := by
  simp only [HasVCDimLE, vcGrowth_lt_iff']
  constructor
  · rintro h A hA hAd
    rw [← hAd]
    contrapose! h
    exact ⟨A, hA, (shatters_iff_le_ncard_image_inter hA).2 h, by lia⟩
  · rintro h A hA hA𝒜
    contrapose! h
    rw [← Nat.add_one_le_iff] at h
    obtain ⟨B, hBA, hB, hBd⟩ := Set.exists_subset_ncard_eq hA h
    refine ⟨B, hB, hBd, ?_⟩
    grw [← hBd, ← shatters_iff_le_ncard_image_inter hB, hBA]
    exact hA𝒜

end Set

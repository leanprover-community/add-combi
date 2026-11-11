module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Combinatorics.Additive.CovBySMul

import AddCombi.Mathlib.Algebra.Group.Action.Pointwise.Set.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Group
import Mathlib.Tactic.Positivity.Finset

/-!
## TODO

Protect `CovBySMul.rfl`
-/

public section

open scoped Finset Pointwise

variable {M G X : Type*}

section Monoid
variable [Monoid M] [MulAction M X] {A B : Set X} {K L ε : ℝ} {m n : ℕ}

attribute [gcongr] CovBySMul.subset_left CovBySMul.subset_right

@[to_additive]
lemma CovBySMul.pos (hAB : CovBySMul M K A B) (hA : A.Nonempty) : 0 < K := by
  obtain ⟨F, hFK, hFAB⟩ := hAB; contrapose! hA; grw [hA] at hFK; simp_all

@[to_additive]
lemma CovBySMul.prod {N : Type*} [Group N] {A B : Set M} {C D : Set N} (hAB : CovBySMul M K A B)
    (hCD : CovBySMul N L C D) : CovBySMul (M × N) (K * L) (A ×ˢ C) (B ×ˢ D) := by
  obtain ⟨F₁, h₁, hAB⟩ := hAB
  obtain ⟨F₂, h₂, hCD⟩ := hCD
  classical
  refine ⟨F₁ ×ˢ F₂, ?_, ?_⟩
  · simp only [Finset.card_product, Nat.cast_mul]
    gcongr
    grw [← h₁]
    positivity
  rintro ⟨x, y⟩ ⟨(hx : x ∈ _), hy⟩
  obtain ⟨g, hg, b, hb, rfl⟩ := hAB hx
  obtain ⟨h, hh, d, hd, rfl⟩ := hCD hy
  exact ⟨(g, h), by simp [*], (b, d), by simp [*]⟩

@[to_additive]
lemma CovBySMul.pi {ι : Type*} {G X : ι → Type*} {s : Finset ι} [∀ i, Group (G i)]
    [∀ i, MulAction (G i) (X i)] {A B : ∀ i, Set (X i)} {K : ι → ℝ}
    (hAB : ∀ i ∈ s, CovBySMul (G i) (K i) (A i) (B i)) :
    CovBySMul (∀ i, G i) (∏ i ∈ s, K i) (.pi s A) (.pi s B) := by
  choose! F hF hFS using hAB
  classical
  refine ⟨(s.pi F).image fun f i ↦ if hi : i ∈ s then f i hi else 1, ?_, fun x hx ↦ ?_⟩
  · calc (#((s.pi F).image _) : ℝ)
        ≤ #(s.pi F) := by grw [Finset.card_image_le]
      _ = ∏ i ∈ s, (#(F i) : ℝ) := by simp [Finset.card_pi]
      _ ≤ ∏ i ∈ s, K i := by gcongr with i hi; exact hF _ hi
  have (i : ι) : Nonempty (X i) := ⟨x i⟩
  choose! g hg y hy hgy using fun i hi ↦ hFS i hi <| hx _ hi
  exact ⟨fun i ↦ if i ∈ s then g i else 1, Finset.mem_image.2 ⟨fun i _ ↦ g i,
    Finset.mem_pi.2 fun i hi ↦ hg i hi, by ext i; simp [dite_eq_ite]⟩,
    fun i ↦ if i ∈ s then y i else x i, by simp_all, by ext; dsimp; split <;> simp_all⟩

end Monoid

variable [Group G] {A B C : Set G} {K L : ℝ}

@[to_additive]
lemma CovBySMul.inter (hA : CovBySMul G K C A) (hB : CovBySMul G L C B) :
    CovBySMul G (K * L) C (A⁻¹ * A ∩ (B⁻¹ * B)) := by
  classical
  obtain ⟨F₁, hF₁card, hF₁⟩ := hA
  obtain ⟨F₂, hF₂card, hF₂⟩ := hB
  have (x : G) (hx : x ∈ C) : ∃ p : G × G, p.1 ∈ F₁ ∧ p.2 ∈ F₂ ∧ p.1⁻¹ * x ∈ A ∧ p.2⁻¹ * x ∈ B := by
    obtain ⟨s, hs, a, ha, hsa⟩ := hF₁ hx
    obtain ⟨u, hu, b, hb, hub⟩ := hF₂ hx
    exact ⟨(s, u), by grind [smul_eq_mul, inv_mul_cancel_left]⟩
  choose! pair hp using this
  let rep (p : G × G) : G := if h : ∃ y ∈ C, pair y = p then h.choose else 1
  have (x : G) (hx : x ∈ C) : pair (rep (pair x)) = pair x := by
    have : ∃ y ∈ C, pair y = pair x := ⟨x, hx, by rfl⟩
    grind
  refine ⟨(F₁ ×ˢ F₂).image rep, ?_, fun x hx ↦ ?_⟩
  · grw [Finset.card_image_le, Finset.card_product, Nat.cast_mul, hF₁card, hF₂card]
    grind
  · let r := rep (pair x)
    have : r ∈ C := by dsimp [r, rep]; split_ifs <;> grind
    refine ⟨r, by grind, r⁻¹ * x, ⟨
      ⟨((pair x).1⁻¹ * r)⁻¹, ?_, (pair x).1⁻¹ * x, (hp x hx).2.2.1, by group⟩,
      ⟨((pair x).2⁻¹ * r)⁻¹, ?_, (pair x).2⁻¹ * x, (hp x hx).2.2.2, by group⟩⟩, by simp⟩
      <;> grind [Set.mem_inv, inv_inv]

/-- If `B` is covered by `Kᵢ`-many translates of each `Aᵢ`, then it is covered by `∏ᵢ Kᵢ`-many
translates of `⋂ᵢ Aᵢ⁻¹ * Aᵢ`. -/
protected lemma CovBySMul.iInter {ι : Type*} {A : ι → Set G} {s : Finset ι} {K : ι → ℝ}
    (h : ∀ i ∈ s, CovBySMul G (K i) B (A i)) :
    CovBySMul G (∏ i ∈ s, K i) B (⋂ i ∈ s, (A i)⁻¹ * A i) := by
  classical
  choose! F hFcard hF using h
  choose! p hpF hpA using fun x hx i hi ↦ Set.mem_smul_iff_inv_smul_mem.1 (hF i hi (a := x) hx)
  let prof (x : G) (i : ι) : G := if i ∈ s then p x i else 1
  let T := (s.pi F).image fun f i ↦ if hi : i ∈ s then f i hi else 1
  have hmem : ∀ x ∈ B, prof x ∈ T := fun x hx ↦ Finset.mem_image.2 ⟨fun i _ ↦ p x i,
    Finset.mem_pi.2 fun i hi ↦ hpF x hx i hi, by ext i; simp [prof, dite_eq_ite]⟩
  let rep (φ : ι → G) : G := if h : ∃ y ∈ B, prof y = φ then h.choose else 1
  have hrep : ∀ x ∈ B, prof (rep (prof x)) = prof x ∧ rep (prof x) ∈ B := fun x hx ↦ by
    have hy : ∃ y ∈ B, prof y = prof x := ⟨x, hx, _root_.rfl⟩
    rw [show rep (prof x) = hy.choose from dite_eq_left hy]
    exact ⟨hy.choose_spec.2, hy.choose_spec.1⟩
  refine ⟨T.image rep, ?_, fun x hx ↦ ?_⟩
  · calc (#(T.image rep) : ℝ)
        ≤ #(s.pi F) := by grw [Finset.card_image_le, Finset.card_image_le]
      _ = ∏ i ∈ s, (#(F i) : ℝ) := by simp [Finset.card_pi]
      _ ≤ ∏ i ∈ s, K i := by gcongr with i hi; exact hFcard i hi
  · obtain ⟨hpr, hrB⟩ := hrep x hx
    refine ⟨rep (prof x), Finset.mem_coe.2 (Finset.mem_image_of_mem _ (hmem x hx)),
      (rep (prof x))⁻¹ * x, Set.mem_iInter₂.2 fun i hi ↦ ?_, by simp [smul_eq_mul]⟩
    have hpr_i : p (rep (prof x)) i = p x i := by simpa [prof, hi] using congr($hpr i)
    refine ⟨((p x i)⁻¹ * rep (prof x))⁻¹, ?_, (p x i)⁻¹ * x, hpA x hx i hi, by group⟩
    rw [Set.mem_inv, inv_inv, ← hpr_i]
    exact hpA _ hrB i hi

/-- Covering `B` by `K` right translates of `A` is the same as covering `B⁻¹` by `K` left translates
of `A⁻¹`. -/
lemma covBySMul_mulOpposite_iff : CovBySMul Gᵐᵒᵖ K A B ↔ CovBySMul G K A⁻¹ B⁻¹ := by
  refine ((Equiv.inv G).trans MulOpposite.opEquiv).finsetCongr.symm.exists_congr' ?_
  simp [Set.inv_subset, ← Function.comp_def _ (·⁻¹), Set.image_comp, -MulOpposite.op_inv,
    Set.image_op_smul]

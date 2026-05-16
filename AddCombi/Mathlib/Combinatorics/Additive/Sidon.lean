/-
Copyright (c) 2026 David B. Hulak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David B. Hulak
-/
module

public import Mathlib.Algebra.Group.Defs
public import Mathlib.Data.Set.Insert

/-!
# Sidon sets

This file defines the predicate `IsSidon` for sets in an additive commutative
monoid. A set is Sidon if whenever `a + b = c + d` for elements `a`, `b`, `c`,
`d` of the set, then either `a = c` and `b = d`, or `a = d` and `b = c`. The
two elements in each pair are not required to be distinct.

## Main declarations

* `IsSidon`: the Sidon predicate for a set.
* `IsSidon.mono`: subsets of Sidon sets are Sidon.
* `IsSidon.empty`: the empty set is Sidon.
* `IsSidon.singleton`: every singleton is Sidon.

## Tags

Sidon set, additive combinatorics
-/

public section

variable {G : Type*} [AddCommMonoid G]

/-- A set `A` is Sidon if whenever `a + b = c + d` for elements `a`, `b`, `c`,
`d` of `A`, then either `a = c` and `b = d`, or `a = d` and `b = c`. The two
elements in each pair are not required to be distinct. -/
def IsSidon (A : Set G) : Prop :=
  ∀ ⦃a b c d : G⦄, a ∈ A → b ∈ A → c ∈ A → d ∈ A →
    a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)

/-- A subset of a Sidon set is Sidon. -/
theorem IsSidon.mono {A B : Set G} (hB : IsSidon B) (hAB : A ⊆ B) :
    IsSidon A := by
  intro a b c d ha hb hc hd hsum
  exact hB (hAB ha) (hAB hb) (hAB hc) (hAB hd) hsum

/-- The empty set is Sidon. -/
@[simp]
theorem IsSidon.empty : IsSidon (∅ : Set G) := by
  intro a b c d ha
  cases ha

/-- A singleton is Sidon. -/
@[simp]
theorem IsSidon.singleton (a : G) : IsSidon ({a} : Set G) := by
  intro b c d e hb hc hd he _
  subst b
  subst c
  subst d
  subst e
  exact Or.inl ⟨rfl, rfl⟩

-- Created by Sean L. on Jul. 5.
-- Last Updated by Sean L. on Jul. 5.
--
-- zfc-aczel-pumac25
-- ZFCAczel/SetTheory/SetProblems.lean
--
-- Makabaka1880, 2026. All rights reserved.

import VersoManual
import ZFCAczel.Meta.Lean
import ZFCAczel.Papers
import Init.Data.Nat.Basic
import Init.Data.Nat.Linear
import ZFCAczel.SetTheory.ZFAxioms
import Lean
import Init

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Verso Code External
open ZFCAczel

set_option pp.rawOnError true
set_option linter.verso.markup.emph false

#doc (Manual) "Elementary Problems" =>
%%%
file := "SetProblems"
tag := "c1-s4-elementary-problems"
%%%

Now that we have introduced the basics of ZFC, let's dive into some problems.

# Intersection of Family (1.2.1)

> Given a nonempty set $`X`, prove that there exists a set $`\bigcap X` such that $`y \in \bigcap X` iff $`y \in x` for all $`y \in x`.
> $$`\forall X \exists \bigcap X, \, \forall y, y \in \bigcap X \iff \forall x \in X, y \in x`

Before doing anything, let's create some ergonomic APIs for expressing nonempty sets.

```lean
open Classical

namespace ZFC

def nonempty : ZFSet → Prop := λ X => ∃ wx, wx ∈ X

@[simp]
theorem nonempty_iff_ne_null : nonempty X ↔ X ≠ ∅ := by
  constructor
  · intro h
    intro hX
    unfold nonempty at h
    rw [hX] at h
    obtain nh := not_exists.mpr null_spec
    contradiction
  · intro hnn
    unfold nonempty
    apply Classical.byContradiction
    intro hne
    have eq : X = ∅ := by
      apply (axiom_ext X ∅).mp
      intro x
      constructor
      · intro _
        exfalso
        apply hne
        exists x
      · intro hx
        exfalso
        apply (null_spec x)
        exact hx
    contradiction

end ZFC
```

The definition of this set looks very like the union, only that the existential quantifier is now an universal quantifier. Our mathematical intuition tells us that this set must be a subset of the family union. Let's try using seperation on the family union.

```lean
open ZFC

namespace PUMAC25

theorem c1_s2_q1_inter_of_family
  (X : ZFSet) (hnnX : nonempty X)
    : ∃ S : ZFSet, ∀ y, y ∈ S ↔ ∀ x ∈ X, y ∈ x := by
    let ⟨union_set, h_union⟩ := axiom_union X
    let ⟨this_set, h_this⟩ :=
      axiom_separation union_set
        (λ y : ZFSet => ∀ x ∈ X, y ∈ x)
    refine ⟨this_set, λ wy => ?_⟩

    constructor
    · intro h_wy_memof_this wx h_wx_memof_X
      have ⟨h_this_for_wy_mp, h_this_for_wy_mpr⟩
        := h_this wy
      exact (h_this_for_wy_mp h_wy_memof_this).right
        wx h_wx_memof_X
    · intro h_def_inter
      have h_wy_in_union : wy ∈ union_set := by
        obtain ⟨x0, h_x0_in_X⟩ := hnnX
        have h_wy_in_x0 := h_def_inter x0 h_x0_in_X
        exact (h_union wy).mpr ⟨x0, ⟨h_wy_in_x0, h_x0_in_X⟩⟩
      have h_this_equiv := h_this wy
      exact h_this_equiv.mpr ⟨h_wy_in_union, h_def_inter⟩

end PUMAC25
```

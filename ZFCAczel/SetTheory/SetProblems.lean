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
%%%
tag := "c1-s1-q1"
%%%

> Given a nonempty set $`X`, prove that there exists a set $`\bigcap X` such that $`y \in \bigcap X` iff $`y \in x` for all $`y \in x`.
> $$`\forall X \exists \bigcap X, \, \forall y, y \in \bigcap X \iff \forall x \in X, y \in x`

Before doing anything, let's create some ergonomic APIs for expressing nonempty sets.

```lean
namespace ZFC

def nonempty : ZFSet → Prop := λ X => ∃ wx, wx ∈ X

@[simp]
theorem nonempty_iff_ne_null
    { X : ZFSet } :
    nonempty X ↔ X ≠ ∅ := by
  let null_spec_mp :=
    λ (x : ZFSet) => (null_spec x).mp
  constructor
  · intro h
    intro hX
    unfold nonempty at h
    rw [hX] at h
    obtain nh := not_exists.mpr null_spec_mp
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
        apply (null_spec_mp x)
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

Now we wrap the intersection theorem into a reusable operator with the same `zfc_set_of` pattern. Unlike family union, intersection requires a nonemptiness hypothesis, so we keep it as a plain function rather than a prefix notation:

```lean
open PUMAC25

namespace ZFC

noncomputable def inter_ (X : ZFSet)
    (hnnX : nonempty X) : ZFSet :=
  zfc_set_of (c1_s2_q1_inter_of_family X hnnX)

theorem inter_spec (X : ZFSet)
    (hnnX : nonempty X) :
    ∀ y, y ∈ inter_ X hnnX ↔
      ∀ x ∈ X, y ∈ x :=
  zfc_set_of_spec (c1_s2_q1_inter_of_family X hnnX)

end ZFC
```

# Existence of Certain Constructions (1.2.2)
%%%
tag := "c1-s2-q2"
%%%

## Existence of Singleton
%%%
tag := "c1-s2-q2-1"
%%%


> Given set $`x`, prove the existence of set $`\{x\}` such that any element of $`\{x\}` is equivalent to $`x`.
> $$`\forall x \exists \{x\} \, \forall z,\, z \in \{x\} \iff z = x`

At first glance, there might be tempting for us to construct a pair $`\{x, \emptyset\}` using the two instances of sets that we have. However, there is a much cleaner approach. While the notation of a singleton makes it look like a collection containing a single token, ZFC defines a set purely by its membership criteria, not by how many syntactically distinct terms we write down.

Looking back at the axioms, the pair $`\{x, x\}` perfectly suited our requirements. The definition of the pair told that $`\forall n, n \in \{x, x\} \iff n = x \lor n = x` which by the logical law of idempotency simplifies to the definition of a singleton : $`\forall n, n \in \{x, x\} \iff n = x`.

```lean
theorem c1_s2_q2_1_exists_singleton
  (x : ZFSet) : ∃ X : ZFSet, ∀ n, n ∈ X ↔ n = x := by
    let ⟨singleton_set, h_singleton⟩ := axiom_pairing x x
    refine ⟨singleton_set, λ ws => ?_⟩
    constructor
    · intro h_ws_memof_singleton
      have h_ws_memof_either := (
        h_singleton ws).mp h_ws_memof_singleton
      exact Or.elim h_ws_memof_either
        id id
    · intro h_ws_eq_x
      exact (h_singleton ws).mpr $ Or.inl h_ws_eq_x
```

We will exploit this characteristic of ZFC membership — focusing on predicates rather than literal element counts — frequently when constructing sets.


## Existence of Binary Union
%%%
tag := "c1-s2-q2-2"
%%%

> Given two sets $`x` and $`y`, there exists a set $`x \cup y` such that every element in it is an element of either $`x` or $`y`
> $$`\forall x, y \exists (x \cup y) \forall z,\, z \in x \cup y \iff z \in x \lor z \in y`

This is relatively easy; pair up $`x` and $`y` and we have a family containing only the $`x` and $`y`. Then construct the family union and we have the union.

```lean
namespace PUMAC25

theorem c1_s2_s2_2_exists_binary_union (x y : ZFSet.{u}) :
    ∃ C : ZFSet.{u},
      ∀ z : ZFSet.{u},
        z ∈ C ↔ z ∈ x ∨ z ∈ y := by
  let ⟨pair_set, h_pair⟩ := axiom_pairing x y
  let ⟨union_set, h_union⟩ := axiom_union pair_set
  refine ⟨union_set, λ z => ?_⟩
  constructor
  · intro hz
    rcases (h_union z).mp hz with ⟨S, hzS, hSpair⟩
    rcases (h_pair S).mp hSpair with (hSx | hSy)
    · left; rw [← hSx]; exact hzS
    · right; rw [← hSy]; exact hzS
  · intro hz_or
    rcases hz_or with (hzx | hzy)
    · apply (h_union z).mpr
      refine ⟨x, hzx, ?_⟩
      exact (h_pair x).mpr (Or.inl rfl)
    · apply (h_union z).mpr
      refine ⟨y, hzy, ?_⟩
      exact (h_pair y).mpr (Or.inr rfl)

noncomputable def cup (x y : ZFSet.{u}) :
    ZFSet.{u} :=
  zfc_set_of (c1_s2_s2_2_exists_binary_union x y)

theorem cup_spec (x y : ZFSet.{u}) :
    ∀ z : ZFSet.{u},
      z ∈ cup x y ↔ z ∈ x ∨ z ∈ y :=
  zfc_set_of_spec (c1_s2_s2_2_exists_binary_union x y)

infix:65 " ∪ " => cup

end PUMAC25
```

## Existence of Binary Intersection
%%%
tag := "c1-s2-q2-3"
%%%

> Given two sets $`x` and $`y`, there exists a set $`x \cap y` such that every element in it is an element of both $`x` and $`y`. This is the binary counterpart of the family intersection we proved in {ref "c1-s1-q1"}[1.2.1].
> $$`\forall x, y \exists (x \cap y) \forall z,\, z \in x \cap y \iff z \in x \land z \in y`

Unlike the family intersection, the binary version carries no nonemptiness condition — if $`x` and $`y` are both empty, the intersection is simply empty. The direct route is separation: filter $`x` by the predicate $`\lambda z.\, z \in y`. No pairing or union is required; the set we are carving out of already exists.

```lean
open ZFC

namespace PUMAC25
theorem c1_s2_q2_3_exists_binary_inter
    (x y : ZFSet.{u}) :
    ∃ C : ZFSet.{u},
      ∀ z : ZFSet.{u},
        z ∈ C ↔ z ∈ x ∧ z ∈ y := by
    let ⟨pair_set, h_pair⟩ := axiom_pairing x y
    let ⟨inter_set, h_inter⟩ := axiom_separation pair_set (λ z => z ∈ x ∧ z ∈ y)
    refine ⟨inter_set, λ wC => ?_⟩
    constructor
    · sorry
    · sorry

noncomputable def cap (x y : ZFSet.{u}) :
    ZFSet.{u} :=
  zfc_set_of
    (c1_s2_q2_3_exists_binary_inter x y)

theorem cap_spec (x y : ZFSet.{u}) :
    ∀ z : ZFSet.{u},
      z ∈ cap x y ↔ z ∈ x ∧ z ∈ y :=
  zfc_set_of_spec
    (c1_s2_q2_3_exists_binary_inter x y)

infix:70 " ∩ " => cap

end PUMAC25
```

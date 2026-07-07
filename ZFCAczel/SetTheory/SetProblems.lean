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

# Intersection of Family
%%%
tag := "c1-s1-q1"
%%%

> _(Problem 1.2.1)_ Given a nonempty set $`X`, prove that there exists a set $`\bigcap X` such that $`y \in \bigcap X` iff $`y \in x` for all $`y \in x`.
> $$`\forall X \exists \bigcap X, \, \forall y, y \in \bigcap X \iff \forall x \in X, y \in x`

Before doing anything, let's create some ergonomic APIs for expressing nonempty sets.

```lean
namespace ZFC

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

# Existence of Certain Constructions
%%%
tag := "c1-s2-q2"
%%%

## Existence of Singleton
%%%
tag := "c1-s2-q2-1"
%%%


> _(Problem 1.2.2.1)_ Given set $`x`, prove the existence of set $`\{x\}` such that any element of $`\{x\}` is equivalent to $`x`.
> $$`\forall x \exists \{x\} \, \forall z,\, z \in \{x\} \iff z = x`

At first glance, there might be tempting for us to construct a pair $`\{x, \emptyset\}` using the two instances of sets that we have, then applying separation to get rid of the $`\emptyset`. However, there is a much cleaner approach. While the notation of a singleton makes it look like a collection containing a single token, ZFC defines a set purely by its membership criteria, not by how many syntactically distinct terms we write down.

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

> _(Problem 1.2.2.2)_ Given two sets $`x` and $`y`, there exists a set $`x \cup y` such that every element in it is an element of either $`x` or $`y`
> $$`\forall x, y \exists (x \cup y) \forall z,\, z \in x \cup y \iff z \in x \lor z \in y`

This is relatively easy; pair up $`x` and $`y` and we have a family containing only the $`x` and $`y`. Then construct the family union and we have the union.

```lean
namespace PUMAC25

theorem c1_s2_q2_2_exists_binary_union (x y : ZFSet.{u}) :
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

end PUMAC25
```

```lean
open PUMAC25

namespace ZFC

noncomputable def bin_union (x y : ZFSet.{u}) :
    ZFSet.{u} :=
  zfc_set_of (c1_s2_q2_2_exists_binary_union x y)

@[simp]
theorem bin_union_spec (x y : ZFSet.{u}) :
    ∀ z : ZFSet.{u},
      z ∈ bin_union x y ↔ z ∈ x ∨ z ∈ y :=
  zfc_set_of_spec (c1_s2_q2_2_exists_binary_union x y)

infix:65 " ∪ " => bin_union

end ZFC
```

## Existence of Binary Intersection
%%%
tag := "c1-s2-q2-3"
%%%

> _(Problem 1.2.2.3)_ Given two sets $`x` and $`y`, there exists a set $`x \cap y` such that every element in it is an element of both $`x` and $`y`. This is the binary counterpart of the family intersection we proved in {ref "c1-s1-q1"}[1.2.1].
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
    let ⟨union_set, h_union⟩ := axiom_union pair_set
    let ⟨inter_set, h_inter⟩ :=
      axiom_separation union_set (λ z => z ∈ x ∧ z ∈ y)
    refine ⟨inter_set, λ wC => ?_⟩
    constructor
    · intro h_wC_memof_inter
      exact ((h_inter wC).mp h_wC_memof_inter).right
    · intro h_wC_memof_both
      suffices h : wC ∈ union_set by
        exact (h_inter wC).mpr ⟨h, h_wC_memof_both⟩
      have h_x_in_pair := (h_pair x).mpr $ Or.inl rfl
      exact (h_union wC).mpr
        $ Exists.intro x ⟨h_wC_memof_both.left, h_x_in_pair⟩

end PUMAC25
```

```lean
open PUMAC25

namespace ZFC

noncomputable def bin_inter (x y : ZFSet.{u}) :
    ZFSet.{u} :=
  zfc_set_of
    (c1_s2_q2_3_exists_binary_inter x y)

@[simp]
theorem bin_inter_spec (x y : ZFSet.{u}) :
    ∀ z : ZFSet.{u},
      z ∈ bin_inter x y ↔ z ∈ x ∧ z ∈ y :=
  zfc_set_of_spec
    (c1_s2_q2_3_exists_binary_inter x y)

infix:70 " ∩ " => bin_inter

end ZFC
```

# Existence of Pair
%%%
tag := "c1-s2-d1"
%%%

> _(Definition 1.2.1)_ For two sets $`x` and $`y`, define the *Kuratowski Ordered Pair* as follows
> $$`(x, y) := \{\{x\}, \{x, y\}\}`

To state this in first-order logic, we must unpack the set-builder notation into the language of ZFC — formulas whose only predicate symbol is $`\in`. The fully expanded sentence reads:

$$`\forall x, y, \exists p, \forall z, \, z \in p \iff (\forall w, w \in z \iff w = x) \lor (\forall w, w \in z \iff w = x \lor w = y)`

This is hard to read, so we introduce two syntactic abbreviations:

$$`Z = \{x\} \triangleq \forall w, w \in Z \iff w = x \\ Z = \{x, y\} \triangleq \forall w, w \in Z \iff w = x \lor w = y`

With these in hand, the statement recovers its familiar shape:

$$`\forall x, y, \exists (x, y), \forall z, \, z \in (x, y) \iff (z = \{x\} \lor z = \{x, y\})`

*A word on notation.* We write $`:=` for a *definition* — a genuinely new construct in ZFC whose existence must be justified by the axioms. We write $`\triangleq` for *syntactic equivalence* — a macro whose left-hand side is nothing more than a textual substitute for its right-hand side. The two $`\triangleq` lines above do not extend ZFC; they exist purely to make the formula fit on a page. When you see $`Z = \{x\}` written anywhere in the development that follows, the actual sentence being asserted is still $`\forall w, w \in Z \iff w = x`.

The good news is that we have already done the heavy lifting: {ref "c1-s2-q2-1"}[Q1.2.2.1] proved that a witness for $`\{x\}` exists, the pair axiom itself guarantees a witness for $`\{x, y\}`, and pairing those two witnesses together gives us a witness for $`\{\{x\}, \{x, y\}\}`. The macros sugarize right back to existence statements we already know how to satisfy.

The two $`\triangleq` abbreviations translate directly into `Prop`-valued predicates — they name a membership condition without constructing a `ZFSet`.

```lean
open ZFC

namespace ZFC

def is_singleton_of (Z x : ZFSet.{u}) : Prop :=
  ∀ w, w ∈ Z ↔ w = x

def is_upair_of (Z x y : ZFSet.{u}) : Prop :=
  ∀ w, w ∈ Z ↔ w = x ∨ w = y

end ZFC
```

We wrap the existence theorems from {ref "c1-s2-q2"}[Q1.2.2] as `noncomputable def`s via `zfc_set_of`, each bundled with its membership spec lemma.

```lean
namespace ZFC

noncomputable def singleton (x : ZFSet.{u}) : ZFSet.{u} :=
  zfc_set_of (c1_s2_q2_1_exists_singleton x)

@[simp]
theorem singleton_spec (x : ZFSet.{u}) :
    ∀ z, z ∈ singleton x ↔ z = x :=
  zfc_set_of_spec (c1_s2_q2_1_exists_singleton x)

noncomputable def upair (x y : ZFSet.{u}) : ZFSet.{u} :=
  zfc_set_of (axiom_pairing x y)

@[simp]
theorem upair_spec (x y : ZFSet.{u}) :
    ∀ z, z ∈ upair x y ↔ z = x ∨ z = y :=
  zfc_set_of_spec (axiom_pairing x y)

end ZFC
```

Immediate membership facts: the two elements are indeed members of their own unordered pair.

```lean
namespace ZFC

@[simp]
theorem mem_upair_left : x ∈ upair x y :=
  (upair_spec x y x).mpr (by simp)

@[simp]
theorem mem_upair_right : y ∈ upair x y :=
  (upair_spec x y y).mpr (by simp)

end ZFC
```

When does an unordered pair collapse to a singleton? The next two lemmas characterize the situation.

```lean
namespace ZFC

theorem is_singleton_of_upair_iff {x y z : ZFSet.{u}}
  : is_singleton_of (upair y z) x ↔ x = y ∧ x = z := by
    unfold is_singleton_of
    constructor
    · intro h
      have hy : x = y := by
        have hy_mem := (upair_spec y z y).mpr (Or.inl rfl)
        exact ((h y).mp hy_mem).symm
      have hz : x = z := by
        have hz_mem := (upair_spec y z z).mpr (Or.inr rfl)
        exact ((h z).mp hz_mem).symm
      exact ⟨hy, hz⟩
    · intro ⟨h1, h2⟩
      rw [← h1, ← h2]
      intro w
      constructor
      · intro h_w_upair
        have h' := (upair_spec x x w).mp h_w_upair
        exact Or.elim h' id id
      · intro h_w_eq_x
        rw [h_w_eq_x]
        apply (upair_spec x x x).mpr
        left; rfl

theorem is_singleton_of_upair_left_iff
  : is_singleton_of (upair x y) x ↔ x = y :=
    (is_singleton_of_upair_iff (y := x) (z := y)).trans
      ⟨fun ⟨_, hy⟩ => hy, fun h => ⟨rfl, h⟩⟩

theorem is_singleton_of_upair_right_iff
  : is_singleton_of (upair y x) x ↔ x = y :=
    (is_singleton_of_upair_iff (y := y) (z := x)).trans
      ⟨fun ⟨hx, _⟩ => hx, fun h => ⟨h, rfl⟩⟩

end ZFC
```

The singleton construction respects extensionality: a set is a singleton of `x` precisely when it equals `{x}`. A direct consequence is that singletons are injective.

```lean
namespace ZFC

@[simp]
theorem is_singleton_of_ext_iff
  : is_singleton_of X x ↔ singleton x = X := by
    constructor
    · intro h
      unfold is_singleton_of at h
      apply (axiom_ext (singleton x) X).mp
      intro witness
      constructor
      · intro hwx
        have h_w_eq_x := (singleton_spec x witness).mp hwx
        rw [h]
        assumption
      · intro h_w_memof_X
        apply (singleton_spec x witness).mpr
        exact (h witness).mp h_w_memof_X
    · intro h
      unfold is_singleton_of
      rw [←h]
      exact singleton_spec x

@[simp]
theorem singleton_inj :
  (singleton a = singleton b) ↔ a = b := by
  constructor
  · intro h
    have hext :=
      (axiom_ext (singleton a) (singleton b)).mpr h
    have ha := hext a
    have h_a_memof_sa := (singleton_spec a a).mpr rfl
    have h_a_memof_sb := ha.mp h_a_memof_sa
    exact (singleton_spec b a).mp h_a_memof_sb
  · simp_all

theorem eq_of_is_singleton_of_singleton_iff
    : is_singleton_of (singleton x) z ↔ x = z := by
    constructor
    · intro h
      have p := is_singleton_of_ext_iff.mp h
      symm
      exact singleton_inj.mp p
    · intro h
      rw [h]
      exact is_singleton_of_ext_iff.mpr rfl

end ZFC
```

Similarly for unordered pairs: if `{x, y}` satisfies the unordered-pair predicate for `z` and `w`, the two unordered pairs are extensionally equal.

```lean
namespace ZFC

theorem is_upair_of_ext_iff {Z x y : ZFSet.{u}}
  : is_upair_of Z x y ↔ upair x y = Z := by
    constructor
    · intro h
      apply (axiom_ext (upair x y) Z).mp
      intro w
      rw [h, upair_spec x y w]
    · intro h
      rw [← h]
      exact upair_spec x y

theorem upair_ext_of_is_upair_of_iff {x y z w : ZFSet.{u}}
  : is_upair_of (upair x y) z w ↔ upair x y = upair z w :=
    (is_upair_of_ext_iff (Z := upair x y)).trans
      ⟨Eq.symm, Eq.symm⟩


end ZFC
```

With these primitives in hand, constructing the Kuratowski ordered pair becomes a straightforward composition: pair up the singleton `{x}` and the unordered pair `{x, y}`.

```lean
namespace ZFC

theorem exists_kuratowski_pair (x y : ZFSet.{u}) :
    ∃ p : ZFSet.{u},
      ∀ z, z ∈ p ↔
        (is_singleton_of z x ∨ is_upair_of z x y) := by
        have ⟨set_sing, h_singleton⟩ :=
          c1_s2_q2_1_exists_singleton x
        have ⟨set_upair, h_upair⟩ := axiom_pairing x y
        have ⟨set_opair, h_opair⟩ :=
          axiom_pairing set_sing set_upair
        refine ⟨set_opair, λ wo => ?_⟩
        constructor
        · intro h_wo_memof_opair
          have h_x_eq_dij :=
            (h_opair wo).mp h_wo_memof_opair
          refine Or.elim h_x_eq_dij ?_ ?_
          · intro h_wo_eq_sing
            left
            unfold is_singleton_of
            rw [h_wo_eq_sing]
            assumption
          · intro h_wo_eq_upair
            right
            unfold is_upair_of
            rw [h_wo_eq_upair]
            assumption
        · intro h_wo_eq_either
          apply (h_opair wo).mpr
          refine Or.elim h_wo_eq_either ?_ ?_
          · intro h_wo_is_sing
            left
            unfold is_singleton_of at h_wo_is_sing
            apply (axiom_ext wo set_sing).mp
            simp_all
          · intro h_wo_is_upair
            right
            unfold is_upair_of at h_wo_is_upair
            apply (axiom_ext wo set_upair).mp
            simp_all

noncomputable def ordered_pair
  (a b : ZFSet.{u}) : ZFSet.{u} :=
  zfc_set_of (exists_kuratowski_pair a b)

notation:60 "⟪" a ", " b "⟫" => ordered_pair a b

@[simp]
theorem ordered_pair_spec (a b : ZFSet.{u})
  : ∀ z, z ∈ ⟪a, b⟫ ↔
    (is_singleton_of z a ∨ is_upair_of z a b) :=
  zfc_set_of_spec (exists_kuratowski_pair a b)

theorem left_in_ordered_pair : singleton a ∈ ⟪a, b⟫ := by
  apply (ordered_pair_spec a b $ singleton a).mpr
  left
  exact singleton_spec a

theorem upair_in_ordered_pair : upair a b ∈ ⟪a, b⟫ := by
  apply (ordered_pair_spec a b $ upair a b).mpr
  right
  exact upair_spec a b

end ZFC
```

# Component-Wise Extensional Equality for Pairs
%%%
tag := "c1-s2-q3"
%%%

> _(Problem 1.2.3)_ Prove that two pairs are equal if their components are equal.
> $$`(x, y) = (z, w) \iff x = z \land y = w`

```lean
open ZFC

namespace PUMAC25
theorem c1_s2_q3_eq_pairs :
  ⟪x, y⟫ = ⟪z, w⟫ ↔ x = z ∧ y = w := by
    constructor
    · intro h_pair_eq
      have spec_xy := ordered_pair_spec x y
      have spec_zw := ordered_pair_spec z w
      have mem_ext : ∀ s, s ∈ ⟪x, y⟫ ↔ s ∈ ⟪z, w⟫ := by
        intro s; rw [h_pair_eq]
      have sgl_x_in_xy : singleton x ∈ ⟪x, y⟫ := by
        rw [spec_xy (singleton x)]
        left; exact singleton_spec x
      have sgl_x_in_zw : singleton x ∈ ⟪z, w⟫ :=
        (mem_ext (singleton x)).mp sgl_x_in_xy

      have hxz : x = z := by
        rcases (spec_zw (singleton x)).mp
          sgl_x_in_zw with (hsgl | hup)
        · exact eq_of_is_singleton_of_singleton_iff.mp hsgl
        · unfold is_upair_of at hup
          have hz_mem_up := hup z
          have hz_eq_x := hz_mem_up.mpr $ Or.inl rfl
          exact ((singleton_spec x z).mp hz_eq_x).symm

      have up_xy_in_xy : upair x y ∈ ⟪x, y⟫ := by
        rw [spec_xy (upair x y)]
        right; exact upair_spec x y
      have up_xy_in_zw : upair x y ∈ ⟪z, w⟫ :=
        (mem_ext (upair x y)).mp up_xy_in_xy
      have hyw : y = w := by
        rcases (spec_zw (upair x y)).mp
          up_xy_in_zw with (hsgl | hup)
        · unfold is_singleton_of at hsgl
          have hyz : y = z := (hsgl y).mp mem_upair_right
          have spec_zz := ordered_pair_spec z z
          have up_zw_in_zz : upair z w ∈ ⟪z, z⟫ := by
            have up_zw_in_zw : upair z w ∈ ⟪z, w⟫ := by
              rw [spec_zw (upair z w)]
              right; exact upair_spec z w
            rw [hxz, hyz] at h_pair_eq
            rw [h_pair_eq]
            exact up_zw_in_zw
          rcases (spec_zz (upair z w)).mp
            up_zw_in_zz with (hsgl' | hup')
          · unfold is_singleton_of at hsgl'
            exact ((hsgl' w).mp mem_upair_right).trans
              hyz.symm |>.symm
          · have up_eq : upair z w = upair z z :=
              upair_ext_of_is_upair_of_iff.mp hup'
            have hwz : w = z := by
              have h_mem := (axiom_ext (upair z w)
                (upair z z)).mpr up_eq
              have hw_in_zz : w ∈ upair z z := (h_mem w).mp
                ((upair_spec z w w).mpr (Or.inr rfl))
              rcases (upair_spec z z w).mp
                hw_in_zz with (h | h)
              · exact h
              · exact h
            exact hwz.trans hyz.symm |>.symm
        · have up_eq : upair x y = upair z w :=
            upair_ext_of_is_upair_of_iff.mp hup
          have hy_cases : y = z ∨ y = w := by
            have h_mem := (axiom_ext (upair x y)
              (upair z w)).mpr up_eq
            have hy_mem : y ∈ upair z w :=
              (h_mem y).mp mem_upair_right
            exact (upair_spec z w y).mp hy_mem
          rcases hy_cases with (hyz | hyw')
          · rw [hxz, hyz] at up_eq
            have hwz : w = z := by
              have h_mem :=
                (axiom_ext (upair z z) (upair z w)).mpr
                  up_eq
              have hw_in_zz : w ∈ upair z z := (h_mem w).mpr
                ((upair_spec z w w).mpr (Or.inr rfl))
              rcases (upair_spec z z w).mp
                hw_in_zz with (h | h)
              · exact h
              · exact h
            rw [hyz, hwz]
          · exact hyw'
      exact ⟨hxz, hyw⟩
    · intro ⟨hx, hy⟩
      rw [hx, hy]

end PUMAC25
```

# Existence of the Cartesian Product
%%%
tag := "c1-s2-q4"
%%%

> _(Problem 1.2.4)_
> Given two sets $`X` and $`Y`, show that we can form the Cartesian product $`X \times Y`, a set of ordered pairs $`(x, y)`, where $`x \in X` and $`y \in Y`.
> $$`\forall X, Y, \exists (X \times Y), \forall a, \, a \in (X \times Y) \iff \exists x, \exists y, \, (a = (x, y) \land x \in X \land y \in Y)`


Now this problem is getting a bit hard. It is obvious that we should try using separation (or else we will be recursively doing unions on pairs and singletons which is just an absolute nightmare for FOL semantics), but on which parent set?

The key to this construction is the sequential application of the *Axiom of Power Set*:

1. We take the union of our two sets to form a base domain of individual coordinates: $`X \cup Y`.
2. We take the power set of this union: $`\mathcal{P}(X \cup Y)`. This set automatically contains every possible flat collection formed from the elements of $`X` and $`Y`, guaranteeing the inclusion of the singletons $`\{x\}` and pairs $`\{x, y\}`.
3. Because the Kuratowski definition of an ordered pair requires a nested structural architecture — $`(x, y) = \{\{x\}, \{x, y\}\}` — a flat collection is insufficient. We must take the power set a second time to yield $`\mathcal{P}(\mathcal{P}(X \cup Y))`.

This nested power set serves as our definitive parent set, as it securely encapsulates every possible set of singletons and pairs. We can then cleanly invoke the Axiom Schema of Specification over this domain to isolate the exact elements that satisfy our product predicate:

$$`X \times Y = \{ a \in \mathcal{P}(\mathcal{P}(X \cup Y)) \mid \exists x \in X, \exists y \in Y, a = (x, y) \}`

To formalize this, we first need to formalize our separation predicate in a ergonomic way

```lean
open ZFC

def is_pair_over_sets (X Y : ZFSet) (a : ZFSet) : Prop :=
    ∃ x y, x ∈ X ∧ y ∈ Y ∧ a = ⟪x, y⟫

namespace PUMAC26

theorem c1_s2_q4_exists_cart_prod (X Y : ZFSet.{u}) :
  ∃ S : ZFSet.{u}, ∀ s, s ∈ S
    ↔ is_pair_over_sets X Y s := by
  have h_union := bin_union_spec X Y
  have ⟨power₁, h_power₁⟩ := axiom_powerset (X ∪ Y)
  have ⟨power₂, h_power₂⟩ := axiom_powerset power₁
  have ⟨prod_set, h_prod⟩ :=
    axiom_separation power₂ (is_pair_over_sets X Y)
  refine ⟨prod_set, λ wp => ?_⟩
  constructor
  · intro h_wp_memof_prod
    exact ((h_prod wp).mp h_wp_memof_prod).right
  · intro h_wp_is_pair
    apply (h_prod wp).mpr
    refine ⟨?_, h_wp_is_pair⟩
    rw [h_power₂]
    intro n hn
    rw [h_power₁]
    intro a ha
    have h := h_union a
    apply h.mpr
    unfold is_pair_over_sets at h_wp_is_pair
    rcases h_wp_is_pair with ⟨x, y, hx, hy, rfl⟩
    have h_n_cases := (ordered_pair_spec x y n).mp hn
    rcases h_n_cases with ( h_sing | h_upair )
    · unfold is_singleton_of at h_sing
      rw [(h_sing a).mp ha]
      left; assumption
    · unfold is_upair_of at h_upair
      rcases (h_upair a).mp ha with ( h_ax | h_ay )
      · rw [h_ax]; left; assumption
      · rw [h_ay]; right; assumption

end PUMAC26
```

Let's collect some useful lemmas and constructs along the way:

```lean
open PUMAC26
namespace ZFC
noncomputable def cartesian_product (X Y : ZFSet) : ZFSet
  := zfc_set_of $ c1_s2_q4_exists_cart_prod X Y

infix:70 " × " => cartesian_product

@[simp]
theorem cartesian_product_spec
  : ∀ a, a ∈ X × Y ↔ ∃ x y : ZFSet,
    x ∈ X ∧ y ∈ Y ∧ a = ⟪x, y⟫ :=
      zfc_set_of_spec $ c1_s2_q4_exists_cart_prod X Y
end ZFC
```

# Relations and Functions
%%%
tag := "c1-s2-d2"
%%%

> _(Definition 1.2.2)_ A *relation* is a set $`R` consisting of ordered pairs. We usually write $`x\ R\ y` as a shorthand for $`(x, y) \in R`.
> A relation $`f` is a *function* if, for any set $`x`, there is at most one set $`y` such that $`(x, y) \in f`. If such a $`y` exists, we write $`f(x) = y`.

There is really not much to formalize about relations, but we can create a binary version of the axiom of seperation, but over the cartesian product of sets to extract a relation particularly over two sets. That is, $`x\ R\ y` only when $`x \in X` and $`y \in Y`.

```lean
namespace ZFC

def relation_pred₂ (X Y : ZFSet) (φ : ZFSet → ZFSet → Prop)
  : ZFSet → Prop := λ a : ZFSet =>
    ∃ x y : ZFSet, x ∈ X ∧ y ∈ Y ∧ a = ⟪x, y⟫ ∧ φ x y

def pure_relation (R : ZFSet) :=
  ∀ p, p ∈ R → ∃ x y, p = ⟪x, y⟫

theorem separation₂ (X Y : ZFSet) (φ : ZFSet → ZFSet → Prop)
  : ∃ S : ZFSet, ∀ a, a ∈ S
    ↔ ∃ x y, x ∈ X ∧ y ∈ Y ∧ a = ⟪x, y⟫ ∧ φ x y := by
      have ⟨sep, h_sep⟩ := axiom_separation (X × Y)
        $ relation_pred₂ X Y φ
      refine ⟨sep, λ w => ?_ ⟩
      constructor
      · intro h
        unfold relation_pred₂ at h_sep
        exact ((h_sep w).mp h).right
      · intro h
        refine ((h_sep w).mpr ⟨?_, h⟩)
        apply (cartesian_product_spec w).mpr
        rcases h with ⟨x, y, hx, hy, hw, hφ⟩
        refine ⟨x, y, hx, hy, hw⟩

end ZFC
```

As for functions, we can define a convenient predicate:

```lean
namespace ZFC

def is_function (F : ZFSet) :=
  pure_relation F ∧
    (∀ x, ∀ y₁ y₂, ⟪x, y₁⟫ ∈ F → ⟪x, y₂⟫ ∈ F → y₁ = y₂)

end ZFC
```

And the identity function just for fun (which is the diagonal relation):

```lean
namespace ZFC

theorem exists_diagonal (D : ZFSet) :
  ∃ S : ZFSet, ∀ s: ZFSet, s ∈ S  ↔ ∃ x ∈ D,
    s = (singleton (singleton x)) := by sorry

noncomputable def zfc_id (D : ZFSet) :=
  zfc_set_of $ exists_diagonal D

@[simp]
theorem id_spec (D : ZFSet) :
  ∀ s, s ∈ zfc_id D ↔ ∃ x ∈ D, s = singleton (singleton x)
    := zfc_set_of_spec $ exists_diagonal D

theorem id_pure : ∀ D, pure_relation $ zfc_id D := by
  intro domain
  unfold pure_relation
  intro diag_p
  intro h
  have ⟨wx, ⟨h_wx_memof_domain, h_diag_eq_sswx⟩⟩
    := (id_spec domain diag_p).mp h
  refine ⟨wx, wx, ?_⟩
  simp_all
  apply (axiom_ext _ _).mp
  intro wsx
  constructor
  · intro h_wsx_memof_sswx
    rw [(singleton_spec _ _).mp h_wsx_memof_sswx]
    simp_all
  · intro h_wsx_memof_opair
    rw [(singleton_spec _ _)]
    have h' := (ordered_pair_spec _ _ _).mp
      h_wsx_memof_opair
    rcases h' with ( h_singleton | h_upair )
    · simp_all
    · have h' := (ext_iff_of_spec_left $ upair_spec _ _).mp
        $ is_upair_of_ext_iff.mp h_upair
      apply (ext_iff_of_spec_right $ singleton_spec _).mpr
      simp_all


end ZFC


#eval 1
```

Note that in ZFC defining the total function `id` is impossible. This is because in order to do so, you are carving out a subset of $`V^2`, which is the cartesian product of "the collection of every set $`V`" with itself, which just does not exist as a set. Here, $`V` is actually what's known as a proper class, which will be introduced later on. But what you need to know now is that a proper class is something that could *never* be formulated as a set, therefore it is also impossible to form a relation over it, not to say a function.

Therefore we chose to parametrize the `id` function to a *local diagonal relation* — you construct the domain set $`D`, feed the set to the relation, and the relation is only defined over $`D^2`. This completely sidesteps the issue of needing an impossible parent set to begin with.

# Existence of Domain and Range
%%%
tag := "c1-s2-q5"
%%%

> _(Problem 1.2.5)_ Let $`R` be a relation. Show that we can form the sets
> $$`\text{dom}(R) = \{x : \exists (x, y) \in R\} \quad \text{and} \quad \text{ran}(R) = \{y : \exists (x, y) \in R\}`
> Called the *domain* and *range* of the sets, respectively.

While the Cartesian product required us to iteratively scale up our universe using the Axiom of Power Set to accommodate nested Kuratowski architectures, isolating the domain and range demands the exact inverse operation. A relation $`R` is a set of ordered pairs, meaning its elements look like $`a = \{\{x\},\{x,y\}\}`

We achieve this structural flattening through the sequential application of the `axiom_union`

1. *First Flattening ($`\bigcup R`):* Taking the union of the relation $`R` dissolves the outermost layer of the ordered pairs. Since the elements of $`R` are of the form $`\{\{x\}, \{x, y\}\}`, their union collects all the constituent singletons and unordered pairs into a single flat set:
$$`\bigcup R = \{ s \mid \exists a \in R, s \in a \} = \{ \{x\}, \{x, y\}, \{z\}, \{z, w\}, \dots \}`
2. *Second Flattening ($`\bigcup\bigcup R`):* We are still one layer too deep; our coordinates are trapped inside singletons and doubletons. Applying the Axiom of Union a second time unpacks these collections, liberating the individual coordinate elements themselves:
$$`\bigcup\bigcup R = \{ x \mid \exists s \in \bigcup R, x \in s \} = \{ x, y, z, w, \dots \}`

This twice-flattened set, $`\bigcup\bigcup R`, serves as our definitive parent domain. It is guaranteed to contain every single coordinate that appears anywhere inside any ordered pair in $`R`.

With a secure bounding set established, we can cleanly invoke the `axiom_separation` to filter out the domain and range coordinates using explicit existential predicates:

$$`\text{dom}(R) = \{ x \in \bigcup\bigcup R \mid \exists y, (x, y) \in R \}`
$$`\text{ran}(R) = \{ y \in \bigcup\bigcup R \mid \exists x, (x, y) \in R \}`

To formalize this in Lean, we can define ergonomic separation predicates for the domain and range components:

```lean
open ZFC

def is_domain_elem_of (R : ZFSet) (x : ZFSet) : Prop :=
    ∃ y, ⟪x, y⟫ ∈ R

def is_range_elem_of (R : ZFSet) (y : ZFSet) : Prop :=
    ∃ x, ⟪x, y⟫ ∈ R

namespace PUMAC26

theorem c1_s2_q5_exists_dom (R : ZFSet.{u}) :
    ∃ Dom : ZFSet.{u}, ∀ x, x ∈ Dom
      ↔ is_domain_elem_of R x := by
    have ⟨union₁, h_union₁⟩ := axiom_union R
    have ⟨union₂, h_union₂⟩ := axiom_union union₁
    have ⟨dom_set, h_dom⟩ :=
      axiom_separation union₂ $ is_domain_elem_of R
    refine ⟨dom_set, λ wd => ?_⟩
    constructor
    · intro h_wd_memof_domain
      exact ((h_dom wd).mp h_wd_memof_domain).right
    · intro h_wd_is_dom_elem
      refine (h_dom wd).mpr ⟨?_, h_wd_is_dom_elem⟩
      unfold is_domain_elem_of at h_wd_is_dom_elem
      apply (h_union₂ wd).mpr
      rcases h_wd_is_dom_elem with ⟨wy, hwy⟩
      have h_swd_memof_dompair
        : singleton wd ∈ ⟪wd, wy⟫ := by simp_all
      have h_up_memof_dompair
        : upair wd wy ∈ ⟪wd, wy⟫ := upair_in_ordered_pair
      have h_swd_memof_union₁
        : singleton wd ∈ union₁ :=
          (h_union₁ $ singleton wd).mpr
            ⟨⟪wd, wy⟫, ⟨h_swd_memof_dompair, hwy⟩⟩
      have h_wd_memof_sing
        : wd ∈ singleton wd := by simp_all
      exact
        ⟨singleton wd,
          ⟨h_wd_memof_sing, h_swd_memof_union₁⟩⟩


theorem c1_s2_q5_exists_ran (R : ZFSet.{u}) :
    ∃ Ran : ZFSet.{u}, ∀ y, y ∈ Ran
      ↔ is_range_elem_of R y := by
    sorry

end PUMAC26
```

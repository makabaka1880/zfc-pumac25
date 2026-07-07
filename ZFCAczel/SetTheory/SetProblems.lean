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

# Intersection of Family (Q1.2.1)
%%%
tag := "c1-s1-q1"
%%%

> Given a nonempty set $`X`, prove that there exists a set $`\bigcap X` such that $`y \in \bigcap X` iff $`y \in x` for all $`y \in x`.
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

# Existence of Certain Constructions (Q1.2.2)
%%%
tag := "c1-s2-q2"
%%%

## Existence of Singleton
%%%
tag := "c1-s2-q2-1"
%%%


> Given set $`x`, prove the existence of set $`\{x\}` such that any element of $`\{x\}` is equivalent to $`x`.
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

noncomputable def bin_union (x y : ZFSet.{u}) :
    ZFSet.{u} :=
  zfc_set_of (c1_s2_s2_2_exists_binary_union x y)

theorem bin_union_spec (x y : ZFSet.{u}) :
    ∀ z : ZFSet.{u},
      z ∈ bin_union x y ↔ z ∈ x ∨ z ∈ y :=
  zfc_set_of_spec (c1_s2_s2_2_exists_binary_union x y)

infix:65 " ∪ " => bin_union

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

# Existence of Pair (D1.2.1)
%%%
tag := "c1-s2-d1"
%%%

> For two sets $`x` and $`y`, define the _Kuratowski Ordered Pair_ as follows
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

def is_uPair_of (Z x y : ZFSet.{u}) : Prop :=
  ∀ w, w ∈ Z ↔ w = x ∨ w = y

end ZFC
```

We wrap the existence theorems from {ref "c1-s2-q2"}[Q1.2.2] as `noncomputable def`s via `zfc_set_of`, each bundled with its membership spec lemma.

```lean
namespace ZFC

noncomputable def singleton (x : ZFSet.{u}) : ZFSet.{u} :=
  zfc_set_of (c1_s2_q2_1_exists_singleton x)

theorem singleton_spec (x : ZFSet.{u}) :
    ∀ z, z ∈ singleton x ↔ z = x :=
  zfc_set_of_spec (c1_s2_q2_1_exists_singleton x)

noncomputable def uPair (x y : ZFSet.{u}) : ZFSet.{u} :=
  zfc_set_of (axiom_pairing x y)

theorem uPair_spec (x y : ZFSet.{u}) :
    ∀ z, z ∈ uPair x y ↔ z = x ∨ z = y :=
  zfc_set_of_spec (axiom_pairing x y)

end ZFC
```

Immediate membership facts: the two elements are indeed members of their own unordered pair.

```lean
namespace ZFC

theorem mem_upair_left : x ∈ uPair x y :=
  (uPair_spec x y x).mpr (by simp)

theorem mem_upair_right : y ∈ uPair x y :=
  (uPair_spec x y y).mpr (by simp)

end ZFC
```

When does an unordered pair collapse to a singleton? The next two lemmas characterize the situation.

```lean
namespace ZFC

theorem is_singleton_of_upair_left_iff
  : is_singleton_of (uPair x y) x ↔ x = y := by
    unfold is_singleton_of
    constructor
    · intro h
      symm
      exact (h y).mp mem_upair_right
    · intro h
      rw [h]
      intro w
      constructor
      · intro h_w_upair
        have h' := (uPair_spec y y w).mp h_w_upair
        exact Or.elim h' id id
      · intro h_w_eq_y
        rw [h_w_eq_y]
        apply (uPair_spec y y y).mpr
        left; rfl


theorem is_singleton_of_upair_right_iff
  : is_singleton_of (uPair y x) x ↔ x = y := by
    unfold is_singleton_of
    constructor
    · intro h
      symm
      exact (h y).mp mem_upair_left
    · intro h
      rw [h]
      intro w
      constructor
      · intro h_w_upair
        have h' := (uPair_spec y y w).mp h_w_upair
        exact Or.elim h' id id
      · intro h_w_eq_y
        rw [h_w_eq_y]
        apply (uPair_spec y y y).mpr
        left; rfl

end ZFC
```

The singleton construction respects extensionality: a set is a singleton of `x` precisely when it equals `{x}`. A direct consequence is that singletons are injective.

```lean
namespace ZFC

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

theorem eq_of_is_singleton_of_singleton {x z : ZFSet.{u}}
    (h : is_singleton_of (singleton x) z) : x = z := by
    have p := is_singleton_of_ext_iff.mp h
    symm
    exact singleton_inj.mp p

end ZFC
```

Similarly for unordered pairs: if `{x, y}` satisfies the unordered-pair predicate for `z` and `w`, the two unordered pairs are extensionally equal.

```lean
namespace ZFC

theorem upair_ext_of_is_upair_of {x y z w : ZFSet.{u}}
    (h : is_uPair_of (uPair x y) z w) :
    uPair x y = uPair z w := by
  apply (axiom_ext (uPair x y) (uPair z w)).mp
  intro v
  rw [h, uPair_spec z w v]

end ZFC
```

With these primitives in hand, constructing the Kuratowski ordered pair becomes a straightforward composition: pair up the singleton `{x}` and the unordered pair `{x, y}`.

```lean
namespace ZFC

theorem exists_kuratowski_pair (x y : ZFSet.{u}) :
    ∃ p : ZFSet.{u},
      ∀ z, z ∈ p ↔
        (is_singleton_of z x ∨ is_uPair_of z x y) := by
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
            unfold is_uPair_of
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
            unfold is_uPair_of at h_wo_is_upair
            apply (axiom_ext wo set_upair).mp
            simp_all

noncomputable def orderedPair
  (a b : ZFSet.{u}) : ZFSet.{u} :=
  zfc_set_of (exists_kuratowski_pair a b)

notation:60 "⟪" a ", " b "⟫" => orderedPair a b

theorem orderedPair_spec (a b : ZFSet.{u})
  : ∀ z, z ∈ ⟪a, b⟫ ↔
    (is_singleton_of z a ∨ is_uPair_of z a b) :=
  zfc_set_of_spec (exists_kuratowski_pair a b)

end ZFC
```

# Component-Wise Extensional Equality for Pairs (Q1.2.3)
%%%
tag := "c1-s2-q3"
%%%

> Prove that two pairs are equal if their components are equal.
> $$`(x, y) = (z, w) \iff x = z \land y = w`

```lean
open ZFC

namespace PUMAC25
theorem c1_s2_q3_eq_pairs :
  ⟪x, y⟫ = ⟪z, w⟫ ↔ x = z ∧ y = w := by
    constructor
    · intro h_pair_eq
      have spec_xy := orderedPair_spec x y
      have spec_zw := orderedPair_spec z w
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
        · exact eq_of_is_singleton_of_singleton hsgl
        · unfold is_uPair_of at hup
          have hz_mem_up := hup z
          have hz_eq_x := hz_mem_up.mpr $ Or.inl rfl
          exact ((singleton_spec x z).mp hz_eq_x).symm

      have up_xy_in_xy : uPair x y ∈ ⟪x, y⟫ := by
        rw [spec_xy (uPair x y)]
        right; exact uPair_spec x y
      have up_xy_in_zw : uPair x y ∈ ⟪z, w⟫ :=
        (mem_ext (uPair x y)).mp up_xy_in_xy
      have hyw : y = w := by
        rcases (spec_zw (uPair x y)).mp
          up_xy_in_zw with (hsgl | hup)
        · unfold is_singleton_of at hsgl
          have hyz : y = z := (hsgl y).mp mem_upair_right
          have spec_zz := orderedPair_spec z z
          have up_zw_in_zz : uPair z w ∈ ⟪z, z⟫ := by
            have up_zw_in_zw : uPair z w ∈ ⟪z, w⟫ := by
              rw [spec_zw (uPair z w)]
              right; exact uPair_spec z w
            rw [hxz, hyz] at h_pair_eq
            rw [h_pair_eq]
            exact up_zw_in_zw
          rcases (spec_zz (uPair z w)).mp
            up_zw_in_zz with (hsgl' | hup')
          · unfold is_singleton_of at hsgl'
            exact ((hsgl' w).mp mem_upair_right).trans
              hyz.symm |>.symm
          · have up_eq : uPair z w = uPair z z :=
              upair_ext_of_is_upair_of hup'
            have hwz : w = z := by
              have h_mem := (axiom_ext (uPair z w)
                (uPair z z)).mpr up_eq
              have hw_in_zz : w ∈ uPair z z := (h_mem w).mp
                ((uPair_spec z w w).mpr (Or.inr rfl))
              rcases (uPair_spec z z w).mp
                hw_in_zz with (h | h)
              · exact h
              · exact h
            exact hwz.trans hyz.symm |>.symm
        · have up_eq : uPair x y = uPair z w :=
            upair_ext_of_is_upair_of hup
          have hy_cases : y = z ∨ y = w := by
            have h_mem := (axiom_ext (uPair x y)
              (uPair z w)).mpr up_eq
            have hy_mem : y ∈ uPair z w :=
              (h_mem y).mp mem_upair_right
            exact (uPair_spec z w y).mp hy_mem
          rcases hy_cases with (hyz | hyw')
          · rw [hxz, hyz] at up_eq
            have hwz : w = z := by
              have h_mem :=
                (axiom_ext (uPair z z) (uPair z w)).mpr
                  up_eq
              have hw_in_zz : w ∈ uPair z z := (h_mem w).mpr
                ((uPair_spec z w w).mpr (Or.inr rfl))
              rcases (uPair_spec z z w).mp
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
    have h_n_cases := (orderedPair_spec x y n).mp hn
    rcases h_n_cases with ( h_sing | h_upair )
    · unfold is_singleton_of at h_sing
      rw [(h_sing a).mp ha]
      left; assumption
    · unfold is_uPair_of at h_upair
      rcases (h_upair a).mp ha with ( h_ax | h_ay )
      · rw [h_ax]; left; assumption
      · rw [h_ay]; right; assumption

noncomputable def cartesian_product (X Y : ZFSet) : ZFSet
  := zfc_set_of $ c1_s2_q4_exists_cart_prod X Y

infix:70 " × " => cartesian_product

theorem cartesian_product_spec
  : ∀ a, a ∈ X × Y ↔ ∃ x y : ZFSet,
    x ∈ X ∧ y ∈ Y ∧ a = ⟪x, y⟫ :=
      zfc_set_of_spec $ c1_s2_q4_exists_cart_prod X Y

end PUMAC26
```

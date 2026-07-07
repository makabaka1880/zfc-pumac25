/-
Copyright (c) 2025. All rights reserved.
-/

import VersoManual
import ZFCAczel.Meta.Lean
import ZFCAczel.Papers
import ZFCAczel.SetTheory.Encoding
import Init.Data.Nat.Basic
import Init.Data.Nat.Linear

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Verso Code External

open ZFCAczel

#doc (Manual) "The Axioms of Zermelo-Fraenkel" =>
%%%
file := "ZFAxoims"
tag := "c1-s3-zf-axioms"
%%%

In this chapter we lay out the axioms of Zermelo–Fraenkel set theory (ZF). These axioms replace the naive comprehension principle discussed in the previous chapter with a carefully curated collection of set-existence principles: extensionality tells us when two sets are equal, while pairing, union, power set, separation, and replacement tell us how to build new sets from old ones. To this list we append the Axiom of Choice, which is independent of ZF but indispensable for much of modern mathematics. The resulting system is known as *ZFC* — Zermelo–Fraenkel set theory with Choice.

# Extensional Equality

> Two sets are equal if and only if they have exactly the same elements.
> $$`\forall A, B \, (\forall x, x \in A \iff x \in B) \iff A = B`

Extensionality is the defining principle of ZF: a set is nothing more than the collection of its members. We begin in a namespace `PreZFC` that collects the PSet-level definitions:

```lean
namespace PreZFC

axiom zfc_ext_pset (A B : PSet.{u}) :
    (∀ x : PSet.{u}, x ∈ A ↔ x ∈ B) ↔ A ≃ B

theorem ext_eq_refl (A : PSet.{u}) : A ≃ A :=
  (zfc_ext_pset A A).mp (λ x => ⟨id, id⟩)

theorem ext_eq_symm {A B : PSet.{u}} (h : A ≃ B) : B ≃ A :=
  (zfc_ext_pset B A).mp (λ x =>
    ((zfc_ext_pset A B).mpr h x).symm)

theorem ext_eq_trans {A B C : PSet.{u}}
  (h₁ : A ≃ B) (h₂ : B ≃ C) : A ≃ C :=
  (zfc_ext_pset A C).mp (λ x =>
    let hAB := (zfc_ext_pset A B).mpr h₁ x
    let hBC := (zfc_ext_pset B C).mpr h₂ x
    ⟨hBC.mp ∘ hAB.mp, hAB.mpr ∘ hBC.mpr⟩)

instance : Setoid PSet.{u} where
  r := Equiv
  iseqv := ⟨ext_eq_refl, ext_eq_symm, ext_eq_trans⟩

end PreZFC
```

The axiom `zfc_ext_pset` is bidirectional: $`A` and $`B` have the same members exactly when they are extensionally equivalent. From it we derive the three properties of an equivalence relation and equip `PSet` with a `Setoid` instance.

```lean
open PreZFC

namespace ZFC

def ZFSet.{u} := Quotient (inferInstance : Setoid PSet.{u})

noncomputable def ZFSet.mk (x : PSet.{u}) : ZFSet.{u} :=
  Quotient.mk (s := inferInstance) x

end ZFC

```

`ZFSet` is the quotient of `PSet` by $`\simeq`. Two PSet s that are extensionally equivalent are identified: $`A \simeq B` implies $`\texttt{ZFSet.mk } A = \texttt{ZFSet.mk } B` via `Quotient.sound`.

Now we lift membership to `ZFSet`. Since `PMem` respects $`\simeq` (if $`a_1 \simeq a_2` and $`b_1 \simeq b_2`, then $`a_1 \in b_1 \leftrightarrow a_2 \in b_2`), the lift by `Quotient.lift₂` is well-defined:

```lean
theorem pmem_congr {a₁ a₂ b₁ b₂ : PSet.{u}}
  (ha : a₁ ≃ a₂) (hb : b₁ ≃ b₂) : a₁ ∈ b₁ ↔ a₂ ∈ b₂ := by
  cases b₁ with | mk α₁ f₁ =>
  cases b₂ with | mk α₂ f₂ =>
  have hmem :=
    (zfc_ext_pset (PSet.mk α₁ f₁) (PSet.mk α₂ f₂)).mpr hb
  have h₁ := hmem a₁
  have h₂ := hmem a₂
  constructor
  · intro h; rcases h₁.mp h with ⟨a, ha'⟩
    exact ⟨a, ext_eq_trans ha' ha⟩
  · intro h; rcases h₂.mpr h with ⟨a, ha'⟩
    exact ⟨a, ext_eq_trans ha' (ext_eq_symm ha)⟩

namespace ZFC

noncomputable def ZFSet.Mem (x y : ZFSet.{u}) : Prop :=
  Quotient.lift₂ PMem (λ a₁ a₂ b₁ b₂ h₁ h₂ =>
    propext (pmem_congr h₁ h₂)) x y

infix:50 " ∈ " => ZFSet.Mem
notation:50 x:50 " ∉ " S:50 => ¬ (x ∈ S)

macro "∀ " x:ident " ∈ " S:term ", " P:term : term =>
  `(∀ $x:ident, $x ∈ $S → $P)

macro "∃ " x:ident " ∈ " S:term ", " P:term : term =>
  `(∃ $x:ident, $x ∈ $S ∧ $P)

theorem zmem_well_defined (p q : PSet) :
  Quot.mk Equiv p ∈ Quot.mk Equiv q ↔  PMem p q := by
  rw [ZFSet.Mem, Quotient.lift₂]

end ZFC
```

From here on, $`\in` denotes membership on `ZFSet`. Before we get to the axioms, we define one basic derived notion that will be used throughout:

```lean
namespace ZFC

/-- A set is nonempty if it has at least one element. -/
def nonempty (X : ZFSet.{u}) : Prop := ∃ wx, wx ∈ X

end ZFC
```

Extensionality for `ZFSet` is now a theorem — it follows from `zfc_ext_pset` by quotient induction:

```lean
namespace ZFC

theorem axiom_ext (A B : ZFSet.{u}) :
    (∀ x : ZFSet.{u}, x ∈ A ↔ x ∈ B) ↔ A = B := by
    constructor
    · intro h
      revert A B h
      apply Quot.ind
      intro p
      apply Quot.ind
      intro q
      intro h
      apply Quot.sound
      change Equiv p q
      apply (zfc_ext_pset p q).mp
      intro wp
      specialize h (Quot.mk Setoid.r wp)
      repeat rw [←zmem_well_defined]
      exact h
    · intro hEq x
      rw [hEq]

end ZFC
```

Before we proceed to the existence axioms, we pause to address a design constraint that shapes every construction in the chapters to come. The axioms we are about to state are all $`\exists` quantifications in `Prop`. One might expect to extract the witness and define a `ZFSet`-valued function:

```lean+error
def mk_pair (a b : ZFSet) : ZFSet := by
  -- error: cannot eliminate from Prop to Type
  have ⟨pair_witness, proof⟩ := axiom_pairing a b
  exact pair_witness
```

This fails, and the failure reveals _two independent obstacles_.

*First obstacle: Prop elimination.* Lean separates `Prop` from `Type` into distinct universe sorts, forbidding elimination from `Prop` into `Type`. In standard type theory (Martin-Löf, HoTT) there is no such bifurcation; $`\exists` and $`\Sigma` are the same thing. But Lean's kernel ramifies its universe hierarchy, diverting `Prop` into a computationally irrelevant sort. In exchange, Lean gains _proof irrelevance_: any two proofs of the same proposition are definitionally equal, and the compiler erases them at runtime. The cost is that a $`\exists` in `Prop` is a ghost — it tells you something exists, but you cannot get your hands on the thing itself.

*Second obstacle: quotient erasure.* Even if we bypassed `Prop` by writing the axiom as a $`\Sigma`-type in `Type`, there is a second problem. Recall from {ref "c1-s2-encoding"}[the Encoding chapter] that `ZFSet` is a _quotient_ of `PSet`. `Quotient` erases the distinction between extensionally equivalent `PSet`s — a `ZFSet` is opaque. We cannot pattern-match on it or inspect its internals. The _only_ information a `ZFSet` carries is what $`\in` tells us.

The *primary* way we produce a `ZFSet` is therefore to prove an existential proposition — exactly like the axioms themselves. $`\exists` composes perfectly within `Prop` via `have`, `obtain`, `rcases`, and friends. The witness stays inside the proof and is erased at runtime.

For *operators used repeatedly* (binary union, Cartesian product, global constants like $`\emptyset`), a secondary pattern is available: `Classical.choose` bridges the Prop/Type divide, yielding a noncomputable `ZFSet` term bundled with a proof lemma. The helper `zfc_set_of` packages this into a reusable two-liner:

```lean
namespace ZFC

noncomputable def zfc_set_of {φ : ZFSet → Prop}
  (h : ∃ S : ZFSet, ∀ x, x ∈ S ↔ φ x) :
    ZFSet := Classical.choose h

theorem zfc_set_of_spec {φ : ZFSet → Prop}
  (h : ∃ S : ZFSet, ∀ x, x ∈ S ↔ φ x) :
    ∀ x, x ∈ zfc_set_of h ↔ φ x :=
  Classical.choose_spec h

end ZFC
```

The rule of thumb: prove theorems as $`\exists` propositions; define `noncomputable def`s only for operators called many times. We will see both patterns throughout the book, and we now put the first to use.

# Existence of the Null Set

> There exists a set with no elements that is unique up to extensional equality.
> $$`\exists! \emptyset \, \forall x \, x \notin \emptyset`

```lean
namespace ZFC

axiom axiom_exists_null
  : ∃ N : ZFSet.{u}, ∀ x : ZFSet.{u}, x ∈ N ↔ False

noncomputable def null : ZFSet.{u} :=
  zfc_set_of axiom_exists_null
theorem null_spec : ∀ x : ZFSet.{u}, x ∈ null ↔ False :=
  zfc_set_of_spec axiom_exists_null
notation "∅" => null

theorem null_unique
  : ∀ (x : ZFSet), ¬ (∃ k, k ∈ x) ↔ x = null := by
  intro x
  constructor
  · intro h
    apply (axiom_ext x null).mp
    intro y
    have hnull := null_spec y
    constructor
    · intro h_y_memof_x
      exfalso
      exact h (Exists.intro y h_y_memof_x)
    · intro h_y_memof_null
      exfalso
      have : y ∈ null := h_y_memof_null
      rcases hnull.mp this with ⟨⟩
  · intro h_x_eq_null
    rw [h_x_eq_null]
    intro h_exists
    obtain ⟨k, hk⟩ := h_exists
    have hnull := null_spec k
    rcases hnull.mp hk with ⟨⟩

end ZFC
```

Strictly speaking, the existence of the empty set is not an independent axiom — it follows from separation and infinity. Given any set at all (and infinity guarantees there is at least one), we can separate the subset satisfying the vacuous condition $`\bot`, yielding a set with no elements. The uniqueness of this empty set then follows from extensionality: any two sets with no elements have the same elements (none), so they are equal. We nevertheless present it as an axiom here for clarity and because the logical dependency on infinity is a quirk of the standard presentation that does not affect the development.

With the empty set in hand, we have our first concrete set. But a universe containing only $`\emptyset` is a rather lonely place. The next few axioms let us build richer collections.

# Existence of the Pair

> Given any sets $`X` and $`Y`, there exists a set whose elements are exactly $`X` and $`Y`.
> $$`\forall X \forall Y \, \exists S\, \forall x\, (x \in S) \iff (x = X \lor x = Y)`

```lean
namespace ZFC

axiom axiom_pairing (X Y : ZFSet.{u}) :
    ∃ C : ZFSet.{u}, (∀ (x : ZFSet.{u}),
      x ∈ C ↔ (x = X ∨ x = Y))

end ZFC
```

Pairing lets us build a set with exactly two elements. But what if we want to gather the elements of those elements? Given a set of sets — say, a family $`\{\{a, b\}, \{c, d\}, \{e, f\}\}` — we often need to talk about the collection of all elements that belong to *any* member of the family — $`\{a, b, c, d, e, f\}`. For that we need the union axiom.

# Existence of the Union

> Given any set $`F`, there exists a set $`\bigcup F` whose elements are exactly the members of members of $`F`.
> $$`\forall F \, \exists \bigcup F \, \forall x \, (x \in \bigcup F) \iff (\exists S, x \in S \land S \in F)`

```lean
namespace ZFC

axiom axiom_union (F : ZFSet.{u}) :
    ∃ C : ZFSet.{u}, ∀ (x : ZFSet.{u}), x ∈ C
      ↔ (∃ (S : ZFSet.{u}), x ∈ S ∧ S ∈ F)

noncomputable def fam_union (F : ZFSet.{u}) :
    ZFSet.{u} := zfc_set_of (axiom_union F)

theorem fam_union_spec (F : ZFSet.{u}) :
    ∀ x, x ∈ fam_union F ↔
      ∃ (S : ZFSet.{u}), x ∈ S ∧ S ∈ F :=
  zfc_set_of_spec (axiom_union F)

prefix:70 "⋃" => fam_union

end ZFC
```

Pairing builds a set from given elements; union collapses a set of sets down to its members. The next axiom moves in the opposite direction, blowing a single set up into the collection of all its subsets.

# Existence of the Powerset

> Given any set $`S`, there is a set $`\mathcal{P}(S)` whose elements are exactly the subsets of $`S`.
> $$`\forall S, \exists P \, \forall X \, X \in P \iff X \subseteq S`

We first define the subset relation:

> A set $`A` is a *subset* of a set $`B` if and only if every element of $`A` is a member of $`B`.
> $$`A \subseteq B \iff \forall x, x \in A \implies x \in B`

```lean
namespace ZFC

def ZFSubseteq (A B : ZFSet.{u}) : Prop :=
  ∀ (x : ZFSet.{u}), ZFSet.Mem x A → ZFSet.Mem x B

infix:64 " ⊆ " => ZFSubseteq

axiom axiom_powerset (S : ZFSet.{u}) :
  ∃ P : ZFSet.{u}, ∀ (X : ZFSet.{u}), X ∈ P ↔ X ⊆ S

noncomputable def powerset (S : ZFSet.{u}) :
  ZFSet.{u} := zfc_set_of $ axiom_powerset S

theorem powerset_spec (S : ZFSet.{u}) :
  ∀ X, X ∈ powerset S ↔ X ⊆ S :=
    zfc_set_of_spec $ axiom_powerset S
end ZFC
```

The axioms so far — empty set, pairing, union, powerset — let us combine and expand sets. But they do not give us the ability to carve a *subcollection* out of an existing set by imposing a condition. That is the role of separation, the axiom that directly replaces naive comprehension while avoiding Russell's paradox.

# Axiom Schema of Separation

> For any predicate $`\phi` and a set $`U`, there exists a set $`U'` whose elements are exactly those members of $`U` that satisfy $`\phi`.
> $$`\forall U \, \exists U'\, \forall x\, x \in U' \iff x \in U \land \phi(x)`

This is called an *axiom scheme* because the language of ZFC is first-order — quantifiers range only over terms (sets), not over predicates. One must posit a separate axiom for each definable $`\phi`, much like a macro expansion in programming. In Lean, however, there is no such restriction: we can accept $`\phi` directly as a function, since our ambient type theory is far more expressive than the first-order language we are modeling.

```lean
namespace ZFC

axiom axiom_separation
  (U : ZFSet.{u}) (φ : ZFSet.{u} → Prop) :
    ∃ A : ZFSet.{u}, ∀ (x : ZFSet.{u}), x ∈ A ↔ x ∈ U ∧ φ x

noncomputable def set_from_pred
  (X : ZFSet.{u}) (φ : ZFSet → Prop)
    : ZFSet.{u} := zfc_set_of $ axiom_separation X φ

theorem set_from_pre_spec
  (X : ZFSet.{u}) (φ : ZFSet → Prop)
    : ∀ x, x ∈ set_from_pred X φ ↔ x ∈ X ∧ φ x :=
      zfc_set_of_spec $ axiom_separation X φ

end ZFC
```

All of the axioms so far describe ways to build finite collections from existing ones. But none of them guarantee the existence of an infinite set. Without an axiom of infinity, we cannot construct the natural numbers, the real line, or indeed any of the objects that make set theory a foundation for mathematics. The next axiom fills that gap.

# Axiom of Infinity

To introduce this axiom, we first need a definition of an inductive set.

> The *Successor* of a set is the union of itself with the singleton containing itself.
> $$`s(a) := a \cup \{a\}`
> A set $`S` is *inductive*, denoted with the predicate $`\text{Ind}`, if $`S` contains $`\emptyset`, and the successor of an element in $`S` is also a member of $`S`.
> $$`\text{Ind}(S) := \emptyset \in S \land \forall a\, (a \in S \implies s(a) \in S)`

The name "successor" came from that fact that later on will be using this function for encoding the cardinal numbers. Let's first formalize these two notions.

```lean
namespace ZFC

def is_succ_of (S A : ZFSet) : Prop :=
  ∀ x, x ∈ S ↔ x = A ∨ x ∈ A

theorem exists_succ_for_all (A : ZFSet)
  : ∃ S : ZFSet, is_succ_of S A := by sorry

def is_inductive (N : ZFSet) : Prop :=
  null ∈ N ∧
    ∀ a, a ∈ N → ∀ s, is_succ_of s a → s ∈ N

noncomputable def succ (X : ZFSet) : ZFSet
  := zfc_set_of $ exists_succ_for_all X

theorem succ_spec (X : ZFSet)
  : is_succ_of (succ X) X :=
    zfc_set_of_spec $ exists_succ_for_all X

end ZFC
```


And now the axiom of infinity itself states that there exists an inductive set.

```lean
namespace ZFC

axiom axiom_infinity
  : ∃ S : ZFSet, is_inductive S

-- Note that here we cannot use
-- our nice zfc_set_of macros
-- since axiom_infinity is not
-- a parametrized theorem.
noncomputable def inf : ZFSet :=
  Classical.choose axiom_infinity

theorem inf_spec
  : is_inductive inf :=
  Classical.choose_spec axiom_infinity

notation "∞" => inf

end ZFC
```

Notice that `exists_succ_for_all` is stated as a _theorem_, not an axiom. This is deliberate: the successor $`s(A) = A \cup \{A\}` is definable from pairing and union — we first form the singleton $`\{A\}` via `axiom_pairing A A`, then take $`\bigcup \{A, \{A\}\}` via `axiom_union`. No new axiom is required.

We now return to the remaining axioms. Separation lets us carve a subset out of a given set by a predicate. But what if we want to *transform* the elements of a set — applying a definable operation to each member and collecting the results? Separation alone cannot do this, because the outputs may not be subsets of the original domain. We need a stronger principle.

# Axiom of Replacement

The standard formulation of replacement can look cryptic at first glance. Another common variant — the axiom schema of collection — isn't directly usable until we've formalized functions, and is trickier to work with under our setup anyway. So let's break the axiom down piece by piece.

First, we need to pin down what we mean by a *functional relation*. In our setting, this is not a ZFC relation in the set-theoretic sense — it's a 2-ary predicate over sets that happens to be single-valued. That is, for each $`x`, there is at most one $`y` such that $`\varphi(x, y)` holds:

> A functional relation $`\varphi` is a 2-ary predicate satisfying:
> $$`\forall x\, \forall y\, \forall z ,\; \varphi(x, y) \land \varphi(x, z) \implies y = z`

This is the *single-valued* or *univalent* condition.

*Nomenclature.* Because $`\varphi` is single-valued, we can think of it as a function at the meta-level. But there's a potential source of confusion: within ZFC itself, a "function" is a specific kind of *set* — a subset of a Cartesian product $`X \times Y` consisting of ordered pairs. That's a concrete mathematical object that lives inside our set-theoretic universe. To avoid mixing up the logical formula $`\varphi` with an actual set-theoretic function, I'll use the word *"map"* (or *"definable class function"*) for the meta-theoretic construct. A "map" is a syntactic rule expressed by a formula. A "function" is a bona fide `ZFSet` that satisfies the usual ordered-pair definition. This keeps the levels straight without much mental overhead.

Now, given a functional relation $`\varphi` and a set $`X`, the replacement axiom guarantees that we can collect all the outputs of $`\varphi` on inputs from $`X` into a single set:

> If $`\varphi` is a functional relation, then for any set $`X`, there exists a set $`Y` such that:
> $$`y \in Y \iff \exists x \in X,\; \varphi(x, y)`

```lean
namespace ZFC

axiom axiom_replacement (X : ZFSet.{u})
  (φ : ZFSet.{u} → ZFSet.{u} → Prop)
  (h_func : ∀ x y z, φ x y → φ x z → y = z) :
    ∃ Y : ZFSet.{u}, ∀ y, y ∈ Y ↔ ∃ x ∈ X, φ x y

noncomputable def replacement_set
  (X : ZFSet) (φ : ZFSet → ZFSet → Prop)
    (h_func : ∀ x y z, φ x y → φ x z → y = z) :=
      zfc_set_of $ axiom_replacement X φ h_func

theorem replacement_set_spec
  (X : ZFSet) (φ : ZFSet → ZFSet → Prop)
    (h_func : ∀ x y z, φ x y → φ x z → y = z)
      : ∀ y, y ∈ replacement_set X φ h_func ↔ ∃ x ∈ X, φ x y
        := zfc_set_of_spec $ axiom_replacement X φ h_func

end ZFC
```

The axioms we have seen so far all assert the *existence* of sets — they tell us what sets there are. The next axiom is different: it tells us what the universe of sets *cannot* contain.

# Axiom of Foundation

> Every nonempty set is disjoint from one of its elements, known as the $`\in`-minimal element.
> $$`\forall x, x \ne \emptyset \implies \exists y \in X, y \cap X = \emptyset`

This axiom prevents a infinite descending chain of membership.

```lean
namespace ZFC

axiom axiom_foundation
  (X : ZFSet.{u}) (h_nonempty_X : nonempty X)
    : ∃ y ∈ X, ¬(∃ x, x ∈ X ∧ x ∈ y)

end ZFC
```

Foundation ensures the universe is built from the ground up. We turn now to the final, and most controversial, axiom — one that permits a kind of non-constructive selection that is ubiquitous in mathematical practice but famously independent of the other axioms.

# Axiom of Choice

> For every set `A` whose elements are non‑empty sets, there exists a set `B` that selects exactly one element from each member of `A`.
> $$`\forall A, (\forall x \in A, x \neq \emptyset) \implies \exists B, \forall x \in A, \exists y \in B \cap x, \forall z \in B \cap x, z = y`

This axiom is independent of ZF; the system ZF + Choice is denoted ZFC. It is needed to prove many classical results, such as the well‑ordering theorem and Zorn’s lemma.

```lean
namespace ZFC

axiom axiom_choice (A : ZFSet.{u}) :
  (∀ x ∈ A, x ≠ null) →
  ∃ B : ZFSet.{u}, ∀ x ∈ A,
    ∃ y, y ∈ B ∧ y ∈ x ∧ ∀ z, z ∈ B ∧ z ∈ x → z = y

end ZFC
```

This completes the list of axioms for ZFC. We have postulated: extensionality (as a theorem of the quotient), the empty set, pairing, union, powerset, separation, infinity, replacement, foundation, and choice. Together they form a remarkably economical foundation — a handful of principles from which virtually all of classical mathematics can be derived. In the chapters that follow, we will put these axioms to work, building up the familiar objects of set-theoretic mathematics: ordered pairs, relations, functions, ordinals, and cardinals.

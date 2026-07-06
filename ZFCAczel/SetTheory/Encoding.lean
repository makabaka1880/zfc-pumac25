/-
Copyright (c) 2025. All rights reserved.
-/
import VersoManual
import ZFCAczel.Meta.Lean
import ZFCAczel.Papers
import Init.Data.Nat.Basic
import Init.Data.Nat.Linear
open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Verso Code External
open ZFCAczel
set_option pp.rawOnError true
set_option linter.verso.markup.emph false

#doc (Manual) "Encoding Sets in Dependent Type Theory" =>
%%%
file := "Encoding"
tag := "c1-s2-encoding"
%%%

Now that we have examined the historical motivation for axiomatic set theory, we turn to a practical question: how should we actually encode ZF sets inside a dependent type theory like Lean's? This section explores two approaches — the naive predicate interpretation, which is simple but limited, and Aczel's tree encoding, which is faithful but more subtle. Understanding both will prepare us for the full axiomatic development to come.

# Predicate Interpretation of Sets

The most direct way to represent sets in a type-theoretic setting is to interpret them as predicates. In Lean, we can define:

```lean
namespace NaiveSetTheory
---
def NSet (α : Type u) : Type u := α → Prop
def NMem (x : α) (S : NSet α) := S x

infix:50 " ∈ " => NMem
notation:50 x:50 " ∉ " S:50 => ¬ (x ∈ S)
---
end NaiveSetTheory
```

Here, a "set" over a type $`\alpha` is simply a function from $`\alpha` to propositions. The membership relation $`\in` is defined by applying the predicate $`S` to the element $`x`: we write $`x \in S` to mean $`S(x)` holds. This mirrors the mathematical intuition that a set is determined by which elements belong to it.

_Example 1._ The set of even natural numbers can be encoded as a predicate:

```lean
open NaiveSetTheory
---
def even_numbers : NSet Nat := λ n => n % 2 = 0
```

Then $`2 \in \texttt{even\_numbers}` computes to the proposition $`2 % 2 = 0`, which is true, while $`3 \in \texttt{even\_numbers}` computes to $`3 % 2 = 0`, which is false. The membership relation $`\in` is the binary relation whose partial application to `even_numbers` gives the unary predicate $`\lambda n.\, n \% 2 = 0`.

```lean
open NaiveSetTheory

example : 2 ∈ even_numbers := by
  unfold even_numbers NMem
  simp_all

example : 3 ∉ even_numbers := by
  unfold even_numbers NMem
  simp_all
```

This interpretation works smoothly _within Lean_ thanks to the stratification of universes. The type-theoretic hierarchy prevents the formation of self-referential or ill-founded sets that caused trouble in naive set theory. For instance, the following construction is rejected by the type checker:

```lean+error
inductive NSetPredicative α where
| Nested (f : NSetPredicative α → Prop) : NSetPredicative α
| Base (s : NSet α) : NSetPredicative α

open NaiveSetTheory

-- If Lean accepted NSetPredicative,
-- we could define a membership-like
-- predicate for the Nested case:
def NPreMem (A B : NSetPredicative α) : Prop :=
  match B with
  | .Nested f => f A
  | .Base _ => False

def russell (α : Type u) : NSetPredicative α :=
  .Nested (λ S => ¬ NPreMem S S)

theorem russell_paradox (α : Type u)
  [Nonempty (NSetPredicative α)] : False := by
  let R := russell α
  have h : NPreMem R R ↔ ¬ NPreMem R R := by
    unfold NPreMem russell
    simp
  have hmem : NPreMem R R := by
    apply Classical.byContradiction
    intro hnmem
    exact hnmem (h.mpr hnmem)
  exact hmem (h.mp hmem)
```

While this stratification makes the predicate view consistent within the proof assistant, it is not sufficiently powerful to faithfully model the full cumulative hierarchy of ZF set theory. In particular, one cannot easily construct sets whose elements have different "orders" or ranks. A classic example is the set

$$`\{0, \{0\}\}`

where the second element is itself a set containing the first. Representing such mixed-rank structures cleanly using only predicates over a fixed universe quickly becomes awkward or impossible without additional machinery.

_Example 2._ Suppose we try to encode $`\{0, \{0\}\}` in the predicate style. The number $`0` is of type $`\mathbb{N}`, so we need $`0 \in S` to be true. But $`\{0\}` is itself a set — a predicate over $`\mathbb{N}` — so it has type $`\mathbb{N} \to \mathsf{Prop}`, while $`0` has type $`\mathbb{N}`. A predicate $`S` would need to accept elements of two different types simultaneously: the natural number $`0` and the predicate $`\{0\}`. Lean's type system prevents this; there is no universe in which both are inhabitants of a single carrier type. This is fundamentally the same limitation that prevents us from forming $`\{0, \{0\}\}` in the stratified predicate encoding.

# Aczel's Tree Encoding (PSet)

To overcome the limitations of the predicate interpretation, we adopt a richer representation: we view a set as a well-founded tree. This approach, due to Peter Aczel, provides a much closer match to the way sets actually behave in ZF. We introduce a dedicated inductive type, called `PSet` (for "pure set" or "pre-set"), to distinguish it from the predicate-based `Set` above:

```lean
inductive PSet : Type (u + 1) where
  | mk (α : Type u) (f : α → PSet) : PSet
```

The constructor takes two arguments:
* `α` is an indexing type describing the elements of the set.
* `f : α → PSet` maps each index to the corresponding element.

Before we can say what it means for one set to belong to another, we must first define what it means for two sets to be equal. In ZF, sets are equal precisely when they have the same elements — this is the principle of _extensionality_. We postulate extensional equality as an equivalence relation on `PSet`:

```lean
axiom Equiv : PSet → PSet → Prop

infix:50 " ≃ " => Equiv
```

We declare $`\simeq` as a `Setoid` instance, which equips `PSet` with a built-in notion of equivalence that interacts with Lean's type class machinery for rewriting and substitution. The theorem `Equiv.refl` is a convenience — it already follows from the instance, but naming it explicitly makes equational proofs more readable.

Now we can define membership directly on the tree structure. A set $`x` belongs to the set $`\texttt{mk } \alpha f`$ if there exists some index $`a : \alpha` such that $`f\;a` is extensionally equivalent to $`x`:

```lean
def PMem : PSet → PSet → Prop
  | x, PSet.mk α f => ∃ a : α, f a ≃ x

infix:50 " ∈ " => PMem
notation:50 x:50 " ∉ " S:50 => ¬ (x ∈ S)
```

The membership relation $`\in` is a binary relation; partially applied to a fixed set $`\texttt{mk } \alpha f`, it yields that set's membership predicate. Every axiom in the remainder of this book will be stated in terms of $`\in` and $`\simeq`.

Conceptually, the mathematical set

$$`\{x_0, x_1, \ldots, x_n\}`

is represented by choosing an indexing type with one inhabitant for each element and a function sending each index to its corresponding `PSet`.

The empty set is the simplest example. Since it contains no elements, we choose the empty type as its indexing type.

```lean
def empty : PSet :=
  .mk Empty (λ e ↦ nomatch e)
```

A singleton set follows the same pattern, using the unit type as the index.

```lean
def singleton (x : PSet) : PSet :=
  .mk Unit (Function.const Unit x)
```

With just these two constructors we can already build a surprising variety of sets. For instance, `singleton (singleton empty)` represents the set $`\{\{\emptyset\}\}`. Let us construct it step by step:

_Example 3._ We build $`\{\emptyset, \{\emptyset\}\}` in the `PSet` encoding:

```lean
-- empty : PSet represents ∅
-- singleton empty : PSet represents {∅}
-- Now we need an indexing type with two elements:
def pair_example : PSet :=
  .mk Bool (λ b => match b with
    | false => empty
    | true  => singleton empty)
```

The indexing type is `Bool`, which has two inhabitants. The element at index `false` is `empty` ($`\emptyset`) and the element at index `true` is `singleton empty` ($`\{\emptyset\}`). The resulting `PSet` faithfully represents the mathematical set $`\{\emptyset, \{\emptyset\}\}`. Notice that we did not need to force both elements into the same type universe — each branch of the match produces a `PSet`, and `PSet` is the uniform carrier for all elements regardless of "rank."

This representation is remarkably faithful to the cumulative nature of set theory: every set is built from previously existing sets, and there is simply no way to construct a pathological self-referential object. The inductive definition guarantees well-foundedness automatically.

# Why Equality is Hard — and Why It Matters

There is a catch. Two sets are _extensionally equal_ if they have exactly the same members. In ZF, extensionality is the only thing that matters: a set _is_ its members. The `PSet` encoding respects this in spirit, but not in letter.

_Example 4._ Consider two different representations of the same singleton $`\{\emptyset\}`:

```lean
-- Version 1: using Unit as the index
def sing1 : PSet := .mk Unit (λ _ => empty)

-- Version 2: using a custom single-inhabitant type
inductive OneElem : Type where | it : OneElem
def sing2 : PSet := .mk OneElem (λ _ => empty)
```

These two values are structurally different — one uses `Unit`, the other uses a bespoke `OneElem` type. Yet they represent the same set: each contains exactly one element, and in both cases that element is `empty`. To prove them equal, we would need to construct a *bisimulation* — a mutual simulation relating the two tree structures — which is nontrivial even for this toy example and rapidly becomes unwieldy for larger sets. This is a well-known difficulty with W-types in dependent type theory: equality on trees is equational reasoning at its most tedious.

So we face a choice. We _could_ define extensional equality recursively and work directly with `PSet` values, proving bisimulations by hand whenever two representations ought to be identified. Or we could take the standard mathematical shortcut: quotient `PSet` by the extensional equivalence relation, so that `sing1` and `sing2` become definitionally the same object — a `ZFSet` — and reason about sets entirely through the membership relation, never through their underlying tree structure.

We choose the second path. In the next chapter, we will define $`\texttt{ZFSet}` as the quotient of $`\texttt{PSet}` by $`\simeq`, lift membership to the quotient, and then state the axioms of ZF directly in terms of the lifted $`\in`. Once the quotient is in place, the tree encoding becomes an implementation detail — we will never look inside a `ZFSet` again. Every set will be specified by a predicate describing which elements belong to it, and every proof will appeal to the axioms rather than to the inductive structure. This is exactly how mathematicians work with sets: they ask what is inside, not how the set was built.

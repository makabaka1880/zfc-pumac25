/-
Copyright (c) 2025. All rights reserved.
-/

import VersoManual
import ZFCAczel.Papers
import ZFCAczel.SetTheory.ZFAxioms
import ZFCAczel.SetTheory.SetProblems

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true
set_option linter.verso.markup.emph false

#doc (Manual) "Conventions" =>
%%%
file := "Conventions"
tag := "appendix-conventions"
number := false
%%%

This appendix documents the naming conventions and organizational patterns used throughout this project. It serves as a reference for contributors and, honestly, for the author to remember what he decided six months ago.

# Naming Conventions

## `Snake_case` is the default

All definitions, theorems, and lemmas use `snake_case`, following mathlib conventions. Every name should read like a sentence fragment describing the proposition it proves — given the name alone, you should be able to reconstruct the signature.

## Predicate names

Predicates that check a property of a set are named `is_`:

:::table

*
  * Predicate
  * Meaning
  * Style
*
  * `is_singleton_of Z x`
  * `Z` is the singleton $`\{x\}`
  * `is_*_of_*` — first argument is canonical
*
  * `is_upair_of Z x y`
  * `Z` is the unordered pair $`\{x, y\}`
  * `is_*_of_*` — first argument is canonical
*
  * `pure_relation R`
  * `R` consists entirely of ordered pairs
  * Free property — drops `_of_`
*
  * `is_function F`
  * `F` is a set of ordered pairs with single-valuedness
  * Free property — drops `_of_`
:::

## Spec lemmas

Every `noncomputable def` built via `zfc_set_of` receives a companion `*_spec` lemma:

```
noncomputable def bin_union (x y : ZFSet) : ZFSet :=
  zfc_set_of (exists_binary_union_proof x y)

@[simp]
theorem bin_union_spec (x y : ZFSet) :
    ∀ z, z ∈ bin_union x y ↔ z ∈ x ∨ z ∈ y :=
  zfc_set_of_spec (exists_binary_union_proof x y)
```

The spec lemma is always an $`\leftrightarrow` rewriting membership into the defining predicate. It carries `@[simp]` because it reduces a complex membership expression to a simple condition.

## Iff over directional

Where both directions are true, prefer a single $`\leftrightarrow` lemma over separate $`\rightarrow` and $`\leftarrow` lemmas:

```
-- Good: one lemma with both directions
theorem singleton_inj : (singleton a = singleton b) ↔ a = b := ...

-- Bad: two separate lemmas
theorem singleton_inj_mp : singleton a = singleton b → a = b := ...
theorem singleton_inj_mpr : a = b → singleton a = singleton b := ...
```

This applies even when one direction is trivially true — the uniform interface is more valuable than the saved line of proof.

## Corollaries should be one-liners

When a lemma is a strict special case of a more general lemma, make it a transparent corollary rather than duplicating the proof. The reader can see immediately that the special case is just the general lemma with one argument fixed.

# Operator Conventions

## Binding power

All infix and notation bindings follow mathlib precedence conventions:

:::table

*
  * Operator
  * Priority
  * Justification
*
  * `∈`
  * 50
  * Same level as `=`
*
  * `∉`
  * 50
  * Same as `∈`
*
  * `⊆`
  * 64
  * mathlib `HasSubset.Subset`
*
  * `⟪,⟫`
  * 60
  * Ordered pair, between `⊆` and `∩`
*
  * `∪`
  * 65
  * mathlib union
*
  * `∩`
  * 70
  * mathlib inter
*
  * `×`
  * 70
  * mathlib product
:::

## Infix notations in the ZFC namespace

All set-theoretic infix operators (`∪`, `∩`, `×`, `⊆`) live in the `ZFC` namespace. The `PUMAC25` namespace contains only existence proofs — problem solutions. Once a construction is proved to exist, its convenience wrapper and notation are promoted to `ZFC` for general use.

# Project Organization

## File structure

:::table

*
  * File
  * Purpose
*
  * `ZFCAczel.lean`
  * Root document; imports all chapters
*
  * `ZFCAczel/SetTheory.lean`
  * Chapter-level aggregator for Set Theory
*
  * `ZFCAczel/SetTheory/Foundations.lean`
  * Naive set theory, historical motivation
*
  * `ZFCAczel/SetTheory/Encoding.lean`
  * Predicate interpretation and PSet encoding
*
  * `ZFCAczel/SetTheory/ZFAxioms.lean`
  * All ZFC axioms and convenience wrappers
*
  * `ZFCAczel/SetTheory/SetProblems.lean`
  * Worked exercises and derived constructions
*
  * `ZFCAczel/Meta/Lean.lean`
  * Custom Verso block extensions
*
  * `ZFCAczel/Papers.lean`
  * Bibliography entries
:::

## Namespaces

:::table

*
  * Namespace
  * Contents
*
  * `ZFC`
  * All constructions built from the ZFC axioms: `singleton`, `upair`, `ordered_pair`, `bin_union`, `bin_inter`, `cartesian_product`, plus their `_spec` lemmas, and derived predicates like `is_function`
*
  * `PUMAC25`
  * Solutions to numbered problems: existence theorems and their proofs
*
  * `PreZFC`
  * PSet-level constructions used before the ZFSet quotient is defined
*
  * `NaiveSetTheory`
  * The predicate-based encoding in Encoding.lean; strictly pedagogical
:::

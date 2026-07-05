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

#doc (Manual) "Naive Set Theory and the Path to ZF" =>
%%%
file := "Foundations"
tag := "c1-s1-history"
%%%

Mathematics, at its core, is the study of structure and relationship. But what kind of thing is the collection of all even numbers? The set of all groups up to isomorphism? The class of all topological spaces? To reason rigorously about such collections, we need a theory. This section explores the first attempt at such a theory — and why it failed.

# Naive Set Theory

Set theory serves as the foundational framework for much of modern mathematics. Even in elementary algebra we encounter the notion of a "set" as a collection of values satisfying a given relation — for instance, the solution set of an equation. This intuitive idea of a collection of objects is what we call a *set* in naive set theory.

In naive set theory, a set is characterized by a predicate over a universe of objects. The fundamental relation of set theory is the binary membership relation, denoted by the symbol $`\in`. For a fixed set $`S`, the expression $`x \in S` is a unary predicate — the *membership predicate of $`S`* — which tells us whether a given $`x` belongs to $`S`. In this way, every set determines a unary predicate, and the central idea of naive set theory is that the converse also holds: every definable unary predicate determines a set.

*Example 1.* Let $`\varphi(x)` be the predicate "$`x` is an even natural number." By unrestricted comprehension, there exists a set

$$`E = \{ x \mid \varphi(x) \} = \{ 0, 2, 4, 6, \dots \}`

whose membership predicate $`x \in E` holds exactly when $`x` is an even natural number. For instance, $`2 \in E` is true, while $`3 \in E` is false. The binary membership relation $`\in`, partially applied to the fixed set $`E`, yields precisely the unary predicate $`\varphi`.

Because naive set theory imposes no restrictions on membership, we are free to define sets that contain other sets — and even sets that contain themselves. The central principle enabling this freedom is the *axiom schema of unrestricted comprehension* (also called the axiom schema of set introduction):

> For any predicate `φ`, there exists a set `S` such that for all `x`, `x ∈ S` if and only if `φ(x)` holds.
> $$`\forall \phi \, \exists S \, \forall x\, x \in S \iff \phi(x)`

This principle asserts that _every_ definable property determines a set. It licenses constructions that feel natural to everyday mathematical practice:

*Example 2.* Let $`\varphi(x)` be "$`x` is a set with exactly two elements." Unrestricted comprehension gives us

$$`T = \{ x \mid x \text{ is a set with exactly two elements} \}`

so that $`\{a, b\} \in T` for any distinct $`a, b`, while $`\{c\} \notin T`. The schema appears harmless — we are merely collecting all objects that share a property into a set.

But in genuine naive set theory the quantifier in the comprehension schema ranges without restriction over all objects — including sets, sets of sets, and the very set being defined. This unbounded freedom leads to Russell's famous paradox. Consider the property "$`a` is not an element of itself" and the set it defines:

$$`S = \{ a : a \notin a \}`

Let us examine the proposition $`S \in S`. Suppose $`S \in S`. Then, by the defining property of $`S`, it follows that $`S \notin S`. Conversely, suppose $`S \notin S`. Then $`S` satisfies the condition $`a \notin a`, so $`S \in S`.

In either case we reach a contradiction. This is *Russell's paradox*, and it demonstrates that unrestricted comprehension cannot serve as a consistent foundation for mathematics. The predicate "$`a \notin a`" is perfectly grammatical — yet the set it purports to define cannot exist.

*Example 3.* To see why some comprehensions are safe while others are not, consider the property "$`a \in b`" for some fixed set $`b`. The set $`\{ a \mid a \in b \}` is simply $`b` itself — no contradiction arises. The difference is that this predicate ranges only over elements of a set we have already built, rather than over the entire universe of all possible objects. This is the key insight behind the *axiom schema of separation*: new sets may be carved out of existing ones, but they cannot be conjured from thin air.

# The Necessity of Zermelo–Fraenkel Set Theory

Russell's paradox showed that the naive approach, while intuitively appealing, is fatally flawed. The problem is not that we lack the right definition — it is that the very idea of letting every predicate determine a set leads to contradiction. The remedy is to give up the axiom of unrestricted comprehension and instead begin with a small stock of primitive sets, constructing new ones only through carefully controlled operations.

This insight led to the modern axiomatic approaches to set theory, most notably *Zermelo–Fraenkel set theory (ZF)*. ZF treats sets as primitive mathematical objects whose behavior is governed by a collection of axioms describing how sets may be constructed and how they interact.

The most fundamental relation remains the membership relation $`a \in b`, but unlike naive set theory there is no universal comprehension principle. Instead, every new set must arise from previously existing sets through one of the axioms of ZF — pairing, union, power set, separation, replacement, and so forth. We will examine each of these axioms in detail in the next chapter.

This modest restriction is enough to avoid Russell's paradox while remaining expressive enough to formalize essentially all of ordinary mathematics. ZF provides a consistent foundation upon which the rest of mathematics can be built with confidence.

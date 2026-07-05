-- Created by Sean L. on Jul. 5.
-- Last Updated by Sean L. on Jul. 5.
--
-- zfc-aczel-pumac25
-- ZFCAczel/SetTheory.lean
--
-- Makabaka1880, 2026. All rights reserved.

import VersoManual
import ZFCAczel.Meta.Lean
import ZFCAczel.Papers
import Init.Data.Nat.Basic
import Init.Data.Nat.Linear

import ZFCAczel.SetTheory.Foundations
import ZFCAczel.SetTheory.Encoding
import ZFCAczel.SetTheory.ZFAxioms

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Verso Code External

open ZFCAczel

#doc (Manual) "Set Theory" =>
%%%
tag := "c1:set-theory"
%%%

Before we can formalize the axioms of Zermelo–Fraenkel set theory within Lean, we must first understand what set theory is — and why the naive formulation that students first encounter in elementary mathematics turns out to be inconsistent. In this chapter, we trace the historical development of set theory from its intuitive origins to its modern axiomatic form, and we introduce the encoding of sets that will serve as the foundation for the rest of the book.

{include 1 ZFCAczel.SetTheory.Foundations}
{include 1 ZFCAczel.SetTheory.Encoding}
{include 1 ZFCAczel.SetTheory.ZFAxioms}

-- Created by Sean L. on Jul. 5.
-- Last Updated by Sean L. on Jul. 5.
--
-- zfc-aczel-pumac25
-- ZFCAczel.lean
--
-- Makabaka1880, 2026. All rights reserved.

import VersoManual
import ZFCAczel.Meta.Lean
import ZFCAczel.Papers

import ZFCAczel.SetTheory

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open ZFCAczel

set_option pp.rawOnError true


#doc (Manual) "Zermelo-Fraenkel for Type Theorists" =>
%%%
tag := "home"
%%%

Mathematicians have come to realize the importance of formalization within a strict system of rigor. Currently, dependent type theory has proven to be the most competitive and ergonomic framework for this work. In this book, we will develop a formalization of ZFC from scratch in Lean 4 (a proof assistant based on the Calculus of Inductive Constructions) using an encoding proposed by Peter Aczel. Specifically, we will work through the PUMAC 2025 Power Round "The Continuum Hypothesis" problem set, providing a rigorous formal proof for the entire set.

{include 1 ZFCAczel.SetTheory}

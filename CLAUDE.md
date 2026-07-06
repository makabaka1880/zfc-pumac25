# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Build & Run

```bash
lake build          # compile the Lean library and executable
lake exe zfca       # build + run the Verso textbook generator (HTML output lands in _out/)
```

The project uses Lean 4 (v4.31.0) with Lake as the build system. The primary dependency is `verso` (v4.31.0), a documentation generator that produces multi-page HTML from Lean source files.

If the editor shows "Imports are out of date," run `lake build` — the LSP server's cache can lag behind filesystem changes, but `lake build` is always the source of truth.

Clean build: `lake clean && lake build`

## Architecture

This is a **Verso textbook** — a book written entirely in Lean source files that is compiled into a multi-page HTML website. There is no LaTeX or external markup; all content lives in `.lean` files under `ZFCAczel/`.

### Key files

| File | Role |
|------|------|
| `ZFCAczelMain.lean` | Build entry point. Defines `RenderConfig` (output mode, CSS, depth) and calls `manualMain`. Also contains the `buildExercises` extra step that extracts `savedLean` blocks into `_out/example-code/`. |
| `ZFCAczel.lean` | Root document (the homepage). Imports all chapters and uses `{include depth ModuleName}` to stitch them into the book. Metadata lives in the `%%% ... %%%` block after `#doc`. |
| `ZFCAczel/SetTheory.lean` | Chapter-level aggregator. Imports its subchapter modules and includes them. |
| `ZFCAczel/SetTheory/Foundations.lean` | Subchapter 1: naive set theory, Russell's paradox, historical motivation for ZF. |
| `ZFCAczel/SetTheory/Encoding.lean` | Subchapter 2: predicate interpretation of sets, Aczel's tree encoding (`PSet`, `PMem`, `Equiv`), quotient into `ZFSet`. |
| `ZFCAczel/SetTheory/ZFAxioms.lean` | Subchapter 3: all ZFC axioms — extensionality, empty set, pairing, union, powerset, separation, infinity, replacement, foundation, choice. Defines `is_succ_of`, `is_inductive`. Contains the "Side Note" on Prop elimination and quotient opacity. |
| `ZFCAczel/Meta/Lean.lean` | Custom Verso block extensions: `savedLean`, `savedImport`, `savedComment`. These are like `lean` blocks but also save code to files. |
| `ZFCAczel/Papers.lean` | Bibliography entries (the `Thesis` type from VersoManual). |
| `static/custom.css` | Custom CSS, read at build time via `include_str` and injected into every HTML page via `extraCssFiles`. |

### Document structure pattern

Each chapter/subchapter file follows this template:

```lean
import VersoManual
import ZFCAczel.Meta.Lean
import ZFCAczel.Papers

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open ZFCAczel
set_option pp.rawOnError true

#doc (Manual) "Chapter Title" =>
%%%
tag := "unique-tag"
%%%

Content goes here — markdown headings (# Title, ## Subtitle), inline roles ({math}`...`, {lean}`, {margin}[...], {index}[...]), and fenced code blocks (```lean ... ```).
```

The root document (`ZFCAczel.lean`) imports each chapter and includes it:

```lean
import ZFCAczel.SetTheory

#doc (Manual) "Book Title" =>
%%%
tag := "home"
%%%

{include 1 ZFCAczel.SetTheory}
```

The `1` in `{include 1 ...}` means "include as a top-level section." Use `2` for subsections, etc.

### How chapters and subchapters work

A "chapter" file (e.g. `SetTheory.lean`) is a container that imports and includes its subchapters. A "subchapter" (e.g. `SetTheory/Foundations.lean`) contains the actual prose. There is nothing structurally special about either — they are both `#doc` declarations. The nesting is purely editorial: the container file's `{include ...}` statements assemble subchapters under its own heading.

### Sharing Lean definitions across chapters

Code inside ```` ```lean ```` blocks is scoped to that chapter's module and invisible to other chapters. To share definitions across multiple chapters, create a plain `.lean` file (a regular Lean module, no `#doc`) and import it from each chapter that needs it.

### Verso markup

Verso uses its own inline markup in source `.lean` files. The prefix before the backtick tells Verso what kind of literal it is:

| Syntax | Renders as |
|--------|-----------|
| `*text*` | Emphasis (em). Nestable: `*like **this***` |
| `_text_` | Italic (i). Nestable. |
| `` `text` `` | Inline code |
| `{lit}`text`` | Inline literal (no interpretation) |
| `$`text`` | Inline LaTeX math |
| `$$`text`` | Display LaTeX math |

Note: Verso's built-in linter reverses these (`*` as bold, `_` as emphasis) and will warn. Suppress with `set_option linter.verso.markup.emph false` at the top of each chapter file.

### Verso inline roles

**Inline roles:** `{lean term}` (type-checked Lean), `{name Foo.bar}` (doc link), `{margin}[note]`, `{index}[term]`, `{index (subterm := "sub")}[term]`, `{citet ref}[]` / `{citep ref}[]` / `{citehere ref}[]` (citations), `{ref "tag"}[text]` (cross-reference), `{deftech term}` / `{tech term}` (glossary).

**Code blocks:** ```` ```lean ```` (elaborated Lean code), ```` ```lean +error ```` (expected error), ```` ```lean (name := foo) ```` (named block for `leanOutput`), ```` ```leanOutput foo ```` (checked output assertion). The custom blocks `savedLean`, `savedImport`, `savedComment` additionally save code to `_out/example-code/`.

**Fenced environments** (Pandoc-style, available from VersoManual with no registration):

````
:::{.theorem name="My Theorem"}
...
:::

:::{.definition name="My Definition"}
...
:::

:::{.axiom name="My Axiom"}
...
:::

:::{.example}
...
:::

:::{.corollary name="My Corollary"}
...
:::
````

**Metadata block** after a heading:
```
%%%
tag := "unique-tag"
number := false    -- suppress numbering
%%%
```

## CSS customization

Custom CSS is served from `static/custom.css`. It is registered in `ZFCAczelMain.lean` via `extraCssFiles` and read at compile time with `include_str "static" / "custom.css"`. Any CSS added there takes effect on the next `lake build`.

## Bibliography

Bibliography entries are defined as Lean constants in `ZFCAczel/Papers.lean`. Verso v4.31.0 supports these types from `VersoManual`: `Thesis`, `InProceedings`, `ArXiv`, `Article`. Use `{citet key}[]` for textual citations and `{citep key}[]` for parenthetical citations.

## Key design conventions

### The `ZFC` namespace

All definitions, axioms, theorems, and notation for the ZFC formalization live inside `namespace ZFC`. Each code block in the prose chapters opens `namespace ZFC` (or `PreZFC` for PSet-level work), defines what it needs, then closes it. This keeps the ZFC material separate from Verso's `Manual` namespace and from the naive set theory examples in `Encoding.lean`.

### ZFSet is opaque — all constructions go through the axioms, via `∃` propositions

`ZFSet` is defined as `Quotient (Setoid PSet)`, which makes it **opaque**: we cannot pattern-match on it, inspect its internal tree structure, or count its elements. Constructing a `ZFSet` directly via the `PSet.mk` constructor is nearly impossible for non-trivial operations, because it requires manipulating the indexing universe types and projection maps.

The **primary** way to produce a `ZFSet` is therefore to **prove an existential proposition** using the axioms (pairing, union, powerset, separation, etc.):

```lean
theorem exists_intersection (A B : ZFSet) : ∃ C, ∀ x, x ∈ C ↔ x ∈ A ∧ x ∈ B := ...
```

An `∃` sentence stays in `Prop`, composes directly with `have`, `obtain`, `rcases` in proofs, and avoids the semantic awkwardness of a term-level function whose sole purpose is propositional. This is the default style for proving theorems throughout the book.

### Convenience operators via `Classical.choose`

For **operators that are used repeatedly** as building blocks (binary union, Cartesian product, etc.), a secondary pattern is available: `noncomputable def` + `Classical.choose` to extract a `ZFSet` term in `Type`:

```lean
noncomputable def binary_union (A B : ZFSet) : ZFSet :=
  Classical.choose (exists_union A B)
```

This yields a noncomputable `ZFSet` bundled with a separate proof lemma (`Classical.choose_spec`) that certifies its properties. The same pattern is used for global constants (`∅`, `∞`). But these are convenience wrappers — the **proof** of any theorem about them still ultimately rests on the existential axioms, not on the `def` itself. The rule of thumb: **prove theorems as `∃` propositions; define `noncomputable def`s only for operators that will be called many times**.

### Bounded quantifier macros

The `ZFC` namespace defines convenience macros for bounded quantification:

```lean
macro "∀ " x:ident " ∈ " S:term ", " P:term : term => `(∀ $x:ident, $x ∈ $S → $P)
macro "∃ " x:ident " ∈ " S:term ", " P:term : term => `(∃ $x:ident, $x ∈ $S ∧ $P)
```

These are used throughout the axiom statements (e.g., `∀ x ∈ A, ...`, `∃ y ∈ B, ...`).

### Linter suppression

Verso's built-in linter warns about `*`/`_` usage (it reverses the markup convention). Every chapter file should include:

```lean
set_option linter.verso.markup.emph false
```

## Lake project naming

Lake project names cannot contain hyphens (they must be valid Lean `Name`s). This project uses `ZFCAczel` as the Lake project name and `zfca` as the executable name.

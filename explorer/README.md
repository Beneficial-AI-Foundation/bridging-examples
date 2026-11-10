# Bridging examples explorer

Open `site/index.html` locally. The top page is an overview: a diagram of how the five panels
connect, and one tile per example. Choosing an example shows five independently collapsible,
resizable panels: Rust, Aeneas, Spec, Crypto, and Bridge. All sources are embedded; no server
is needed. `site/etm/index.html` remains an entry point to the same artifact with Encrypt then Mac
selected. The title and the first entry of the example picker return to the overview.

Smoke contains only byte identity. Probabilistic Smoke only fills a buffer from an external
generator, so it shows the randomness assumption and its model on their own. Byte Mask draws one
byte the same way and combines it with the value by XOR. Modular Masking is a separate example with
range sampling, additive masking modulo `q`, and its Crypto interpretation and Bridge contracts.

Spec contains functional specifications of the extracted code, `f_spec`: an Aeneas triple
(successful return with the stated value) for a function without RNG calls, or an equation
exposing the one RNG call and the pure continuation after it. Deterministic contracts for
external hashes, ciphers, and MACs are Spec assumptions. Crypto contains stateless `ProbComp`
algorithms built from VCVio primitives. An external call has a Crypto counterpart of the same
name, such as `Crypto.ByteRng.next_u8`, and the algorithms call it. Bridge states one assumption
per RNG atom, `X_assumption`, a proposition relating the extracted call to its Crypto
counterpart, with the implementation and the distributions of its state as parameters
(`entropy n` is the distribution of states with `n` draws left), and one theorem per atom,
`f_bridge`: run the extracted function on a state with
`n` draws more than it makes and compare, in distribution, with the Crypto algorithm wrapped in
`Result.ok` and a state with `n` draws left. Deterministic bridges are `bridge_of_spec` applied
to the spec. Assumptions are hypotheses of the theorems; the handwritten files declare no axioms.
`Model.lean`, a supporting Bridge file, proves each assumption about a translated trait for a
source that reads from a random tape.
Smoke has no external calls. One-Time Pad assumes only `fill_bytes`; its Spec proves the XOR
loop with Aeneas's `loop.spec_decr_nat`, and `encrypt`, the loop, and its body share one
Bridge theorem.

Assumptions are labelled. Theorem statements have no routine “Proved” badge; their opaque-symbol
dependencies remain in metadata, declaration tooltips, and Sources. A theorem whose hypotheses
include an assumption is a checked derivation from that assumption, not a verification of the
external library. The concrete Lazy Oracle tape fixture remains separately proved.

Selecting an external atom shows its assumption in Spec or Bridge; selecting a function shows
its spec and bridge theorems together with the assumptions they take as hypotheses. Original line numbers and
complete source copying/downloads are preserved.

An example opens on full files with nothing selected. Choosing an atom from the picker, or
clicking a highlighted line number, highlights its related declarations and scrolls each panel
to them; the focus icon
restricts each panel to the selected material, including linked assumptions in Bridge.
Theorem statements remain visible in Bridge; proof bodies start folded and can be expanded
individually. Proof boundaries come from Lean's syntax parser. Copying and downloading retain
the complete source, including folded proofs.
Source-file and declaration
selectors remain available. Divider dragging resizes adjacent panels; double-click resets widths.

## Starting with Rust

To add an example, create a folder `BridgingExamples/<Name>/` with a Cargo crate in `rust/`.
The extraction command is:

```bash
bash scripts/extract.sh <Name>
```

Extraction uses pinned Charon/Aeneas versions. It writes three files into the example's folder:
`Aeneas.lean`, the generated Lean; `translation.json`, Aeneas's inventory of what it
translated; and `provenance.json`, the hashes of the Rust sources and of the generated files.
The handwritten stages are `Spec.lean`, `Crypto.lean` and `Bridge.lean` in the same folder;
absent files are allowed, and other Lean files there are shown as supporting Bridge files.

A crate without extraction has unknown coverage, not zero or complete. Once extracted, its
atoms appear automatically, with missing Crypto and Bridge work marked pending. The check
command does not run extraction itself or create placeholder Lean files. Loops extract as a
`*_loop` atom plus a `*_loop.body` atom. They share the Crypto definition and the Bridge theorem
of the function that contains them, and each keeps its own spec. A trait implementation is
described by its methods. Neither needs an annotation.

## Discovery and evidence

`scripts/examples.mjs` finds the example folders, obtains package metadata from Cargo, and
orders the examples from simple to complex, for the overview and the example picker; an
example missing from that order comes last.
Aeneas supplies the emitted atom inventory and Rust locations. Trait methods are atoms too:
Aeneas lists only the trait, so they are taken from the fields of the translated trait
structure. A method of an external trait is an atom only when something is linked to it.
`Common/Metadata.lean` exports compiled Lean names, types, declaration ranges,
associations, and axiom dependencies. No catalog or source-range list is edited.

Optional `[package.metadata.explorer]` fields in `Cargo.toml` set the display `name` and
`item-aliases` for renamed atoms. Existing links to `encrypt_randomized` select `encrypt`.

For `example.atom`, discovery looks for `example.Spec.atom_spec`, `example.Crypto.atom`,
`example.Bridge.atom_bridge`, and `example.Spec.atom_assumption` or
`example.Bridge.atom_assumption`. Unique shortened trait-method names are also supported;
ambiguous matches require explicit `spec_for`, `crypto_for`, `bridge_for`, or `assumption_for`
annotations. Tagged and named links are combined. An atom's focused Spec and Bridge views also
list the assumptions referenced in the types of its theorems. An external atom with an
assumption counts as covered, and an assumption about a trait covers its methods; types and
traits need no spec.

An assumption must be a proposition-valued definition in a Spec or Bridge module. The export
audit accepts only Lean's foundational axioms and recorded Aeneas opaque functions; admissions
and all other axioms fail validation.

Tags establish relevance, not mathematical adequacy. The assumptions remain trusted
hypotheses, and their scope must still be reviewed. Untagged supporting declarations remain
visible in full-file mode.

## Lean rendering

Lean code is rendered by [Verso](https://github.com/leanprover/verso): pointing at a name shows
its type and docstring, and pointing at a tactic shows the proof state after it.
`explorer/verso.mjs` exports each module with SubVerso, renders it with Verso
(`explorer/verso/Render.lean`), and cuts the result into source lines. The output is cached in
`.lake/explorer/verso/`, keyed by the source hash, so only changed files are rendered again; a
module takes 20 to 60 seconds. A file without a current render keeps the explorer's plain
colouring. Verso is pinned in `lakefile.toml` and is built only by this step.

## Verification and publication

Run `bash scripts/check.sh` with Node.js and the pinned Rust/Lean dependencies installed.
`scripts/setup-tools.sh` fetches the locked Cargo dependencies. After changing a crate's
dependencies, fetch them once before running the offline checks.
It checks every Rust crate, builds all present Lean modules, exports compiler metadata, renders
the Lean files with Verso, rebuilds the offline artifact and generated `manifest.json`, and
checks that the committed artifact is fresh.

`node explorer/build.mjs` can rebuild the viewer after UI-only changes. Lean changes require
`source scripts/env.sh` followed by `node explorer/export.mjs` and `node explorer/verso.mjs`
first. `node explorer/qa.mjs` provides optional Playwright checks and screenshots; it is not run by
the check command. Requires Playwright and an installed Chromium browser.

The GitHub workflow uploads a downloadable PR snapshot. Pages deployment runs only after a
successful push build of `main` in `Beneficial-AI-Foundation/bridging-examples`, with deployment
permissions confined to that job. A maintainer must enable GitHub Actions as the Pages source.
See [GitHub's workflow documentation](https://docs.github.com/en/pages/getting-started-with-github-pages/using-custom-workflows-with-github-pages).

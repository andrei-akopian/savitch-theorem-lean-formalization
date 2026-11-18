# Savitch's lemma in Lean

> [!WARNING]
> Project is currently pure AI slop produced by a combination of Sonnet 5.5, GPT6 Luna, and Gemini 4 Hydrongen. I haven't checked anything by hand at all.

Lean 4 project using Mathlib. The Lean toolchain and Mathlib are pinned to
`v4.35.0` so the project builds reproducibly.

The paper is included as [`savitch-paper-original.pdf`](savitch-paper-original.pdf)
and as a searchable, page-marked text extraction in
[`savitch-paper-original.md`](savitch-paper-original.md). The PDF remains the
source of truth for formulas and typography.

## Progress

The abstract register machine, tag-soundness invariant, termination argument,
Savitch's Lemmas 1–3, the concrete multitape simulator (`savitchSimulator`),
alphabet compression (`AlphabetCompression`), iterative deepening (`IterativeDeepening`),
and Savitch's Theorem (`savitch_theorem_one_full` in `SavitchLemma/MainTheorem.lean`)
are all formalized with no `sorry`s. See [`docs/ARCHITECTURE.md`](docs/ARCHITECTURE.md)
for the module map.

## Project layout

- `SavitchLemma.lean` is the public umbrella exporting the abstract proofs and `MainTheorem`.
- `SavitchLemma/Abstract/` contains the abstract register machine, reachability, and Lemmas 1–3.
- `SavitchLemma/Model/` contains the multitape machine model, TM combinators, IDs, and bit encoding.
- `SavitchLemma/Tape/` and `SavitchLemma/RegisterTape/` contain the concrete tape and register-tape operations.
- `SavitchLemma/Simulator/` (with `Step/` and `Valid/` subpackages) contains the concrete D0–D3 simulator and `MainBridge`.
- `SavitchLemma/SpaceBounds/` contains `RulerWriter`, `AlphabetCompression`, and `IterativeDeepening`.
- `SavitchLemma/MainTheorem.lean` proves the main theorems (`savitch_theorem_one`, `savitch_theorem_one_measurable`, `savitch_theorem_one_of_measurable`, `savitch_theorem_one_full`).
- `TapePrimitives`, `RegisterTapeOps`, and `SavitchSimulator` remain as compatibility facades.

## Build

With elan installed, from this directory run:

```sh
lake exe cache get
lake build
```

The first command downloads Mathlib's precompiled build cache; the first setup
may take a little while.

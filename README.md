# Savitch's lemma in Lean

Lean 4 project using Mathlib. The Lean toolchain and Mathlib are pinned to
`v4.35.0` so the project builds reproducibly.

The paper is included as [`savitch-paper-original.pdf`](savitch-paper-original.pdf)
and as a searchable, page-marked text extraction in
[`savitch-paper-original.md`](savitch-paper-original.md). The PDF remains the
source of truth for formulas and typography.

## Progress

The abstract register machine, tag-soundness invariant, termination argument,
and Savitch Lemma 1 are formalized. The remaining milestones and current module
layout are tracked in [`PLAN.md`](PLAN.md).

The concrete tape backend is organized into focused alphabet, tape-operation,
register-tape, and simulator modules. See [`docs/ARCHITECTURE.md`](docs/ARCHITECTURE.md)
for the module map and import conventions.

## Project layout

- `SavitchLemma.lean` is the public umbrella for the abstract proofs.
- `SavitchLemma/` contains the abstract algorithm, reachability, and machine model.
- `SavitchLemma/Tape/`, `SavitchLemma/RegisterTape/`, and
  `SavitchLemma/Simulator/` contain the concrete backend in smaller modules.
- The original `TapePrimitives`, `RegisterTapeOps`, and `SavitchSimulator` module
  paths remain as compatibility facades.

## Build

With elan installed, from this directory run:

```sh
lake exe cache get
lake build
```

The first command downloads Mathlib's precompiled build cache; the first setup
may take a little while.

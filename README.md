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

## Build

With elan installed, from this directory run:

```sh
lake exe cache get
lake build
```

The first command downloads Mathlib's precompiled build cache; the first setup
may take a little while.

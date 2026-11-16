# Savitch's lemma in Lean

Lean 4 project using Mathlib. The Lean toolchain and Mathlib are pinned to
`v4.35.0` so the project builds reproducibly.

## Build

With elan installed, from this directory run:

```sh
lake exe cache get
lake build
```

The first command downloads Mathlib's precompiled build cache; the first setup
may take a little while.

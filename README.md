# Savitch's Theorem in Lean 4

> [!NOTE]
> The proofs were machine-generated and kernel-checked in Lean 4 (`v4.35.0`, Mathlib `v4.35.0`).
> All proofs compile with no `sorry`s and depend only on the standard Lean axioms
> (`propext`, `Classical.choice`, `Quot.sound`). What has **not** been audited by hand
> is statement fidelity: confirming that the formal definitions of machines, space bounds,
> and measurability match Savitch (1970).

The paper is included as [`savitch-paper-original.pdf`](savitch-paper-original.pdf)
and as a searchable, page-marked text extraction in
[`savitch-paper-original.md`](savitch-paper-original.md). The PDF remains the
source of truth for formulas and typography.

## External review guide

To audit the formalization without reading ~25k lines of simulator proofs:

1. **Machine & space definitions:** [`SavitchLemma/Model/MachineDefinitions.lean`](SavitchLemma/Model/MachineDefinitions.lean)
   isolates the trusted definitions (`MultitapeNTM`, `MultitapeDTM`, `OneSidedTape`,
   `AcceptsLanguageWithinSpace`, `HaltsScanningExactly`, `IsMeasurable`) with no internal
   bounded-capacity proof machinery.
2. **Theorem statements:** [`SavitchLemma/MainTheorem.lean`](SavitchLemma/MainTheorem.lean)
   states and proves `savitch_theorem_one`, `savitch_theorem_one_measurable`,
   `savitch_theorem_one_of_measurable`, and `savitch_theorem_one_full`
   (`NSPACE(L) ⊆ DSPACE(L^2)` for `1 ≤ L n` and `n ≤ 2 ^ L n`).
3. **Non-vacuity check:** [`SavitchLemma/Examples/SanityCheck.lean`](SavitchLemma/Examples/SanityCheck.lean)
   instantiates `savitch_theorem_one_full` on a concrete 2-state NTM accepting non-empty
   `Bool` strings in space `n + 1`.

## Lemma 2 discrepancy with the paper

The formalization uncovered and certified a bug in the printed local statement of
**Lemma 2** in Savitch (1970, p. 183): the printed bound `2^j` (one-based) fails at `j = 1`.
The true bound is `2^(j - 1)` (i.e. `2^j` in zero-based Lean indexing), and
`savitch_abstract_completeness` uses one extra work register so paths of length up to `2^r`
are still covered. See [`docs/LEMMA2_COUNTEREXAMPLE.md`](docs/LEMMA2_COUNTEREXAMPLE.md) for
the full write-up and [`SavitchLemma/Abstract/LemmaTwoCounterexample.lean`](SavitchLemma/Abstract/LemmaTwoCounterexample.lean)
for the Lean-certified counterexample.

## Project layout

- [`SavitchLemma.lean`](SavitchLemma.lean) — public entry point (`MachineDefinitions`, `MainTheorem`, `Examples.SanityCheck`).
- `SavitchLemma/Abstract/` — abstract register machine, reachability, Lemma 2 counterexample, and corrected Lemmas 1–3.
- `SavitchLemma/Model/` — isolated external definitions (`MachineDefinitions.lean`), finite-capacity equivalence (`MachineModel.lean`), TM combinators, IDs, and bit encoding.
- `SavitchLemma/Tape/` and `SavitchLemma/RegisterTape/` — concrete tape and register-tape operations.
- `SavitchLemma/Simulator/` (with `Step/` and `Valid/` subpackages) — concrete D0–D3 simulator and `MainBridge`.
- `SavitchLemma/SpaceBounds/` — `RulerWriter`, `AlphabetCompression`, and `IterativeDeepening`.
- `SavitchLemma/MainTheorem.lean` — Theorem 1 (measurable and general cases).
- `SavitchLemma/Examples/` — non-vacuity sanity check.

See [`docs/ARCHITECTURE.md`](docs/ARCHITECTURE.md) for the full module map and dependency flow.

## Build

With `elan` installed, from this directory run:

```sh
lake exe cache get
lake build
```

The first command downloads Mathlib's precompiled build cache.

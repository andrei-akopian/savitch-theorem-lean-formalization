# Savitch's Theorem in Lean 4 — Status & Design Notes

The formalization of Savitch's Theorem 1 (`NSPACE(L) ⊆ DSPACE(L^2)` for `1 ≤ L n`
and `n ≤ 2 ^ L n`, both measurable and general non-measurable cases) is **complete**
and builds cleanly with `lake build`.

For the current module map and dependency flow, see [`docs/ARCHITECTURE.md`](docs/ARCHITECTURE.md).
For the Lemma 2 discrepancy with Savitch (1970, p. 183), see
[`docs/LEMMA2_COUNTEREXAMPLE.md`](docs/LEMMA2_COUNTEREXAMPLE.md).

## Key design choices

- **Isolated external definitions:** [`SavitchLemma/Model/MachineDefinitions.lean`](SavitchLemma/Model/MachineDefinitions.lean)
  contains only the one-sided machine model, acceptance, and measurability definitions
  needed to audit the theorem statements in [`SavitchLemma/MainTheorem.lean`](SavitchLemma/MainTheorem.lean).
- **Abstract-first separation:** `SavitchLemma/Abstract/` proves termination, Lemma 1,
  and the corrected Lemmas 2–3 (`2^j` for zero-based index `j`, with `r + 1` work
  registers in `savitch_abstract_completeness`) independently of tape-head arithmetic.
- **Sealed TM components:** `SealedTMComponent` in `SavitchLemma/Model/TMCombinators.lean`
  hides deep `Sum`/`Prod` state trees behind an existential `Fintype` package so
  downstream `toDTM` compilation synthesizes `Fintype` in O(1) without raising
  `synthInstance.maxSize`.
- **Optional future extensions:** Savitch's Theorems 2–3 and Section 3 (threadable mazes /
  Theorems 4–5) are not yet formalized.

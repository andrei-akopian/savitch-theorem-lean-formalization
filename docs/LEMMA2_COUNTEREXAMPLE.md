# Lemma 2 Counterexample and Correction

This note documents a discrepancy between the printed statement of **Lemma 2** in Savitch (1970) ([`savitch-paper-original.pdf`](../savitch-paper-original.pdf), p. 183; [`savitch-paper-original.md`](../savitch-paper-original.md)) and the Lean 4 formalization.

## What fails in the printed Lemma 2

In the paper (p. 183, one-based register indexing `i = 1, 2, …`), Lemma 2 states that if the first `j` registers are untagged, register `j` holds an ID `x` reachable from a tagged register in at most `2^j` steps, then the deterministic register machine `ZD` eventually tags `x` in register `j`.

At the base case **`j = 1`** (zero-based index `i0 = 0` in Lean):
- `2^1 = 2` steps are allowed by the printed bound.
- However, with `j = 1` (no lower registers to hold an intermediate midpoint), `D1` only tests **single-step** reachability (`0` or `1` transition) from a tagged register.
- When `x` is at distance **2** from the tagged source, `D1` fails to tag `x`, `D3` increments register `1` past `x` up to the maximum code `N`, and the machine never tags `x`.

### Lean-certified counterexample

[`SavitchLemma/Abstract/LemmaTwoCounterexample.lean`](../SavitchLemma/Abstract/LemmaTwoCounterexample.lean) constructs an explicit finite instance (`N = 5`, `r = 2` work registers, source `1` tagged in register `2`, transitions `1 → 2 → 3`) and proves `printed_lemma2_counterexample`:

1. `start` is reachable from `zdInitial 2 5 hN src`.
2. In `start`, register `0` (`j = 1` in 1-based) holds `3` (untagged), register `1` holds `4` (untagged), and the source register holds `1` (tagged).
3. `ReachesWithin problem 2 code1 code3` holds (`1 → 2 → 3`).
4. The deterministic `zdStep` run from `start` reaches a stuck configuration `s9` (`zdStep problem hN s9 = none`), and **no** configuration on any continuation from `start` ever has register `0` holding `3` with `tag = true` (`target_never_tagged`).

## The corrected hypothesis

The true bound for zero-based register index `j : Fin r` is **`2 ^ j.val`** (i.e. **`2 ^ (i - 1)`** in one-based notation):
- Base case `j = 0` (1-based `i = 1`): `2^0 = 1` step (tested directly by `D1`).
- Inductive step `j + 1`: `2^(j + 1) = 2^j + 2^j` steps, using the lower registers `0 .. j - 1` to search for a midpoint at distance `≤ 2^j`.

This corrected form is proved in [`SavitchLemma/Abstract/LemmasTwoThree.lean`](../SavitchLemma/Abstract/LemmasTwoThree.lean):
- `lemma_two_three` proves the unified Lemmas 2–3 with bound `2 ^ j`.
- `lemma_two_corrected` and `lemma_three_corrected` are its corollaries.
- `savitch_abstract_completeness` uses `r + 1` work registers so that paths of length up to `2^r` are still covered (at register index `r`), preserving the `O(L(n)^2)` space bound without any extra hypotheses.

## Simulator usage

The concrete 5-tape simulator (`SavitchLemma/Simulator/SavitchDriver.lean`) and `MainTheorem.lean` use `savitch_abstract_completeness` from `LemmasTwoThree.lean` (the corrected Lemma 1–3 chain).

# Savitch's Theorem in Lean 4 — Implementation Plan

## Goal and references

The primary goal is a Lean proof of Savitch's Theorem 1: nondeterministic space
`L(n)` can be simulated deterministically in `O(L(n)^2)` space, under the
paper's stated lower bound. The paper's extensions and maze results are later,
optional milestones.

- Original source: [`savitch-paper-original.pdf`](savitch-paper-original.pdf)
- Searchable extraction, with printed-page markers:
  [`savitch-paper-original.md`](savitch-paper-original.md)
- Text extraction is a navigation aid. Check the PDF when formulas, symbols,
  or OCR-like glyphs matter.

## Environment and conventions

- Lean `v4.35.0`, Mathlib `v4.35.0`; build with `lake build`.
- Keep mathematical modules narrowly imported. `SavitchLemma.lean` is the
  public umbrella module.
- The abstract register algorithm is developed independently from the tape
  machine. This avoids introducing tape-head arithmetic into Lemmas 1–3.
- Register indices in Lean are zero-based. Any exponent or prefix bound copied
  from the paper must be translated explicitly; do not assume the paper's
  one-based `j` is the Lean `Fin` value `j`.

## Current formalization

The abstract layer is implemented and builds successfully.

| Module | Status | Contents |
| --- | --- | --- |
| `SavitchLemma/SavitchAlgorithm.lean` | Done | `AbstractProblem`, valid codes, `ZDConfig`, D0 initialization, D1/D2/D3 step, and tag soundness. |
| `SavitchLemma/Selection.lean` | Done | Least-untagged and least-below-maximum search facts. |
| `SavitchLemma/ConfigUpdates.lean` | Done | Pointwise facts for D2/D3 register updates. |
| `SavitchLemma/Reachability.lean` | Done | Reserved-code reachability exclusions and the D1 maximum-code test fact. |
| `SavitchLemma/StepBehavior.lean` | Done | D1/D2/D3 control-flow and exact D3 update shape. |
| `SavitchLemma/Termination.lean` | Done | Decreasing colexicographic remaining-capacity measure; every run reaches a stuck configuration; stuck configurations have all work registers at `N`. |
| `SavitchLemma/LemmaOne.lean` | Done | Lemma 1's two outcomes, progress invariant, and `lemma_one`. |
| `SavitchLemma/BoundedReachability.lean` | In progress | Exact/at-most paths, concatenation, and midpoint splitting are proved; finite-state path shortening remains. |

`SavitchLemma.lean` imports these modules. No machine model, ID encoding, or
Theorem 1 proof has been connected yet.

### Abstract code and indexing choices

- A code is `Fin (N + 1)`. Valid IDs use values `1 ≤ x < N`; `0` and `N` are
  reserved. `AbstractProblem` excludes transitions into either reserved code.
- A register configuration has `r` work registers plus a final source register.
- In `LemmaOne.lean`, paper register `i` corresponds to Lean index `j = i - 1`.
  Outcome A writes the requested code to `j`; Outcome B tags the least
  initially-untagged register strictly to its right.
- The termination potential uses digit `2 * value + tag` and its remaining
  capacity `2 * N + 1 - digit`, ordered colexicographically with higher register
  indices more significant. Each machine step decreases this measure. This is
  more precise than the earlier proposed claim that every step simply
  increments the register tuple.

## Planned file structure

Keep the current small abstract modules at the root of `SavitchLemma/`. Add the
remaining modules as their proofs become ready; avoid empty placeholder files.

```text
SavitchLemma.lean                         # Public umbrella
SavitchLemma/
├── SavitchAlgorithm.lean                 # Abstract register machine and soundness
├── Selection.lean                        # Finite least-index searches
├── ConfigUpdates.lean                    # Register update behavior
├── Reachability.lean                     # Reserved codes / abstract graph facts
├── StepBehavior.lean                     # D1/D2/D3 transition lemmas
├── Termination.lean                      # Well-founded progress and stuck states
├── LemmaOne.lean                         # Lemma 1 (complete)
├── BoundedReachability.lean              # Finite path lengths and path shortening [in progress]
├── LemmasTwoThree.lean                   # Simultaneous divide-and-conquer induction
├── MachineModel.lean                     # Read-only input + bounded work tapes + NTM
├── InstantaneousDesc.lean                # IDs, code embedding, configuration count
├── MainTheorem.lean                      # Theorem 1 and space analysis
└── Mazes.lean                            # Optional Section 3 / Theorems 4–5
```

Dependency outline:

```text
SavitchAlgorithm + helpers + Termination + LemmaOne
                         ↓
             BoundedReachability
                         ↓
                LemmasTwoThree

MachineModel → InstantaneousDesc ─────────┐
                                          ├→ MainTheorem
Abstract register proofs ─────────────────┘
                                          ↓
                                  optional Mazes
```

## Remaining work, in dependency order

### 1. Bounded graph reachability — in progress

In `BoundedReachability.lean`:

- Define exact-length and at-most-length paths over `AbstractProblem.step`.
- Prove reflexivity, monotonicity in the bound, concatenation, and midpoint
  splitting for a path of length at most `2^m`.
- Prove finite-state path shortening: if one valid code reaches another, a
  path with no repeated intermediate code suffices, hence the path length is
  bounded by the number of valid codes.

The exact path-length API, at-most bounds, concatenation, and power-of-two
midpoint split are already proved in `BoundedReachability.lean`.

Keep this graph-level API independent from the Turing machine. It will support
both Lemmas 2–3 and the configuration-count bound used by Theorem 1.

### 2. Lemmas 2 and 3 — abstract algorithm

In `LemmasTwoThree.lean`:

- State both lemmas as predicates on `ZDConfig`, including untouched suffixes
  and the tag conditions from pp. 183–184.
- Prove them simultaneously by induction, using Lemma 1 and the midpoint split.
- Derive the exact exponent/index mapping from the paper before fixing the Lean
  statement. The paper uses one-based register `j` and a `2^j` path bound; with
  Lean index `j - 1`, this corresponds to `2^(j.val + 1)` unless the statement
  is deliberately reparameterized.

**Source-consistency gate:** Do not formalize the printed Lemma 2 statement
until its hypotheses are reconciled with the implemented D0–D3 machine. A
small finite simulation gives a suspicious case with `N = 5`, `r = 2`,
`I₀ = 1`, and transitions `1 → 2 → 3`. At the reachable configuration
`<3, 4, 1>, <0, 0, 1>`, the premise for paper index `j = 1` holds: the tagged
source reaches the target in two steps (`2^1`), while the target register's
tag is clear. But D1 has no tagged predecessor for `3`; D3 increments the
target through the maximum and the run eventually reaches all registers at
`N` without tagging `3`. This appears to contradict the local conclusion as
printed on p. 183. Recheck the PDF's exponent and all implicit configuration
conditions (or the intended D1–D3 semantics) before choosing a correction; do
not silently weaken the bound or strengthen the hypotheses.

### 3. Multitape nondeterministic machine model

In `MachineModel.lean`:

- Model a read-only input tape with end markers and a finite number of
  read/write work tapes.
- Give nondeterministic transitions finite branching, configurations, initial
  configurations, and acceptance.
- Define the space bound to match Savitch's “nonblank portion” convention.
  Validate the list-pair tape representation against head movement and blank
  trimming before relying on it for the main theorem.
- Define acceptance within storage and measurable space functions.

### 4. Instantaneous descriptions and finite bounds

In `InstantaneousDesc.lean`:

- Encode valid bounded-space configurations as IDs and embed those IDs into the
  abstract code domain.
- Prove that the induced transition relation satisfies the reserved-code
  assumptions of `AbstractProblem`.
- Prove a cardinality bound on valid IDs and instantiate the finite path
  shortening result. Keep constants and logarithm ceilings explicit until the
  final `O(L(n))` space statement.

### 5. Theorem 1

In `MainTheorem.lean`:

- Connect bounded NTM computations to the abstract graph and obtain a short
  accepting path from the finite-ID bound.
- Apply Lemmas 1–3 to show the deterministic algorithm discovers an accepting
  ID; then formalize the accepting version of D2.
- Prove the measurable-space case first, including the register/tape space
  calculation and alphabet compression.
- Formalize the non-measurable iterative-deepening argument separately, using
  the fixed-bound termination theorem already proved for the abstract machine.

### 6. Optional paper extensions

- `Mazes.lean`: formalize threadable finite mazes, the log-space NTM, and
  Theorems 4–5.
- Add Theorem 2 and Theorem 3 only after Theorem 1 is complete; they should not
  complicate the core proof modules.

## Corrections to the earlier draft plan

- The code now proves Lemma 1 before introducing the tape model, following the
  recommended abstract-first execution order.
- The earlier flat architecture combined the machine model, IDs, all register
  lemmas, and the main theorem too early; the revised tree separates those
  proof layers and reflects the modules already present.
- The earlier `0`-based Lemma 2/3 base-case suggestion did not establish the
  exponent translation from the paper. The `2^(j.val + 1)` mapping must be
  handled explicitly.
- The earlier termination note understated D2's resets. The checked Lean proof
  uses a colexicographic remaining-capacity potential that accounts for both
  tags and register contents.

## Validation

After each milestone, run `lake build` from the repository root. Keep the
abstract results free of `sorry`/`admit`; do not connect the machine model to
the algorithm until the code embedding and reserved-code proofs compile.

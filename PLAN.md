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
| `SavitchLemma/BoundedReachability.lean` | Done | Exact/at-most paths, concatenation, positive power-of-two midpoint splitting, and finite-state shortening to at most `N` edges on `Fin (N + 1)`. |
| `SavitchLemma/LemmaTwoCounterexample.lean` | Done | Lean-certified counterexample to the printed local Lemma 2 statement, including reachability from D0 and the deterministic continuation to a stuck state. |
| `SavitchLemma/LemmasTwoThree.lean` | Done | Unified corrected Lemmas 2–3 (`2^j` for zero-based index `j`), the paper-shape corollaries, and abstract completeness using one extra work register. |
| `SavitchLemma/MachineModel.lean` | In progress | Finite-capacity input/work tapes, finite-branching transitions, bounded acceptance, finite configurations, a cardinality formula, and per-tape capacity bounds. |
| `SavitchLemma/InstantaneousDesc.lean` | In progress | Embeds finite configurations into valid abstract codes, builds the induced transition problem, bounds concrete runs, and derives abstract tagged acceptance at a ceiling-log register budget. |
| `SavitchLemma/SpaceAnalysis.lean` | In progress | Bounds the configuration count exponentially in capacity and proves an abstract accepting-run transfer with quadratic register-storage proxy under `n ≤ 2^S`. |

`SavitchLemma.lean` imports these modules without the broad `Mathlib` umbrella.
The finite-capacity machine model is connected to abstract IDs and register
completeness. It is not yet related to standard unbounded-tape space semantics,
or to a concrete deterministic tape simulator for Theorem 1.

### Abstract code and indexing choices

- A code is `Fin (N + 1)`. Valid IDs use values `1 ≤ x < N`; `0` and `N` are
  reserved. `AbstractProblem` excludes transitions into either reserved code.
- A register configuration has `r` work registers plus a final source register.
- In `LemmaOne.lean`, paper register `i` corresponds to Lean index `j = i - 1`.
  Outcome A writes the requested code to `j`; Outcome B tags the least
  initially-untagged register strictly to its right.
- The corrected Lemmas 2–3 use the path bound `2 ^ j.val`, i.e. `2^(i-1)` for
  the paper's one-based register `i`. `savitch_abstract_completeness` uses
  `r + 1` work registers to handle paths of at most `2^r`; the extra register
  does not change the asymptotic space bound.
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
├── BoundedReachability.lean              # Finite path lengths, midpoint splitting, path shortening
├── LemmaTwoCounterexample.lean            # Certified source-statement counterexample
├── LemmasTwoThree.lean                   # Corrected simultaneous induction and abstract completeness
├── MachineModel.lean                     # Finite-capacity input/work tapes + NTM [in progress]
├── InstantaneousDesc.lean                # IDs, code embedding, configuration count
├── SpaceAnalysis.lean                     # Configuration-count and register-space arithmetic
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

### 1. Bounded graph reachability — done

In `BoundedReachability.lean`:

- Define exact-length and at-most-length paths over `AbstractProblem.step`.
- Prove reflexivity, monotonicity in the bound, concatenation, and midpoint
  splitting for a path of length at most `2^m`.
- Prove finite-state path shortening: a shortest path has no repeated vertices,
  hence a path on `Fin (N + 1)` has at most `N` edges.

The exact path-length API, at-most bounds, concatenation, positive-midpoint
power-of-two splitting, and finite-state shortening are proved in
`BoundedReachability.lean`.

Keep this graph-level API independent from the Turing machine. It will support
both Lemmas 2–3 and the configuration-count bound used by Theorem 1.

### 2. Lemmas 2 and 3 — abstract algorithm — done

In `LemmasTwoThree.lean`:

- The unified `lemma_two_three` proves the corrected form with reset prefix,
  tagged middle block, untouched suffix, and positive target code.
- `lemma_two_corrected` and `lemma_three_corrected` are its empty/nonempty
  middle-block corollaries.
- `savitch_abstract_completeness` uses `r + 1` work registers to tag any target
  reachable within `2^r` steps.

**Source-consistency resolution:** The PDF confirms that printed p. 183 says
`2^j`; `LemmaTwoCounterexample.lean` certifies that this literal local claim is
false at its `j = 1` base case for the encoded D0–D3 machine. As `review.md`
diagnoses, the inductive step needs `j - 1` lower registers to hold the
midpoint, while D1 itself checks only one transition. The formalization keeps
the counterexample and uses the corrected bound `2^(j-1)` in one-based
notation (`2^j.val` in Lean). `savitch_abstract_completeness` adds one work
register so paths of up to `2^r` steps are still covered, without changing the
asymptotic space bound; no unmentioned side condition is assumed.

The review's import cleanup was also applied: the umbrella no longer imports
all of Mathlib, and the bounded-reachability and termination modules use
targeted positivity/tactic imports.

### 3. Multitape nondeterministic machine model — in progress

In `MachineModel.lean`:

- Model a read-only input tape with end markers and a finite number of
  read/write work tapes.
- Give nondeterministic transitions finite branching, configurations, initial
  configurations, and acceptance.
- Use `Fin S → Γ` plus a `Fin S` head for each bounded work tape; the current
  model exposes the finite configuration type and its cardinality. Each head
  remains in range, and the current nonblank-cell set has size at most `S`.
- Define the space bound to match Savitch's “nonblank portion” convention.
  Still needed: relate a standard unbounded-tape computation that scans at most
  `S` cells to the finite-capacity semantics, including boundary and
  initial-head conventions.
- Define acceptance within storage and measurable space functions.

### 4. Instantaneous descriptions and finite bounds — in progress

In `InstantaneousDesc.lean`:

- `finiteConfigCode` uses `Fintype.equivFin` and a shifted finite index to embed
  each bounded configuration type into `ValidCode`.
- `multitapeProblem` induces the abstract transition relation and proves the
  reserved zero/maximum codes cannot be transition targets.
- `multitapeProblem_run_short_path` turns any bounded machine run into an
  abstract path of at most `card(configuration) + 1` edges.
- `acceptingRun_is_tagged_abstractly` combines that path with abstract
  completeness to tag an accepting ID when `2^r` covers the configuration
  count plus one.
- `acceptsWithinCapacity_abstractly` chooses `r = Nat.clog 2 (card + 1)` and
  gives the corresponding ceiling-log register budget directly.
- `SpaceAnalysis.lean` bounds the configuration count exponentially in `S`
  under `n ≤ 2^S`, then proves that `(r + 2) * (codeWidth + 1)` is quadratic
  in `S + 1` for fixed control/alphabet/tape parameters. Here `r` and
  `codeWidth` are the ceiling-log configuration-count bounds.
- `acceptsWithinCapacity_abstractly_with_space_bound` combines the bounded
  machine run, abstract ID path, corrected Lemmas 2–3, and storage arithmetic.
- Still needed: prove the finite-capacity model matches the paper's space
  convention and connect `r` to the original space bound with explicit
  logarithm ceilings.

### 5. Theorem 1

In `MainTheorem.lean`:

- The abstract finite-capacity acceptance transfer is available from
  `SpaceAnalysis.lean`.
- Still needed: model the deterministic register algorithm as a tape machine,
  connect the finite-capacity semantics to the paper's standard space
  convention, and formalize the accepting version of D2.
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
- The literal printed Lemma 2/3 bound is off by one at the base case. The
  formalized bound is `2^j.val` for zero-based Lean index `j`, and one extra
  work register preserves the `2^r` path bound needed by the main theorem.
- The earlier termination note understated D2's resets. The checked Lean proof
  uses a colexicographic remaining-capacity potential that accounts for both
  tags and register contents.

## Validation

After each milestone, run `lake build` from the repository root. Keep the
abstract results free of `sorry`/`admit`; the machine-to-ID embedding and
reserved-code proofs now compile and are covered by the project build.

# Code Review: Savitch's Theorem in Lean 4

Reviewed: commit `54db4fc` (~25k lines of Lean across 60 files, Lean/Mathlib `v4.35.0`).

## Method and limits

- I ran `lake build`. It succeeds.
- I ran `#print axioms SavitchLemma.savitch_theorem_one_full`. It reports only `propext`, `Classical.choice` and `Quot.sound`.
- I grepped for `sorry`, `axiom`, `native_decide`, `admit`, `unsafe`, `implemented_by` and `set_option`. The only hits are the `set_option` items listed under Findings.
- I read the machine model and acceptance definitions in `Model/MachineModel.lean`, plus the top-level theorems in `MainTheorem.lean`.
- I did not read the roughly 20k lines of simulator and tape-operation proofs line by line. Kernel acceptance covers their correctness. The risks below are about what is stated, and about maintainability.
- I did not check the formalization against the PDF.

## Summary

The proof appears sound. It is complete, uses no extra axioms, and builds cleanly. The remaining risks are these:

1. **Statement fidelity.** The formal definitions of acceptance, space and "measurable" need a human check against the paper.
2. **Maintainability.** Some files are very large, and there is no CI.
3. **Documentation drift.** `PLAN.md` and the README have stale or misleading parts.

The README says the code was machine-generated and never checked by hand. That makes item 1 the highest-value follow-up. A kernel-checked proof of the wrong statement is still the wrong statement.

## Findings

### High: statement fidelity (human review needed)

The kernel can't catch these.

**H1. Definition of `MultitapeNTM.AcceptsLanguageWithinSpace`** ([MachineModel.lean#L644](file:///Users/andrei/Documents/Coding/Projects/savitch-lemma/SavitchLemma/Model/MachineModel.lean#L644))
- The definition says:
  - Every `x ∈ A` has an accepting run with all heads `< L n`.
  - Every input the machine accepts, on unbounded tapes, is in `A`.
- This is a reasonable formulation.
- The head bound `HeadsWithin S` is a bound on head *positions*. The definition does not say "number of cells visited", but for one-sided tapes starting at 0 the two coincide.
- Check whether the paper's space measure counts the input tape and the end-markers.
- Check that the head bound is applied to every work tape, as `HeadsWithin` suggests.

**H2. `IsMeasurable` / `HaltsScanningExactly` / `IsMeasurableSim`**
- Savitch's "tape-constructible" notion (called "measurable" in the paper) is encoded as a 1-tape DTM that halts having scanned exactly `L n` work squares.
- I read the definitions, but I did not re-derive that they match the paper. Specifically:
  - In the `HaltsScanningExactly` shown above, the last conjunct asserts that some reachable configuration has head `= S - 1`, which is the "scanned exactly S squares" condition.
  - That conjunct is guarded by `0 < S`.
  - The final configuration is required to have no applicable transition (`transition … = none`), and halting is not required to be an accepting state. Confirm this matches the paper.
- The final theorem `savitch_theorem_one_full` is independent of this notion, which is the main reason the full theorem is trustworthy.

**H3. Theorem statement** (`savitch_theorem_one_full`, [MainTheorem.lean#L170-L187](file:///Users/andrei/Documents/Coding/Projects/savitch-lemma/SavitchLemma/MainTheorem.lean#L170-L187))
- The conclusion is `∃ QD D L' C, D.Accepts… A L' ∧ ∀ n, L' n ≤ C * (L n + 1)^2`.
- The simulating machine `D` has 5 tapes and the alphabet `SimSym`. That is fine for a statement about O(L²) space.
- The hypothesis `n ≤ 2^L n` with `1 ≤ L n` matches the paper.
- The `(L n + 1)^2` slack, rather than `L n ^ 2`, is justified by `L n ≥ 1` but should be documented as the paper's O(·) constant.
- Add a short docstring that states the theorem in plain language: "NSPACE(L) ⊆ DSPACE(L²) for L(n) ≥ 1 and n ≤ 2^L(n)". The README partly does this, but the theorem itself carries no such statement.
- Add one trivial sanity-check example: for a concrete small machine and language, show the hypotheses are satisfiable. This prevents vacuity, for example from a mis-stated `AcceptsLanguageWithinSpace`.

**H4. Lemma 2 counterexample**
- [LemmaTwoCounterexample.lean](file:///Users/andrei/Documents/Coding/Projects/savitch-lemma/SavitchLemma/Abstract/LemmaTwoCounterexample.lean) (585 lines) certifies that the paper's printed local Lemma 2 is false as stated.
- `LemmasTwoThree.lean` then proves a corrected version.
- This is a significant claim. It deserves a prominent write-up covering:
  - What exactly fails.
  - What the corrected hypothesis is.
  - A pointer to the paper page.
- Right now this is only in the file list. Put it in `docs/` and the README.
- Double-check that the Lemma 1 to 3 chain that the simulator uses is the corrected one. The kernel guarantees it type-checks, but a reader needs to know.

### Medium: maintainability

**M1. Very large files**
- The largest are:
  - `AlphabetCompression.lean` (1221 lines)
  - `IterativeDeepeningPrimitives.lean` (1223)
  - `StepScanCells.lean` (1049)
  - `StepScanner.lean` (990)
  - `StepChecker.lean` (864)
  - `ReachableLoop.lean` (854)
- Compile time and incremental rebuild cost suffer, and review is hard.
- Split along natural seams. For example, separate definitions from correctness lemmas, and as `AlphabetCompressionDef.lean` already does, from correctness proofs.
- A common target is under 500 lines.

**M2. Global instance-search limits raised in four files**
- Affected files:
  - `MainTheorem.lean`
  - `MainBridge.lean`
  - `IterativeDeepening.lean`
  - `IterativeDeepeningPrimitives.lean`
- All four use `set_option synthInstance.maxSize 200000` and `synthInstance.maxHeartbeats 2000000`.
- The duplication suggests a deep `Fintype` instance tower on the 5-tape product states. Solutions:
  - Make the state types explicit with `abbrev`s or `deriving Fintype`.
  - Give a named `Fintype` instance with `inferInstanceAs`.
  - Put the options in one shared place with a comment.
- Raising the limits can hide an instance-diamond or a performance regression, and it makes builds fragile as Mathlib changes.

**M3. No CI**
- There is no `.github/` directory.
- Add a workflow that runs `lake build` and fails on warnings. Use the `leanprover/lean-action` action.
- Add a check that rejects `sorry` and `axiom`, and a `#print axioms` test file for the main theorems.
- Add `lake lint` / `batteries` linters and `lake exe lint-style` if desired.

**M4. Lakefile**
- Add `leanOptions := #[⟨`autoImplicit, false⟩, ⟨`linter.unusedVariables, true⟩]`. Consider `weak.linter.mathlibStandardSet`.
- This catches typos in binder names in a codebase this size.
- The `lakefile.lean` could use `lakefile.toml` instead. That is optional.

**M5. Compatibility facades**
- `TapePrimitives.lean`, `RegisterTapeOps.lean` and `SavitchSimulator.lean` are 11 to 23 line re-exporters.
- The package has no external users, so delete them or mark them deprecated.
- `SavitchLemma.lean` contains an empty `namespace SavitchLemma … end SavitchLemma`. Remove it.
- The umbrella imports `Model` and `Abstract` modules explicitly but reaches `Simulator`, `Tape` and `SpaceBounds` only through `MainTheorem`. Be consistent about whether it is the full public API or a minimal one.

**M6. Heavy `simp` attribute and proof style**
- Only about four `@[simp]` lemmas exist, which is good.
- With about 370 top-level theorems across large files, I could not review proof style. Use `lake exe shake` to find unused imports, and the Lean unused-variables and unused-`have` linters.
- `public import` / `@[expose] public section` is used everywhere. Check that this is deliberate with the new module system. It prevents hiding internals.

### Low: documentation

**L1. `PLAN.md` is stale.** It lists modules at `SavitchLemma/SavitchAlgorithm.lean`, `SavitchLemma/Selection.lean` and so on. They now live under `SavitchLemma/Abstract/`. Refresh the table, or delete the file and keep only `docs/ARCHITECTURE.md`.

**L2. README tone and claims**
- The "AI slop" warning is honest, but it undersells what is verified. State what is machine-checked (the axioms above) and what is not (definitions and statements).
- "No `sorry`s" is a claim; back it with the CI check from M3.
- Note the Lemma 2 discrepancy with the paper (H4).

**L3. Module docstrings.** Each file has a `/-! -/` header. Check that the large simulator files describe their invariant and how the pieces compose. `docs/ARCHITECTURE.md` should carry a dependency diagram.

**L4. Paper text extraction.** `savitch-paper-original.md` and the PDF are checked in. Confirm the licence allows redistribution. Otherwise move them out of the repository and link to the source.

**L5. `.gitignore`** is fine, but add `*.olean` is already there. Consider ignoring `.DS_Store`.

## Recommended next steps (priority order)

1. Have a human check H1 to H3 against the paper. Then add a plain-language docstring on `savitch_theorem_one_full`, and a non-vacuity example.
2. Write up the Lemma 2 counterexample (H4) in the docs.
3. Add CI with the `#print axioms` check (M3).
4. Replace the four `set_option` blocks by fixing the instance tower (M2).
5. Enable `autoImplicit false` and linters (M4).
6. Split the files over 800 lines (M1).
7. Refresh `PLAN.md`, the README and the facades (L1, L2, M5).

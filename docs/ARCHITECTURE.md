# Project architecture

This project formalizes Savitch's Theorem (`NSPACE(L) ⊆ DSPACE(L^2)` for
`1 ≤ L n` and `n ≤ 2 ^ L n`) by separating the abstract register-machine proof
from its concrete multitape Turing machine implementation, and by isolating the
external-review definitions (`Model/MachineDefinitions.lean`) from internal proof
machinery.

## Module map

```text
SavitchLemma.lean                       # Public entry point
SavitchLemma/
├── MainTheorem.lean                    # Theorem 1 (measurable and general cases)
├── Examples/
│   └── SanityCheck.lean                # Non-vacuity instantiation of Theorem 1
├── Abstract/
│   ├── SavitchAlgorithm.lean, Selection.lean, ConfigUpdates.lean
│   ├── Reachability.lean, StepBehavior.lean, Termination.lean
│   ├── LemmaOne.lean, BoundedReachability.lean
│   └── LemmaTwoCounterexample.lean, LemmasTwoThree.lean, AcceptingZD.lean
├── Model/
│   ├── MachineDefinitions.lean         # Isolated external-review definitions
│   ├── MachineModel.lean, TMCombinators.lean
│   ├── InstantaneousDesc.lean, SpaceAnalysis.lean
│   └── ConcreteEncoding.lean, SimCombinators.lean
├── Tape/
│   ├── Alphabet.lean                   # SimSym and TapeMatches
│   ├── Actions.lean                    # single-/two-tape actions
│   ├── BasicOperations.lean            # initialization, scans, rewind, clear
│   ├── BinaryArithmetic.lean           # decrementing bit tapes
│   └── Comparison.lean                 # bit comparison and fixed-width reads
├── RegisterTape/
│   ├── Layout.lean                     # tape roles and register encoding
│   ├── Copy.lean, Reset.lean
│   ├── FindUntagged.lean, Advance.lean, Tag.lean
│   └── Increment.lean, Initialization.lean
├── Simulator/
│   ├── Core.lean, Loops.lean           # shared actions, bit trackers, loop combinators
│   ├── InitPrimitives.lean, InitRegisters.lean, Initialize.lean
│   ├── ReachableLoop.lean, StepDriver.lean, SavitchDriver.lean
│   ├── MainBridge.lean                 # compiles savitchSimulator to MultitapeDTM
│   ├── Step/
│   │   ├── StepChecker.lean            # head-block comparison and input-move check
│   │   ├── StepScanInput.lean          # control-state decoder and input-head reader
│   │   ├── StepScanCells.lean          # per-tape cell scanner (scanTapeCells)
│   │   ├── StepScanTape.lean           # scanWorkTape and scanAllWorkTapes
│   │   ├── StepScanner.lean            # full checkStep and M.step equivalence
│   │   └── AcceptChecker.lean
│   └── Valid/
│       ├── ConfigValidity.lean, CheckValidB.lean
│       ├── ValidConfigB.lean, ConfigCheckB.lean
│       └── CheckValidBTop.lean, CheckValidAndStep.lean
└── SpaceBounds/
    ├── RulerWriter.lean                # ruler writer over SimSym
    ├── AlphabetCompressionDef.lean     # block encoding and rwCompGen
    ├── AlphabetCompressionSim.lean     # step-by-step simulation proofs for rwCompGen
    ├── AlphabetCompression.lean        # cleanup and rwg_prefix
    ├── IterativeDeepeningTapeOps.lean  # CleanTapesFor, idInit, rewindInputHead, extendRuler
    ├── IterativeDeepeningPrimitives.lean # binary counter (checkInputLenComp)
    └── IterativeDeepening.lean         # non-measurable Theorem 1
```

## Dependency flow

```text
Model.MachineDefinitions ──► Model.MachineModel ──► Model.TMCombinators ──► Tape.*
                                    │                                         │
                                    └──► Model.ConcreteEncoding ──────────────▼
                                                                        RegisterTape.*
                                                                              │
                                                                              ▼
                                                                         Simulator.*
                                                                        (Step/*, Valid/*)
                                                                              │
                                                                              ▼
                                                                        SpaceBounds.*
                                                                              │
                                                                              ▼
                                                                         MainTheorem ──► Examples.SanityCheck
```

## Validation

Run `lake build` from the repository root to build the full library
(including `MainTheorem` and `Examples.SanityCheck`). Compile an individual
module with `lake env lean path/to/Module.lean` when iterating on one file.

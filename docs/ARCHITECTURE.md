# Project architecture

This project formalizes Savitch's Theorem (`NSPACE(L) ⊆ DSPACE(L^2)` for
`1 ≤ L n` and `n ≤ 2 ^ L n`) by separating the abstract register-machine proof
from its concrete multitape Turing machine implementation.

## Module map

```text
SavitchLemma.lean
SavitchLemma/
├── MainTheorem.lean                    # Theorem 1 (measurable and general cases)
├── Abstract/
│   ├── SavitchAlgorithm.lean, Selection.lean, ConfigUpdates.lean
│   ├── Reachability.lean, StepBehavior.lean, Termination.lean
│   ├── LemmaOne.lean, BoundedReachability.lean
│   └── LemmaTwoCounterexample.lean, LemmasTwoThree.lean, AcceptingZD.lean
├── Model/
│   ├── MachineModel.lean, TMCombinators.lean
│   ├── InstantaneousDesc.lean, SpaceAnalysis.lean
│   └── ConcreteEncoding.lean, SimCombinators.lean
├── TapePrimitives.lean                 # compatibility facade
├── Tape/
│   ├── Alphabet.lean                   # SimSym and TapeMatches
│   ├── Actions.lean                    # single-/two-tape actions
│   ├── BasicOperations.lean            # initialization, scans, rewind, clear
│   ├── BinaryArithmetic.lean           # decrementing bit tapes
│   └── Comparison.lean                 # bit comparison and fixed-width reads
├── RegisterTapeOps.lean                # compatibility facade
├── RegisterTape/
│   ├── Layout.lean                     # tape roles and register encoding
│   ├── Copy.lean, Reset.lean
│   ├── FindUntagged.lean, Advance.lean, Tag.lean
│   └── Increment.lean, Initialization.lean
├── SavitchSimulator.lean               # compatibility facade
├── Simulator/
│   ├── Core.lean, Loops.lean           # shared actions, bit trackers, loop combinators
│   ├── InitPrimitives.lean, InitRegisters.lean, Initialize.lean
│   ├── ReachableLoop.lean, StepDriver.lean, SavitchDriver.lean
│   ├── MainBridge.lean                 # compiles savitchSimulator to MultitapeDTM
│   ├── Step/
│   │   ├── StepChecker.lean
│   │   ├── StepScanCells.lean, StepScanner.lean
│   │   └── AcceptChecker.lean
│   └── Valid/
│       ├── ConfigValidity.lean, CheckValidB.lean
│       ├── ValidConfigB.lean, ConfigCheckB.lean
│       └── CheckValidBTop.lean, CheckValidAndStep.lean
└── SpaceBounds/
    ├── RulerWriter.lean                # ruler writer over SimSym
    ├── AlphabetCompressionDef.lean     # block encoding and rwCompGen
    ├── AlphabetCompression.lean        # simulation and rwg_prefix
    ├── IterativeDeepeningPrimitives.lean
    └── IterativeDeepening.lean         # non-measurable Theorem 1
```

## Dependency flow

```text
Model.MachineModel ──► Model.TMCombinators ──► Tape.*
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
                                            MainTheorem
```

## Validation

Run `lake build` from the repository root to build the full library
(including `MainTheorem`). Compile an individual module with
`lake env lean path/to/Module.lean` when iterating on one file.

# Project architecture

This project separates the abstract proof of Savitch's algorithm from its
concrete multitape implementation. The public root module, `SavitchLemma.lean`,
exports the abstract layer. The concrete backend is kept outside that umbrella
so its unfinished simulator proofs do not block the abstract API.

## Module map

```text
SavitchLemma.lean
SavitchLemma/
├── SavitchAlgorithm.lean, Selection.lean, ConfigUpdates.lean
├── Reachability.lean, StepBehavior.lean, Termination.lean
├── LemmaOne.lean, BoundedReachability.lean, LemmasTwoThree.lean
├── MachineModel.lean, InstantaneousDesc.lean, SpaceAnalysis.lean
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
│   ├── Increment.lean, Initialization.lean
├── SavitchSimulator.lean               # compatibility facade
└── Simulator/
    ├── Core.lean                       # shared actions and bit trackers
    ├── InitPrimitives.lean, InitRegisters.lean, Initialize.lean
    ├── Loops.lean
    └── StepChecker.lean
```

The completed abstract proofs remain in small top-level modules. The concrete
implementation is divided by dependency and responsibility, keeping each Lean
file focused enough to inspect and iterate on independently.

The tape and register-tape chains compile through their compatibility facades.
The simulator chain currently compiles through `Simulator.Loops`; the
`Simulator.StepChecker` proof is still in progress and prevents
`SavitchLemma.SavitchSimulator` from compiling. The default public target does
not import this backend.

## Concrete backend dependency flow

```text
MachineModel ──► TMCombinators ──► Tape.Alphabet
       │                               │
       └──► ConcreteEncoding ──────────┘
                                       ▼
                                 Tape.Actions
                                       ▼
                             Tape.BasicOperations
                                       ▼
                          Tape.BinaryArithmetic
                                       ▼
                              Tape.Comparison
                                       ▼
                                RegisterTape.*
                                       ▼
                                 Simulator.*
```

The abstract acceptance and register-machine modules also feed into
`ConcreteEncoding`, `RegisterTape.Layout`, and `Simulator.Core`. Within each
folder, the imports follow the implementation order: foundational data and
invariants first, followed by operations and their higher-level compositions.

## Import conventions

- Import the narrowest module that provides the definitions needed by new work.
- Keep the old flat entry points (`SavitchLemma.TapePrimitives`,
  `SavitchLemma.RegisterTapeOps`, and `SavitchLemma.SavitchSimulator`) as
  facades so existing imports remain valid.
- Add new operations to the focused module that owns their invariant; add a new
  file when a module grows beyond one coherent proof/implementation unit.
- Avoid importing the concrete backend from `SavitchLemma.lean` unless the
  public abstract API is intentionally being expanded.

## Validation

Use the pinned Lean toolchain and run `lake build` from the repository root to
check the default abstract target. Check the concrete layers explicitly with
`lake build SavitchLemma.TapePrimitives SavitchLemma.RegisterTapeOps`; the full
simulator target is still blocked by `Simulator.StepChecker`. Compile an
individual module with `lake env lean path/to/Module.lean` when iterating on one
file.

module

public import SavitchLemma.Model.MachineDefinitions
public import SavitchLemma.MainTheorem
public import SavitchLemma.Examples.SanityCheck

@[expose] public section

/-!
# Savitch's theorem in Lean 4

Public entry point for external review and downstream users:
- `SavitchLemma.Model.MachineDefinitions`: isolated, proof-free definitions of
  multitape NTM/DTM, one-sided space-bounded acceptance, and measurability.
- `SavitchLemma.MainTheorem`: `savitch_theorem_one`,
  `savitch_theorem_one_measurable`, `savitch_theorem_one_of_measurable`, and
  `savitch_theorem_one_full`.
- `SavitchLemma.Examples.SanityCheck`: non-vacuity check instantiating
  `savitch_theorem_one_full` on a concrete 2-state NTM.

All internal proof layers (`SavitchLemma.Abstract`, `SavitchLemma.Model`,
`SavitchLemma.Tape`, `SavitchLemma.RegisterTape`, `SavitchLemma.Simulator`,
`SavitchLemma.SpaceBounds`) are built transitively via `MainTheorem`.
-/

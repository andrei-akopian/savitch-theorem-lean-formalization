import Lake
open Lake DSL

package SavitchLemma where
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`linter.unusedVariables, true⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.35.0"

@[default_target]
lean_lib SavitchLemma where

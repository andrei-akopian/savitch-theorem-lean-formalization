module

public import SavitchLemma.Abstract.SavitchAlgorithm

@[expose] public section

/-!
# Register-update facts

This module exposes the pointwise behavior of `updateAndReset`, which is used
by both D2 and D3.
-/

namespace SavitchLemma

/-- The selected register receives exactly the supplied value and tag. -/
theorem updateAndReset_at_current (hN : 1 < N) (cfg : ZDConfig r N) (j : Fin r)
    (value : Fin (N + 1)) (newTag : Bool) :
    (updateAndReset hN cfg j value newTag).x j.castSucc = value ∧
      (updateAndReset hN cfg j value newTag).tag j.castSucc = newTag := by
  simp [updateAndReset]

/-- Registers strictly left of the selected index are reset to the first code
and untagged. -/
theorem updateAndReset_at_before (hN : 1 < N) (cfg : ZDConfig r N) (j : Fin r)
    (value : Fin (N + 1)) (newTag : Bool) (i : Fin (r + 1))
    (hij : i.val < j.val) :
    (updateAndReset hN cfg j value newTag).x i = firstCode N hN ∧
      (updateAndReset hN cfg j value newTag).tag i = false := by
  have hne : i.val ≠ j.val := Nat.ne_of_lt hij
  simp [updateAndReset, hne, hij]

/-- Registers strictly right of the selected index retain their values and
tags. -/
theorem updateAndReset_at_after (hN : 1 < N) (cfg : ZDConfig r N) (j : Fin r)
    (value : Fin (N + 1)) (newTag : Bool) (i : Fin (r + 1))
    (hij : j.val < i.val) :
    (updateAndReset hN cfg j value newTag).x i = cfg.x i ∧
      (updateAndReset hN cfg j value newTag).tag i = cfg.tag i := by
  have hne : i.val ≠ j.val := Nat.ne_of_gt hij
  have hnlt : ¬ i.val < j.val := Nat.not_lt_of_ge (Nat.le_of_lt hij)
  simp [updateAndReset, hne, hnlt]

end SavitchLemma

module

public import SavitchLemma.Abstract.SavitchAlgorithm

@[expose] public section

/-!
# Basic reachability facts for abstract IDs

The endpoints 0 and N are reserved codes.  This module turns those model
assumptions into path facts used by the register-progress argument.
-/

namespace SavitchLemma

/-- No path from a valid source can end at the reserved maximum code. -/
theorem no_reaches_max (P : AbstractProblem N) (source : ValidCode N) :
    ¬ Relation.ReflTransGen P.step source.val (maxCode N) := by
  intro hReach
  rcases Relation.ReflTransGen.cases_tail hReach with hEq | ⟨prev, _, hEdge⟩
  · have hValues := congrArg Fin.val hEq
    have hSource : source.val.val = N := hValues.symm
    have hBound := source.property.2
    rw [hSource] at hBound
    exact Nat.lt_irrefl N hBound
  · exact P.noStepToMax prev hEdge

/-- No path from a valid source can end at the reserved zero code. -/
theorem no_reaches_zero (P : AbstractProblem N) (source : ValidCode N) :
    ¬ Relation.ReflTransGen P.step source.val ⟨0, Nat.zero_lt_succ N⟩ := by
  intro hReach
  rcases Relation.ReflTransGen.cases_tail hReach with hEq | ⟨prev, _, hEdge⟩
  · have hValues := congrArg Fin.val hEq
    have hSource : 0 = source.val.val := hValues
    have hPositive := source.property.1
    rw [← hSource] at hPositive
    exact Nat.lt_irrefl 0 hPositive
  · exact P.noStepToZero prev hEdge

/-- Every tagged register contains a code other than the reserved maximum. -/
theorem tagged_value_ne_max (P : AbstractProblem N) (source : ValidCode N)
    (cfg : ZDConfig r N) (hSound : TagsSound P source.val cfg) (i : Fin (r + 1))
    (hi : cfg.tag i = true) : cfg.x i ≠ maxCode N := by
  intro hEq
  have hReach := hSound i hi
  rw [hEq] at hReach
  exact no_reaches_max P source hReach

/-- Every tagged register contains a code other than the reserved zero. -/
theorem tagged_value_ne_zero (P : AbstractProblem N) (source : ValidCode N)
    (cfg : ZDConfig r N) (hSound : TagsSound P source.val cfg) (i : Fin (r + 1))
    (hi : cfg.tag i = true) : cfg.x i ≠ ⟨0, Nat.zero_lt_succ N⟩ := by
  intro hEq
  have hReach := hSound i hi
  rw [hEq] at hReach
  exact no_reaches_zero P source hReach

/-- The D1 test cannot succeed when its target is the reserved maximum code. -/
theorem no_tagged_test_to_max (P : AbstractProblem N) (source : ValidCode N)
    (cfg : ZDConfig r N) (hSound : TagsSound P source.val cfg) :
    ¬ ∃ i : Fin (r + 1), cfg.tag i = true ∧
      (cfg.x i = maxCode N ∨ P.step (cfg.x i) (maxCode N)) := by
  rintro ⟨i, hi, hTest⟩
  rcases hTest with hEq | hEdge
  · exact tagged_value_ne_max P source cfg hSound i hi hEq
  · exact P.noStepToMax (cfg.x i) hEdge

end SavitchLemma

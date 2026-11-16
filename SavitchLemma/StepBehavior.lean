module

public import SavitchLemma.ConfigUpdates
public import SavitchLemma.Reachability
public import SavitchLemma.Selection

@[expose] public section

/-!
# One-step behavior of the register machine

These lemmas expose the control-flow cases and the exact D3 update.  They are
the local transition facts used by the register-progress induction.
-/

namespace SavitchLemma

/-- If every working register is tagged, D1 sends control to D3. -/
theorem zdStep_of_all_tagged (P : AbstractProblem N) (hN : 1 < N)
    (cfg : ZDConfig r N) (hNone : firstUntagged cfg = none) :
    zdStep P hN cfg = zdBacktrack hN cfg := by
  classical
  simp [zdStep, hNone]

/-- When D1 finds a successful tagged predecessor, the next configuration is
the D2 update at the selected register. -/
theorem zdStep_of_successful_test (P : AbstractProblem N) (hN : 1 < N)
    (cfg : ZDConfig r N) (j : Fin r) (hFind : firstUntagged cfg = some j)
    (hTest : ∃ i : Fin (r + 1), cfg.tag i = true ∧
      (cfg.x i = cfg.x j.castSucc ∨ P.step (cfg.x i) (cfg.x j.castSucc))) :
    zdStep P hN cfg = some (updateAndReset hN cfg j (cfg.x j.castSucc) true) := by
  classical
  simp [zdStep, hFind, hTest]

/-- A tag-sound computation cannot D2-tag the reserved maximum code. -/
theorem zdStep_backtracks_at_max (P : AbstractProblem N) (hN : 1 < N)
    (source : ValidCode N) (cfg : ZDConfig r N) (j : Fin r)
    (hSound : TagsSound P source.val cfg) (hFind : firstUntagged cfg = some j)
    (hMax : cfg.x j.castSucc = maxCode N) :
    zdStep P hN cfg = zdBacktrack hN cfg := by
  classical
  have hTest : ¬ ∃ i : Fin (r + 1), cfg.tag i = true ∧
      (cfg.x i = cfg.x j.castSucc ∨ P.step (cfg.x i) (cfg.x j.castSucc)) := by
    simpa [hMax] using no_tagged_test_to_max P source cfg hSound
  simp [zdStep, hFind, hTest]

/-- Exact shape of a successful D3 pass: the least register below the maximum
is incremented, its tag is cleared, and the lower prefix is reset. -/
theorem zdBacktrack_eq_some_iff (hN : 1 < N) (cfg next : ZDConfig r N) :
    zdBacktrack hN cfg = some next ↔
      ∃ j : Fin r, firstBelowMax cfg = some j ∧
        ∃ hLt : (cfg.x j.castSucc).val < N,
          next = updateAndReset hN cfg j
            ⟨(cfg.x j.castSucc).val + 1, Nat.succ_lt_succ hLt⟩ false := by
  constructor
  · intro hNext
    unfold zdBacktrack at hNext
    cases hFind : firstBelowMax cfg with
    | none => simp [hFind] at hNext
    | some j =>
      by_cases hLt : (cfg.x j.castSucc).val < N
      · have hSome :
            some (updateAndReset hN cfg j
              ⟨(cfg.x j.castSucc).val + 1, Nat.succ_lt_succ hLt⟩ false) = some next := by
          simpa [hFind, hLt] using hNext
        exact ⟨j, rfl, hLt, (Option.some.inj hSome).symm⟩
      · simp [hFind, hLt] at hNext
  · rintro ⟨j, hFind, hLt, hEq⟩
    subst next
    simp [zdBacktrack, hFind, hLt]

/-- D3 increments the least nonmaximum register; every lower register is at
the maximum immediately before the update. -/
theorem zdBacktrack_selected_shape (hN : 1 < N) (cfg next : ZDConfig r N)
    (hBack : zdBacktrack hN cfg = some next) :
    ∃ j : Fin r, firstBelowMax cfg = some j ∧
      (∀ i : Fin r, i < j → cfg.x i.castSucc = maxCode N) ∧
      ∃ hLt : (cfg.x j.castSucc).val < N,
        next = updateAndReset hN cfg j
          ⟨(cfg.x j.castSucc).val + 1, Nat.succ_lt_succ hLt⟩ false := by
  rcases (zdBacktrack_eq_some_iff hN cfg next).mp hBack with
    ⟨j, hFind, hLt, hEq⟩
  exact ⟨j, hFind, firstBelowMax_prefix_max cfg j hFind, hLt, hEq⟩

end SavitchLemma

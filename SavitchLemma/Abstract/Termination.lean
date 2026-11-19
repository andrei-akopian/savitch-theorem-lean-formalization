module

public import Mathlib.Data.DFinsupp.WellFounded
public import Mathlib.Order.PiLex
import Mathlib.Tactic.Positivity
public import SavitchLemma.Abstract.StepBehavior

@[expose] public section

/-!
# A well-founded measure for the register machine

Each working register contributes its value together with its tag bit.  The
colexicographic order makes larger register indices more significant, matching
the carry/reset behavior of D2 and D3.
-/

namespace SavitchLemma

variable {r N : ℕ}

/-- The natural-valued digit associated to a working register. -/
def zdDigit (cfg : ZDConfig r N) (i : Fin r) : ℕ :=
  2 * (cfg.x i.castSucc).val + if cfg.tag i.castSucc then 1 else 0

/-- Remaining capacity in one register digit. -/
def zdCostDigit (cfg : ZDConfig r N) (i : Fin r) : ℕ :=
  2 * N + 1 - zdDigit cfg i

/-- The remaining counter capacity, ordered colexicographically. -/
def zdMeasure (cfg : ZDConfig r N) : Colex (Fin r → ℕ) :=
  toColex (zdCostDigit cfg)

/-- Colexicographic order on a finite tuple of natural numbers is well-founded. -/
theorem zdMeasure_wellFounded (r : ℕ) :
    WellFounded (fun a b : Colex (Fin r → ℕ) => a < b) := by
  infer_instance

/-- Every register digit is bounded by its maximum value. -/
theorem zdDigit_le (cfg : ZDConfig r N) (i : Fin r) : zdDigit cfg i ≤ 2 * N + 1 := by
  have hValue : (cfg.x i.castSucc).val ≤ N :=
    Nat.le_of_lt_succ (cfg.x i.castSucc).isLt
  unfold zdDigit
  cases hTag : cfg.tag i.castSucc
  · simp
    omega
  · simp
    omega

/-- Increasing a digit strictly decreases its remaining capacity. -/
theorem zdCostDigit_lt_of_digit_lt (cfg₁ cfg₂ : ZDConfig r N) (i : Fin r)
    (hDigit : zdDigit cfg₁ i < zdDigit cfg₂ i) :
    zdCostDigit cfg₂ i < zdCostDigit cfg₁ i := by
  have h₁ := zdDigit_le cfg₁ i
  have h₂ := zdDigit_le cfg₂ i
  unfold zdCostDigit
  omega

/-- Updating a register leaves all more significant (higher-indexed) digits
unchanged. -/
theorem zdDigit_updateAndReset_at_after (hN : 1 < N) (cfg : ZDConfig r N)
    (j k : Fin r) (value : Fin (N + 1)) (newTag : Bool) (hjk : j < k) :
    zdDigit (updateAndReset hN cfg j value newTag) k = zdDigit cfg k := by
  have hValues : j.val < k.val := by simpa using hjk
  obtain ⟨hX, hTag⟩ := updateAndReset_at_after hN cfg j value newTag k.castSucc hValues
  simp [zdDigit, hX, hTag]

/-- Updating a register leaves every higher-indexed cost digit unchanged. -/
theorem zdCostDigit_updateAndReset_at_after (hN : 1 < N) (cfg : ZDConfig r N)
    (j k : Fin r) (value : Fin (N + 1)) (newTag : Bool) (hjk : j < k) :
    zdCostDigit (updateAndReset hN cfg j value newTag) k = zdCostDigit cfg k := by
  simp [zdCostDigit, zdDigit_updateAndReset_at_after hN cfg j k value newTag hjk]

/-- If the cost at `j` decreases and higher-indexed costs are unchanged, the
whole register tuple decreases in colexicographic order. -/
theorem zdMeasure_updateAndReset_lt (hN : 1 < N) (cfg : ZDConfig r N)
    (j : Fin r) (value : Fin (N + 1)) (newTag : Bool)
    (hCost : zdCostDigit (updateAndReset hN cfg j value newTag) j < zdCostDigit cfg j) :
    zdMeasure (updateAndReset hN cfg j value newTag) < zdMeasure cfg := by
  change Pi.Lex (· > ·) (· < ·) (zdCostDigit (updateAndReset hN cfg j value newTag))
    (zdCostDigit cfg)
  refine ⟨j, ?_, hCost⟩
  intro k hjk
  exact zdCostDigit_updateAndReset_at_after hN cfg j k value newTag hjk

/-- Every successful D3 pass strictly decreases the colexicographic measure. -/
theorem zdBacktrack_decreases_measure (hN : 1 < N) (cfg next : ZDConfig r N)
    (hBack : zdBacktrack hN cfg = some next) : zdMeasure next < zdMeasure cfg := by
  rcases (zdBacktrack_eq_some_iff hN cfg next).mp hBack with
    ⟨j, hFind, hLt, hEq⟩
  subst next
  apply zdMeasure_updateAndReset_lt hN cfg j _ false
  apply zdCostDigit_lt_of_digit_lt cfg _ j
  cases hTag : cfg.tag j.castSucc
  · simp [zdDigit, updateAndReset, hTag]
  · simp [zdDigit, updateAndReset, hTag]
    omega

/-- Every step of the modified register machine strictly decreases the
well-founded measure. -/
theorem zdStep_decreases_measure (P : AbstractProblem N) (hN : 1 < N)
    (cfg next : ZDConfig r N) (hStep : zdStep P hN cfg = some next) :
    zdMeasure next < zdMeasure cfg := by
  classical
  unfold zdStep at hStep
  cases hFind : firstUntagged cfg with
  | none =>
    apply zdBacktrack_decreases_measure hN cfg next
    simpa [hFind] using hStep
  | some j =>
    by_cases hTest : ∃ i : Fin (r + 1), cfg.tag i = true ∧
        (cfg.x i = cfg.x j.castSucc ∨ P.step (cfg.x i) (cfg.x j.castSucc))
    · have hEq : updateAndReset hN cfg j (cfg.x j.castSucc) true = next :=
        Option.some.inj (by simpa [hFind, hTest] using hStep)
      subst next
      apply zdMeasure_updateAndReset_lt hN cfg j (cfg.x j.castSucc) true
      apply zdCostDigit_lt_of_digit_lt cfg _ j
      have hUntagged := (firstUntagged_eq_some_iff cfg j).mp hFind |>.1
      simp [zdDigit, updateAndReset, hUntagged]
    · apply zdBacktrack_decreases_measure hN cfg next
      simpa [hFind, hTest] using hStep

/-- The backward view of a machine step, used for well-founded recursion. -/
noncomputable def zdStepBackRel (P : AbstractProblem N) (hN : 1 < N) (r : ℕ)
    (next current : ZDConfig r N) : Prop :=
  zdStep P hN current = some next

/-- Every predecessor step decreases the remaining-capacity measure. -/
theorem zdStepBackRel_wellFounded (P : AbstractProblem N) (hN : 1 < N) (r : ℕ) :
    WellFounded (zdStepBackRel P hN r) := by
  refine Subrelation.wf ?_ (InvImage.wf zdMeasure (zdMeasure_wellFounded r))
  intro next current hStep
  exact zdStep_decreases_measure P hN current next hStep

/-- Every execution reaches a configuration with no successor in finitely many
steps. -/
theorem zdStep_reaches_stuck (P : AbstractProblem N) (hN : 1 < N)
    (r : ℕ) (cfg : ZDConfig r N) :
    ∃ final, Relation.ReflTransGen (fun a b : ZDConfig r N => zdStep P hN a = some b)
      cfg final ∧ zdStep P hN final = none := by
  apply (zdStepBackRel_wellFounded P hN r).induction cfg
  intro current ih
  cases hStep : zdStep P hN current with
  | none => exact ⟨current, Relation.ReflTransGen.refl, hStep⟩
  | some next =>
    obtain ⟨final, hRun, hStop⟩ := ih next hStep
    have hFirst :
        Relation.ReflTransGen (fun a b : ZDConfig r N => zdStep P hN a = some b)
          current next :=
      Relation.ReflTransGen.tail Relation.ReflTransGen.refl hStep
    exact ⟨final, hFirst.trans hRun, hStop⟩

/-- A configuration with a working register below `N` always has a successor:
D1 either performs D2 or D3 can increment a register. -/
theorem zdStep_ne_none_of_below_max (P : AbstractProblem N) (hN : 1 < N)
    (cfg : ZDConfig r N) (i : Fin r)
    (hBelow : (cfg.x i.castSucc).val < N) : zdStep P hN cfg ≠ none := by
  classical
  have hFindNe : firstBelowMax cfg ≠ none := by
    intro hNone
    have hAll := (firstBelowMax_eq_none_iff cfg).mp hNone
    exact hAll i hBelow
  have hBack : ∃ next, zdBacktrack hN cfg = some next := by
    cases hFind : firstBelowMax cfg with
    | none => exact (hFindNe hFind).elim
    | some j =>
      have hLt := (firstBelowMax_eq_some_iff cfg j).mp hFind |>.1
      refine ⟨updateAndReset hN cfg j
        ⟨(cfg.x j.castSucc).val + 1, Nat.succ_lt_succ hLt⟩ false, ?_⟩
      simp [zdBacktrack, hFind, hLt]
  intro hStop
  unfold zdStep at hStop
  cases hFind : firstUntagged cfg with
  | none =>
    rcases hBack with ⟨next, hNext⟩
    simp [hFind, hNext] at hStop
  | some j =>
    by_cases hTest : ∃ i : Fin (r + 1), cfg.tag i = true ∧
        (cfg.x i = cfg.x j.castSucc ∨ P.step (cfg.x i) (cfg.x j.castSucc))
    · simp [hFind, hTest] at hStop
    · rcases hBack with ⟨next, hNext⟩
      simp [hFind, hTest, hNext] at hStop

/-- If the machine is stuck, every working register has reached the maximum
code. -/
theorem zdStep_none_forces_max (P : AbstractProblem N) (hN : 1 < N)
    (cfg : ZDConfig r N) (hStop : zdStep P hN cfg = none) :
    ∀ i : Fin r, cfg.x i.castSucc = maxCode N := by
  intro i
  by_contra hNotMax
  have hValueNe : (cfg.x i.castSucc).val ≠ N := by
    intro hValue
    apply hNotMax
    apply Fin.ext
    simpa [maxCode] using hValue
  have hBelow : (cfg.x i.castSucc).val < N := by
    have hBound := (cfg.x i.castSucc).isLt
    omega
  exact (zdStep_ne_none_of_below_max P hN cfg i hBelow) hStop

end SavitchLemma

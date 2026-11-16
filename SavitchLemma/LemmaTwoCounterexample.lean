module

public import SavitchLemma.BoundedReachability
public import SavitchLemma.LemmaOne
public import SavitchLemma.StepBehavior

import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Positivity

@[expose] public section

/-!
# A finite counterexample to the printed local Lemma 2 statement

For maximum code `5`, the tagged source `1` reaches `3` in two edges, but the
register machine cannot tag `3` from the configuration with working registers
`3, 4`.  The theorem below certifies the finite run and its terminal state.
-/

namespace SavitchLemma.LemmaTwoCounterexample

def code1 : Fin 6 := ⟨1, by decide⟩
def code2 : Fin 6 := ⟨2, by decide⟩
def code3 : Fin 6 := ⟨3, by decide⟩
def code4 : Fin 6 := ⟨4, by decide⟩
def code5 : Fin 6 := ⟨5, by decide⟩

def problem : AbstractProblem 5 where
  step a b := (a.val = 1 ∧ b.val = 2) ∨ (a.val = 2 ∧ b.val = 3)
  noStepToZero := by
    intro a h
    change (a.val = 1 ∧ 0 = 2) ∨ (a.val = 2 ∧ 0 = 3) at h
    rcases h with ⟨_, h⟩ | ⟨_, h⟩ <;> omega
  noStepToMax := by
    intro a h
    change (a.val = 1 ∧ 5 = 2) ∨ (a.val = 2 ∧ 5 = 3) at h
    rcases h with ⟨_, h⟩ | ⟨_, h⟩ <;> omega

theorem hN : 1 < 5 := by decide
def i0 : Fin 2 := ⟨0, by decide⟩
def i1 : Fin 2 := ⟨1, by decide⟩
def src : ValidCode 5 := ⟨code1, by constructor <;> decide⟩

/-- The configuration in printed Lemma 2 with `j = 1`, target `3`,
remaining register `4`, and tagged source `1`. -/
def start : ZDConfig 2 5 where
  x := fun i => if i.val = 0 then code3 else if i.val = 1 then code4 else code1
  tag := fun i => decide (i.val = 2)

def s1 : ZDConfig 2 5 := updateAndReset hN start i0 code4 false
def s2 : ZDConfig 2 5 := updateAndReset hN s1 i0 code5 false
def s3 : ZDConfig 2 5 := updateAndReset hN s2 i1 code5 false
def s4 : ZDConfig 2 5 := updateAndReset hN s3 i0 code1 true
def s5 : ZDConfig 2 5 := updateAndReset hN s4 i0 code2 false
def s6 : ZDConfig 2 5 := updateAndReset hN s5 i0 code2 true
def s7 : ZDConfig 2 5 := updateAndReset hN s6 i0 code3 false
def s8 : ZDConfig 2 5 := updateAndReset hN s7 i0 code4 false
def s9 : ZDConfig 2 5 := updateAndReset hN s8 i0 code5 false

private theorem find0 (cfg : ZDConfig 2 5) (hTag : cfg.tag i0.castSucc = false) :
    firstUntagged cfg = some i0 := by
  apply (firstUntagged_eq_some_iff cfg i0).2
  refine ⟨hTag, ?_⟩
  intro i hi
  fin_cases i <;> simp [i0] at hi

private theorem find1 (cfg : ZDConfig 2 5)
    (hTag0 : cfg.tag i0.castSucc = true) (hTag1 : cfg.tag i1.castSucc = false) :
    firstUntagged cfg = some i1 := by
  apply (firstUntagged_eq_some_iff cfg i1).2
  refine ⟨hTag1, ?_⟩
  intro i hi
  fin_cases i
  · exact hTag0
  · simp [i1] at hi

private theorem below0 (cfg : ZDConfig 2 5) (hX : (cfg.x i0.castSucc).val < 5) :
    firstBelowMax cfg = some i0 := by
  apply (firstBelowMax_eq_some_iff cfg i0).2
  refine ⟨hX, ?_⟩
  intro i hi
  fin_cases i <;> simp [i0] at hi

private theorem below1 (cfg : ZDConfig 2 5)
    (hX0 : ¬ (cfg.x i0.castSucc).val < 5) (hX1 : (cfg.x i1.castSucc).val < 5) :
    firstBelowMax cfg = some i1 := by
  apply (firstBelowMax_eq_some_iff cfg i1).2
  refine ⟨hX1, ?_⟩
  intro i hi
  fin_cases i
  · exact hX0
  · simp [i1] at hi

private theorem belowNone (cfg : ZDConfig 2 5)
    (hX0 : ¬ (cfg.x i0.castSucc).val < 5) (hX1 : ¬ (cfg.x i1.castSucc).val < 5) :
    firstBelowMax cfg = none := by
  apply (firstBelowMax_eq_none_iff cfg).2
  intro i
  fin_cases i
  · exact hX0
  · exact hX1

private theorem failed_step (cfg : ZDConfig 2 5) (target backtrack : Fin 2)
    (hFind : firstUntagged cfg = some target)
    (hFail : ¬ ∃ i : Fin 3, cfg.tag i = true ∧
      (cfg.x i = cfg.x target.castSucc ∨ problem.step (cfg.x i) (cfg.x target.castSucc)))
    (hBelow : firstBelowMax cfg = some backtrack)
    (hLt : (cfg.x backtrack.castSucc).val < 5) :
    zdStep problem hN cfg =
      some (updateAndReset hN cfg backtrack
        ⟨(cfg.x backtrack.castSucc).val + 1, Nat.succ_lt_succ hLt⟩ false) := by
  rw [zdStep_backtracks_when_test_fails problem hN cfg target hFind hFail]
  exact (zdBacktrack_eq_some_iff hN cfg _).2 ⟨backtrack, hBelow, hLt, rfl⟩

private theorem successful_step (cfg : ZDConfig 2 5) (j : Fin 2)
    (hFind : firstUntagged cfg = some j)
    (hTest : ∃ i : Fin 3, cfg.tag i = true ∧
      (cfg.x i = cfg.x j.castSucc ∨ problem.step (cfg.x i) (cfg.x j.castSucc))) :
    zdStep problem hN cfg = some (updateAndReset hN cfg j (cfg.x j.castSucc) true) :=
  zdStep_of_successful_test problem hN cfg j hFind hTest

private theorem start_find : firstUntagged start = some i0 := by
  apply find0
  simp [start, i0]

private theorem start_fail : ¬ ∃ i : Fin 3, start.tag i = true ∧
    (start.x i = start.x i0.castSucc ∨ problem.step (start.x i) (start.x i0.castSucc)) := by
  rintro ⟨i, hi, htest⟩
  fin_cases i <;> simp [start, i0, problem, code1, code3] at hi htest

private theorem start_below : firstBelowMax start = some i0 := by
  apply below0
  simp [start, i0, code3]

private theorem step_start : zdStep problem hN start = some s1 := by
  have h := failed_step start i0 i0 start_find start_fail start_below (by decide)
  simpa [s1, start, i0, code3, code4, updateAndReset] using h

private theorem s1_find : firstUntagged s1 = some i0 := by
  apply find0
  simp [s1, start, i0, code1, code3, code4, updateAndReset]

private theorem s1_fail : ¬ ∃ i : Fin 3, s1.tag i = true ∧
    (s1.x i = s1.x i0.castSucc ∨ problem.step (s1.x i) (s1.x i0.castSucc)) := by
  rintro ⟨i, hi, htest⟩
  fin_cases i <;> simp [s1, start, i0, problem, code1, code3, code4,
    updateAndReset] at hi htest

private theorem s1_below : firstBelowMax s1 = some i0 := by
  apply below0
  simp [s1, start, i0, code3, code4, updateAndReset]

private theorem step_s1 : zdStep problem hN s1 = some s2 := by
  have h := failed_step s1 i0 i0 s1_find s1_fail s1_below (by decide)
  simpa [s2, s1, start, i0, code1, code3, code4, code5, updateAndReset] using h

private theorem s2_find : firstUntagged s2 = some i0 := by
  apply find0
  simp [s2, s1, start, i0, code1, code3, code4, code5, updateAndReset]

private theorem s2_fail : ¬ ∃ i : Fin 3, s2.tag i = true ∧
    (s2.x i = s2.x i0.castSucc ∨ problem.step (s2.x i) (s2.x i0.castSucc)) := by
  rintro ⟨i, hi, htest⟩
  fin_cases i <;> simp [s2, s1, start, i0, problem, code1, code3, code4, code5,
    updateAndReset]
    at hi htest

private theorem s2_below : firstBelowMax s2 = some i1 := by
  apply below1
  · simp [s2, s1, start, i0, code3, code4, code5, updateAndReset]
  · simp [s2, s1, start, i0, i1, code3, code4, code5, updateAndReset]

private theorem step_s2 : zdStep problem hN s2 = some s3 := by
  have h := failed_step s2 i0 i1 s2_find s2_fail s2_below (by decide)
  -- D3 carries from register 1 to register 2 and resets register 1.
  simpa [s3, s2, s1, start, i0, i1, code1, code3, code4, code5,
    updateAndReset] using h

private theorem s3_find : firstUntagged s3 = some i0 := by
  apply find0
  simp [s3, s2, s1, start, i0, i1, code1, code3, code4, code5, updateAndReset]

private theorem s3_test : ∃ i : Fin 3, s3.tag i = true ∧
    (s3.x i = s3.x i0.castSucc ∨ problem.step (s3.x i) (s3.x i0.castSucc)) := by
  refine ⟨Fin.last 2, ?_, Or.inl ?_⟩
  · simp [s3, s2, s1, start, i0, i1, code1, code3, code4, code5,
      firstCode, updateAndReset]
  · simp [s3, s2, s1, start, i0, i1, code1, code3, code4, code5,
      firstCode, updateAndReset]

private theorem step_s3 : zdStep problem hN s3 = some s4 := by
  have h := successful_step s3 i0 s3_find s3_test
  simpa [s4, s3, s2, s1, start, i0, i1, code1, code2, code3, code4, code5,
    firstCode, updateAndReset] using h

private theorem s4_find : firstUntagged s4 = some i1 := by
  apply find1
  · simp [s4, s3, s2, s1, start, i0, i1, code1, code3, code4, code5,
      updateAndReset]
  · simp [s4, s3, s2, s1, start, i0, i1, code1, code3, code4, code5,
      updateAndReset]

private theorem s4_fail : ¬ ∃ i : Fin 3, s4.tag i = true ∧
    (s4.x i = s4.x i1.castSucc ∨ problem.step (s4.x i) (s4.x i1.castSucc)) := by
  rintro ⟨i, hi, htest⟩
  fin_cases i <;> simp [s4, s3, s2, s1, start, i0, i1, problem,
    code1, code3, code4, code5, updateAndReset] at hi htest

private theorem s4_below : firstBelowMax s4 = some i0 := by
  apply below0
  simp [s4, s3, s2, s1, start, i0, i1, code1, code3, code4, code5,
    updateAndReset]

private theorem step_s4 : zdStep problem hN s4 = some s5 := by
  have h := failed_step s4 i1 i0 s4_find s4_fail s4_below (by decide)
  simpa [s5, s4, s3, s2, s1, start, i0, i1,
    code1, code2, code3, code4, code5, updateAndReset] using h

private theorem s5_find : firstUntagged s5 = some i0 := by
  apply find0
  simp [s5, s4, s3, s2, s1, start, i0, i1,
    code1, code2, code3, code4, code5, updateAndReset]

private theorem s5_test : ∃ i : Fin 3, s5.tag i = true ∧
    (s5.x i = s5.x i0.castSucc ∨ problem.step (s5.x i) (s5.x i0.castSucc)) := by
  refine ⟨Fin.last 2, ?_, Or.inr ?_⟩
  · simp [s5, s4, s3, s2, s1, start, i0, i1,
      code1, code2, code3, code4, code5, updateAndReset]
  · simp [problem, s5, s4, s3, s2, s1, start, i0, i1,
      code1, code2, code3, code4, code5, updateAndReset]

private theorem step_s5 : zdStep problem hN s5 = some s6 := by
  have h := successful_step s5 i0 s5_find s5_test
  simpa [s6, s5, s4, s3, s2, s1, start, i0, i1,
    code1, code2, code3, code4, code5, updateAndReset] using h

private theorem s6_find : firstUntagged s6 = some i1 := by
  apply find1
  · simp [s6, s5, s4, s3, s2, s1, start, i0, i1,
      code1, code2, code3, code4, code5, updateAndReset]
  · simp [s6, s5, s4, s3, s2, s1, start, i0, i1,
      code1, code2, code3, code4, code5, updateAndReset]

private theorem s6_fail : ¬ ∃ i : Fin 3, s6.tag i = true ∧
    (s6.x i = s6.x i1.castSucc ∨ problem.step (s6.x i) (s6.x i1.castSucc)) := by
  rintro ⟨i, hi, htest⟩
  fin_cases i <;> simp [s6, s5, s4, s3, s2, s1, start, i0, i1,
    problem, code1, code2, code3, code4, code5, updateAndReset] at hi htest

private theorem s6_below : firstBelowMax s6 = some i0 := by
  apply below0
  simp [s6, s5, s4, s3, s2, s1, start, i0, i1,
    code1, code2, code3, code4, code5, updateAndReset]

private theorem step_s6 : zdStep problem hN s6 = some s7 := by
  have h := failed_step s6 i1 i0 s6_find s6_fail s6_below (by decide)
  simpa [s7, s6, s5, s4, s3, s2, s1, start, i0, i1,
    code1, code2, code3, code4, code5, updateAndReset] using h

private theorem s7_find : firstUntagged s7 = some i0 := by
  apply find0
  simp [s7, s6, s5, s4, s3, s2, s1, start, i0, i1,
    code1, code2, code3, code4, code5, updateAndReset]

private theorem s7_fail : ¬ ∃ i : Fin 3, s7.tag i = true ∧
    (s7.x i = s7.x i0.castSucc ∨ problem.step (s7.x i) (s7.x i0.castSucc)) := by
  rintro ⟨i, hi, htest⟩
  fin_cases i <;> simp [s7, s6, s5, s4, s3, s2, s1, start, i0, i1,
    problem, code1, code2, code3, code4, code5, updateAndReset] at hi htest

private theorem s7_below : firstBelowMax s7 = some i0 := by
  apply below0
  simp [s7, s6, s5, s4, s3, s2, s1, start, i0, i1,
    code1, code2, code3, code4, code5, updateAndReset]

private theorem step_s7 : zdStep problem hN s7 = some s8 := by
  have h := failed_step s7 i0 i0 s7_find s7_fail s7_below (by decide)
  simpa [s8, s7, s6, s5, s4, s3, s2, s1, start, i0, i1,
    code1, code2, code3, code4, code5, updateAndReset] using h

private theorem s8_find : firstUntagged s8 = some i0 := by
  apply find0
  simp [s8, s7, s6, s5, s4, s3, s2, s1, start, i0, i1,
    code1, code2, code3, code4, code5, updateAndReset]

private theorem s8_fail : ¬ ∃ i : Fin 3, s8.tag i = true ∧
    (s8.x i = s8.x i0.castSucc ∨ problem.step (s8.x i) (s8.x i0.castSucc)) := by
  rintro ⟨i, hi, htest⟩
  fin_cases i <;> simp [s8, s7, s6, s5, s4, s3, s2, s1, start, i0, i1,
    problem, code1, code2, code3, code4, code5, updateAndReset] at hi htest

private theorem s8_below : firstBelowMax s8 = some i0 := by
  apply below0
  simp [s8, s7, s6, s5, s4, s3, s2, s1, start, i0, i1,
    code1, code2, code3, code4, code5, updateAndReset]

private theorem step_s8 : zdStep problem hN s8 = some s9 := by
  have h := failed_step s8 i0 i0 s8_find s8_fail s8_below (by decide)
  simpa [s9, s8, s7, s6, s5, s4, s3, s2, s1, start, i0, i1,
    code1, code2, code3, code4, code5, updateAndReset] using h

private theorem s9_find : firstUntagged s9 = some i0 := by
  apply find0
  simp [s9, s8, s7, s6, s5, s4, s3, s2, s1,
    start, i0, i1, code1, code2, code3, code4, code5, updateAndReset]

private theorem s9_fail : ¬ ∃ i : Fin 3, s9.tag i = true ∧
    (s9.x i = s9.x i0.castSucc ∨ problem.step (s9.x i) (s9.x i0.castSucc)) := by
  rintro ⟨i, hi, htest⟩
  fin_cases i <;> simp [s9, s8, s7, s6, s5, s4, s3, s2, s1,
    start, i0, i1, problem, code1, code2, code3, code4, code5,
    updateAndReset] at hi htest

private theorem s9_all_max : firstBelowMax s9 = none := by
  apply belowNone
  · simp [s9, s8, s7, s6, s5, s4, s3, s2, s1,
      start, i0, i1, code1, code2, code3, code4, code5, updateAndReset]
  · simp [s9, s8, s7, s6, s5, s4, s3, s2, s1,
      start, i0, i1, code1, code2, code3, code4, code5, updateAndReset]

private theorem step_s9 : zdStep problem hN s9 = none := by
  rw [zdStep_backtracks_when_test_fails problem hN s9 i0 s9_find s9_fail]
  simp [zdBacktrack, s9_all_max]

/-- The configuration's registers and tags are exactly those in printed (4). -/
theorem start_shape :
    start.x i0.castSucc = code3 ∧ start.tag i0.castSucc = false ∧
    start.x i1.castSucc = code4 ∧ start.tag i1.castSucc = false ∧
    start.x (Fin.last 2) = code1 ∧ start.tag (Fin.last 2) = true := by
  simp [start, i0, i1, code1, code3, code4]

/-- After the certified trace, D1/D3 has no next configuration. -/
theorem stuck_at_s9 : zdStep problem hN s9 = none := step_s9

private theorem no_reaches_code4 :
    ¬ Relation.ReflTransGen problem.step code1 code4 := by
  intro hReach
  rcases Relation.ReflTransGen.cases_tail hReach with hEq | ⟨prev, _, hEdge⟩
  · have hVals := congrArg Fin.val hEq
    norm_num [code1, code4] at hVals
  · simp [problem, code4] at hEdge

/-- The offending configuration is reached from D0, not merely a possible
register assignment.  Lemma 1 sets register 2 to `4`, then register 1 to `3`;
tag soundness rules out the alternate outcome that would tag `4`. -/
theorem initial_reaches_start : Relation.ReflTransGen
    (fun a b : ZDConfig 2 5 => zdStep problem hN a = some b)
    (zdInitial 2 5 hN src) start := by
  let initial := zdInitial 2 5 hN src
  have hPrefix2 : LemmaOnePrefix hN initial i1 := by
    intro k hk
    fin_cases k <;> simp [initial, zdInitial, src, code1]
  obtain ⟨base, hRunBase, hOutcomeBase⟩ :=
    lemma_one problem hN initial i1 code4 hPrefix2 (by decide)
  have hBaseA : LemmaOneOutcomeA hN initial i1 code4 base := by
    rcases hOutcomeBase with hA | hB
    · exact hA
    · rcases hB with ⟨q, hq, hRest⟩
      have hImpossible : 1 < q.val := by simpa [i1] using hq
      omega
  rcases hBaseA with ⟨hBaseX1, hBaseTag1, hBasePrefix, hBaseSuffix⟩
  have hBaseX0 : base.x i0.castSucc = code1 := by
    have h := hBasePrefix i0 (by decide)
    simpa [i0, hN, firstCode, code1] using h.1
  have hBaseTag0 : base.tag i0.castSucc = false := by
    exact (hBasePrefix i0 (by decide)).2
  have hBaseSrcX : base.x (Fin.last 2) = code1 := by
    have h := hBaseSuffix (Fin.last 2) (by decide)
    rw [zdInitial_source] at h
    exact h.1
  have hBaseSrcTag : base.tag (Fin.last 2) = true := by
    have h := hBaseSuffix (Fin.last 2) (by decide)
    rw [zdInitial_source_tag] at h
    exact h.2
  have hPrefix1 : LemmaOnePrefix hN base i0 := by
    intro k hk
    have hk0 : k = i0 := by
      simpa [i0] using hk
    subst k
    exact ⟨hBaseX0, hBaseTag0⟩
  obtain ⟨event, hRunEvent, hOutcomeEvent⟩ :=
    lemma_one problem hN base i0 code3 hPrefix1 (by decide)
  have hEventA : LemmaOneOutcomeA hN base i0 code3 event := by
    rcases hOutcomeEvent with hA | hB
    · exact hA
    · rcases hB with ⟨q, hq, hInitiallyUntagged, hMiddle, hValue, hTag,
        hPrefix, hSuffix⟩
      have hqVal : q.val = 1 := by
        have hLower : 0 < q.val := by simpa [i0] using hq
        omega
      have hqEq : q = i1 := by
        apply Fin.ext
        exact hqVal
      subst q
      have hSound := zd_soundness problem 2 hN src (by
        simpa [initial] using hRunBase.trans hRunEvent)
      have hReach := hSound i1.castSucc hTag
      have hEventValue : event.x i1.castSucc = code4 := by
        calc
          event.x i1.castSucc = base.x i1.castSucc := hValue
          _ = code4 := hBaseX1
      rw [hEventValue] at hReach
      exact (no_reaches_code4 hReach).elim
  rcases hEventA with ⟨hEventX0, hEventTag0, hEventPrefix, hEventSuffix⟩
  have hEventX1 : event.x i1.castSucc = code4 := by
    exact (hEventSuffix i1.castSucc (by decide)).1.trans hBaseX1
  have hEventTag1 : event.tag i1.castSucc = false := by
    rw [(hEventSuffix i1.castSucc (by decide)).2, hBaseTag1]
  have hEventSrcX : event.x (Fin.last 2) = code1 := by
    exact (hEventSuffix (Fin.last 2) (by decide)).1.trans hBaseSrcX
  have hEventSrcTag : event.tag (Fin.last 2) = true := by
    rw [(hEventSuffix (Fin.last 2) (by decide)).2, hBaseSrcTag]
  have hEventEq : event = start := by
    cases event with
    | mk x tag =>
      simp only [start, ZDConfig.mk.injEq]
      constructor
      · funext i
        fin_cases i
        · simpa [i0] using hEventX0
        · simpa [i1] using hEventX1
        · simpa using hEventSrcX
      · funext i
        fin_cases i
        · simpa [i0] using hEventTag0
        · simpa [i1] using hEventTag1
        · simpa using hEventSrcTag
  rw [← hEventEq]
  exact hRunBase.trans hRunEvent

/-- The machine reaches the all-maximum stuck configuration from `start`. -/
theorem trace_to_stuck : Relation.ReflTransGen
    (fun a b : ZDConfig 2 5 => zdStep problem hN a = some b) start s9 := by
  let R := fun a b : ZDConfig 2 5 => zdStep problem hN a = some b
  have h01 : Relation.ReflTransGen R start s1 :=
    Relation.ReflTransGen.tail Relation.ReflTransGen.refl step_start
  have h02 : Relation.ReflTransGen R start s2 :=
    Relation.ReflTransGen.tail h01 step_s1
  have h03 : Relation.ReflTransGen R start s3 :=
    Relation.ReflTransGen.tail h02 step_s2
  have h04 : Relation.ReflTransGen R start s4 :=
    Relation.ReflTransGen.tail h03 step_s3
  have h05 : Relation.ReflTransGen R start s5 :=
    Relation.ReflTransGen.tail h04 step_s4
  have h06 : Relation.ReflTransGen R start s6 :=
    Relation.ReflTransGen.tail h05 step_s5
  have h07 : Relation.ReflTransGen R start s7 :=
    Relation.ReflTransGen.tail h06 step_s6
  have h08 : Relation.ReflTransGen R start s8 :=
    Relation.ReflTransGen.tail h07 step_s7
  exact Relation.ReflTransGen.tail h08 step_s8

/-- The tagged source reaches the target in exactly two abstract steps. -/
theorem source_reaches_target : ReachesWithin problem 2 code1 code3 := by
  have h12 : problem.step code1 code2 := by simp [problem, code1, code2]
  have h23 : problem.step code2 code3 := by simp [problem, code2, code3]
  exact ⟨2, by decide, AbstractPath.cons h12 (AbstractPath.cons h23 (AbstractPath.nil code3))⟩

private theorem all_reachable_configs_are_in_trace {final : ZDConfig 2 5}
    (hRun : Relation.ReflTransGen
      (fun a b : ZDConfig 2 5 => zdStep problem hN a = some b) start final) :
    final = start ∨ final = s1 ∨ final = s2 ∨ final = s3 ∨ final = s4 ∨
      final = s5 ∨ final = s6 ∨ final = s7 ∨ final = s8 ∨ final = s9 := by
  induction hRun with
  | refl => exact Or.inl rfl
  | @tail prev current hRun hStep ih =>
    rcases ih with h | h | h | h | h | h | h | h | h | h
    · subst prev
      rw [step_start] at hStep
      right
      left
      exact (Option.some.inj hStep).symm
    · subst prev
      rw [step_s1] at hStep
      right
      right
      left
      exact (Option.some.inj hStep).symm
    · subst prev
      rw [step_s2] at hStep
      right
      right
      right
      left
      exact (Option.some.inj hStep).symm
    · subst prev
      rw [step_s3] at hStep
      right
      right
      right
      right
      left
      exact (Option.some.inj hStep).symm
    · subst prev
      rw [step_s4] at hStep
      right
      right
      right
      right
      right
      left
      exact (Option.some.inj hStep).symm
    · subst prev
      rw [step_s5] at hStep
      right
      right
      right
      right
      right
      right
      left
      exact (Option.some.inj hStep).symm
    · subst prev
      rw [step_s6] at hStep
      right
      right
      right
      right
      right
      right
      right
      left
      exact (Option.some.inj hStep).symm
    · subst prev
      rw [step_s7] at hStep
      right
      right
      right
      right
      right
      right
      right
      right
      left
      exact (Option.some.inj hStep).symm
    · subst prev
      rw [step_s8] at hStep
      right
      right
      right
      right
      right
      right
      right
      right
      right
      exact (Option.some.inj hStep).symm
    · subst prev
      rw [step_s9] at hStep
      cases hStep

/-- No configuration on any continuation of this computation has the target
value `3` tagged in register 1. -/
theorem target_never_tagged {final : ZDConfig 2 5}
    (hRun : Relation.ReflTransGen
      (fun a b : ZDConfig 2 5 => zdStep problem hN a = some b) start final) :
    ¬ (final.x i0.castSucc = code3 ∧ final.tag i0.castSucc = true) := by
  intro hTarget
  rcases all_reachable_configs_are_in_trace hRun with h | h | h | h | h | h | h | h | h | h <;>
    subst final <;>
    simp [start, s1, s2, s3, s4, s5, s6, s7, s8, s9, i0, i1,
      code1, code2, code3, code4, code5, firstCode, updateAndReset] at hTarget

/-- The printed Lemma 2 premise holds at `start`, but its conclusion fails on
every subsequent configuration of this deterministic computation. -/
theorem printed_lemma2_counterexample :
    start.x i0.castSucc = code3 ∧ start.tag i0.castSucc = false ∧
      start.x i1.castSucc = code4 ∧ start.tag i1.castSucc = false ∧
      start.x (Fin.last 2) = code1 ∧ start.tag (Fin.last 2) = true ∧
      Relation.ReflTransGen
        (fun a b : ZDConfig 2 5 => zdStep problem hN a = some b)
        (zdInitial 2 5 hN src) start ∧
      ReachesWithin problem 2 code1 code3 ∧
      Relation.ReflTransGen
        (fun a b : ZDConfig 2 5 => zdStep problem hN a = some b) start s9 ∧
      zdStep problem hN s9 = none ∧
      ∀ final, Relation.ReflTransGen
        (fun a b : ZDConfig 2 5 => zdStep problem hN a = some b) start final →
        ¬ (final.x i0.castSucc = code3 ∧ final.tag i0.castSucc = true) := by
  exact ⟨start_shape.1, start_shape.2.1, start_shape.2.2.1, start_shape.2.2.2.1,
    start_shape.2.2.2.2.1, start_shape.2.2.2.2.2, initial_reaches_start,
    source_reaches_target, trace_to_stuck, stuck_at_s9,
    fun final hRun ↦ target_never_tagged hRun⟩

end SavitchLemma.LemmaTwoCounterexample

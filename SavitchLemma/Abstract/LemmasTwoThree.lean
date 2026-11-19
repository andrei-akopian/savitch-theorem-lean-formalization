module

public import SavitchLemma.Abstract.BoundedReachability
public import SavitchLemma.Abstract.LemmaOne
public import SavitchLemma.Abstract.StepBehavior

import Mathlib.Tactic.Positivity

@[expose] public section

/-!
# Corrected simultaneous form of Savitch's Lemmas 2 and 3

With zero-based register indices, a target at index `j` is reachable from a
tagged register through at most `2^j` transitions.  The printed one-based bound
`2^j` is off by one at its base case; this module uses the corrected bound.
-/

namespace SavitchLemma

variable {r N : ℕ}

/-- The conclusion for a target register: its value is retained and tagged,
the prefix is cleared, and the suffix is unchanged. -/
def TwoThreeOutcome (hN : 1 < N) (initial final : ZDConfig r N)
    (target : Fin r) : Prop :=
  (∀ k : Fin r, k.val < target.val →
    final.x k.castSucc = firstCode N hN ∧ final.tag k.castSucc = false) ∧
  final.x target.castSucc = initial.x target.castSucc ∧
  final.tag target.castSucc = true ∧
  (∀ i : Fin (r + 1), target.val < i.val →
    final.x i = initial.x i ∧ final.tag i = initial.tag i)

/-- Unified Lemmas 2 and 3 with the corrected exponential bound.  `j` counts
the reset prefix, while `m` counts the already-tagged middle block; `m = 0`
is Lemma 2 and `m = p + 1` is Lemma 3. -/
theorem lemma_two_three (P : AbstractProblem N) (hN : 1 < N) :
    ∀ (j m : ℕ) (cfg : ZDConfig r N) (target : Fin r),
      target.val = j + m →
      (∀ k : Fin r, k.val < j →
        cfg.x k.castSucc = firstCode N hN ∧ cfg.tag k.castSucc = false) →
      (∀ k : Fin r, j ≤ k.val → k.val < target.val → cfg.tag k.castSucc = true) →
      cfg.tag target.castSucc = false →
      0 < (cfg.x target.castSucc).val →
      (∃ q : Fin (r + 1), cfg.tag q = true ∧
        ReachesWithin P (2 ^ j) (cfg.x q) (cfg.x target.castSucc)) →
      ∃ final,
        Relation.ReflTransGen (fun a b : ZDConfig r N => zdStep P hN a = some b)
          cfg final ∧ TwoThreeOutcome hN cfg final target := by
  intro j
  induction j with
  | zero =>
    intro m cfg target hIndex hPrefix hMiddle hTargetUntagged hTargetPos hReach
    rcases hReach with ⟨q, hqTag, hPath⟩
    have hPathOne : ReachesWithin P 1 (cfg.x q) (cfg.x target.castSucc) := by
      simpa using hPath
    have hOneTest := (ReachesWithin.one_iff P).mp hPathOne
    have hFind : firstUntagged cfg = some target := by
      apply (firstUntagged_eq_some_iff cfg target).2
      refine ⟨hTargetUntagged, ?_⟩
      intro k hkt
      have hktVal : k.val < target.val := by simpa using hkt
      exact hMiddle k (by omega) hktVal
    have hTest : ∃ i : Fin (r + 1), cfg.tag i = true ∧
        (cfg.x i = cfg.x target.castSucc ∨ P.step (cfg.x i) (cfg.x target.castSucc)) :=
      ⟨q, hqTag, hOneTest⟩
    have hStep := zdStep_of_successful_test P hN cfg target hFind hTest
    refine ⟨updateAndReset hN cfg target (cfg.x target.castSucc) true,
      Relation.ReflTransGen.tail Relation.ReflTransGen.refl hStep, ?_⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro k hkt
      exact updateAndReset_at_before hN cfg target (cfg.x target.castSucc) true
        k.castSucc (by simpa using hkt)
    · exact (updateAndReset_at_current hN cfg target (cfg.x target.castSucc) true).1
    · exact (updateAndReset_at_current hN cfg target (cfg.x target.castSucc) true).2
    · intro i hit
      exact updateAndReset_at_after hN cfg target (cfg.x target.castSucc) true i hit
  | succ j ih =>
    intro m cfg target hIndex hPrefix hMiddle hTargetUntagged hTargetPos hReach
    rcases hReach with ⟨q, hqTag, hPath⟩
    have hSplit := ReachesWithin.splitPowTwo_with_positive_midpoint P j
      hTargetPos hPath
    rcases hSplit with ⟨midpoint, hLeft, hRight, hMidPos⟩
    have hjLt : j < r := by omega
    let jFin : Fin r := ⟨j, hjLt⟩
    have hPrefixOne : LemmaOnePrefix hN cfg jFin := by
      intro k hk
      exact hPrefix k (by simpa [jFin] using Nat.lt_succ_of_le hk)
    have hJltTarget : jFin.val < target.val := by
      simpa [jFin] using (show j < target.val by omega)
    obtain ⟨event, hEventRun, hEventOutcome⟩ :=
      lemma_one P hN cfg jFin midpoint hPrefixOne hMidPos
    rcases hEventOutcome with hA | hB
    · rcases hA with ⟨hMidValue, hMidUntagged, hEventPrefix, hEventSuffix⟩
      have hqAfter : j < q.val := by
        by_contra hNot
        have hqLe : q.val ≤ j := Nat.le_of_not_gt hNot
        let k : Fin r := ⟨q.val, by omega⟩
        have hPrefixQ := hPrefix k (by simp [k]; omega)
        have hQEq : q = k.castSucc := Fin.ext rfl
        rw [hQEq, hPrefixQ.2] at hqTag
        cases hqTag
      have hQPreserved := hEventSuffix q (by simpa [jFin] using hqAfter)
      have hEventSource : event.tag q = true ∧ event.x q = cfg.x q :=
        ⟨hQPreserved.2.trans hqTag, hQPreserved.1⟩
      have hEventMidPos : 0 < (event.x jFin.castSucc).val := by
        rw [hMidValue]
        exact hMidPos
      have hLeftEvent : ReachesWithin P (2 ^ j)
          (event.x q) (event.x jFin.castSucc) := by
        simpa [hEventSource.2, hMidValue] using hLeft
      have hPrefixSmall : ∀ k : Fin r, k.val < j →
          event.x k.castSucc = firstCode N hN ∧ event.tag k.castSucc = false := by
        intro k hk
        exact hEventPrefix k (by simpa [jFin] using hk)
      have hMiddleEmpty : ∀ k : Fin r, j ≤ k.val → k.val < j →
          event.tag k.castSucc = true := by
        intro k hLo hHi
        omega
      have hIndexSmall : jFin.val = j + 0 := by simp [jFin]
      obtain ⟨event1, hRun1, hOutcome1⟩ := ih 0 event jFin hIndexSmall
        hPrefixSmall hMiddleEmpty hMidUntagged hEventMidPos
        ⟨q, hEventSource.1, hLeftEvent⟩
      rcases hOutcome1 with ⟨hReset1, hTaggedValue, hTaggedTag, hSuffix1⟩
      have hTargetAfterJ : jFin.val < (target.castSucc).val := by
        simpa using hJltTarget
      have hTargetValue1 : event1.x target.castSucc = cfg.x target.castSucc := by
        calc
          event1.x target.castSucc = event.x target.castSucc :=
            (hSuffix1 target.castSucc hTargetAfterJ).1
          _ = cfg.x target.castSucc := (hEventSuffix target.castSucc hTargetAfterJ).1
      have hTargetTag1 : event1.tag target.castSucc = false := by
        calc
          event1.tag target.castSucc = event.tag target.castSucc :=
            (hSuffix1 target.castSucc hTargetAfterJ).2
          _ = cfg.tag target.castSucc := (hEventSuffix target.castSucc hTargetAfterJ).2
          _ = false := hTargetUntagged
      have hMiddleLarge : ∀ k : Fin r, j ≤ k.val → k.val < target.val →
          event1.tag k.castSucc = true := by
        intro k hLo hHi
        by_cases hEq : k.val = j
        · have hk : k = jFin := Fin.ext hEq
          subst k
          exact hTaggedTag
        · have hGt : j < k.val := by omega
          have hGtFin : jFin.val < (k.castSucc).val := by simpa [jFin] using hGt
          calc
            event1.tag k.castSucc = event.tag k.castSucc :=
              (hSuffix1 k.castSucc hGtFin).2
            _ = cfg.tag k.castSucc :=
              (hEventSuffix k.castSucc hGtFin).2
            _ = true := hMiddle k (by omega) hHi
      have hRightEvent : ReachesWithin P (2 ^ j)
          (event1.x jFin.castSucc) (event1.x target.castSucc) := by
        have hMidValue1 : event1.x jFin.castSucc = midpoint := hTaggedValue.trans hMidValue
        simpa [hMidValue1, hTargetValue1] using hRight
      have hIndexLarge : target.val = j + (m + 1) := by omega
      obtain ⟨final, hRun2, hOutcome2⟩ := ih (m + 1) event1 target hIndexLarge
        hReset1 hMiddleLarge hTargetTag1 (by rw [hTargetValue1]; exact hTargetPos)
        ⟨jFin.castSucc, hTaggedTag, hRightEvent⟩
      rcases hOutcome2 with ⟨hReset2, hFinalValue, hFinalTag, hFinalSuffix⟩
      refine ⟨final, hEventRun.trans (hRun1.trans hRun2), ?_⟩
      refine ⟨hReset2, ?_, hFinalTag, ?_⟩
      · exact hFinalValue.trans hTargetValue1
      · intro i hi
        have hiAfterJ : jFin.val < i.val := by
          simpa [jFin] using (show j < i.val by omega)
        constructor
        · calc
            final.x i = event1.x i := (hFinalSuffix i hi).1
            _ = event.x i := (hSuffix1 i hiAfterJ).1
            _ = cfg.x i := (hEventSuffix i hiAfterJ).1
        · exact (hFinalSuffix i hi).2.trans
            ((hSuffix1 i hiAfterJ).2.trans (hEventSuffix i hiAfterJ).2)
    · rcases hB with ⟨qB, hJQ, hQUntagged, hBetween, hQValue, hQTag,
        hReset, hSuffix⟩
      have hJQVal : j < qB.val := by simpa [jFin] using hJQ
      have hQVal : qB.val = target.val := by
        by_contra hNe
        rcases Nat.lt_or_gt_of_ne hNe with hQlt | hTlt
        · have hTargetMiddle := hMiddle qB (by omega) hQlt
          rw [hQUntagged] at hTargetMiddle
          cases hTargetMiddle
        · have hTargetBetween := hBetween target hJltTarget hTlt
          rw [hTargetUntagged] at hTargetBetween
          cases hTargetBetween
      have hQEq : qB = target := Fin.ext hQVal
      subst qB
      exact ⟨event, hEventRun, ⟨hReset, hQValue, hQTag, hSuffix⟩⟩

/-- Corrected Lemma 2 is the empty-middle-block case of `lemma_two_three`. -/
theorem lemma_two_corrected (P : AbstractProblem N) (hN : 1 < N)
    (j : ℕ) (cfg : ZDConfig r N) (target : Fin r) (hTarget : target.val = j)
    (hPrefix : ∀ k : Fin r, k.val < j →
      cfg.x k.castSucc = firstCode N hN ∧ cfg.tag k.castSucc = false)
    (hTargetUntagged : cfg.tag target.castSucc = false)
    (hTargetPos : 0 < (cfg.x target.castSucc).val)
    (hReach : ∃ q : Fin (r + 1), cfg.tag q = true ∧
      ReachesWithin P (2 ^ j) (cfg.x q) (cfg.x target.castSucc)) :
    ∃ final,
      Relation.ReflTransGen (fun a b : ZDConfig r N => zdStep P hN a = some b)
        cfg final ∧ TwoThreeOutcome hN cfg final target := by
  apply lemma_two_three P hN j 0 cfg target
  · simpa using hTarget
  · exact hPrefix
  · intro k _ hLt
    omega
  · exact hTargetUntagged
  · exact hTargetPos
  · exact hReach

/-- Corrected Lemma 3 is the positive-middle-block case of
`lemma_two_three`. -/
theorem lemma_three_corrected (P : AbstractProblem N) (hN : 1 < N)
    (j p : ℕ) (cfg : ZDConfig r N) (target : Fin r)
    (hTarget : target.val = j + (p + 1))
    (hPrefix : ∀ k : Fin r, k.val < j →
      cfg.x k.castSucc = firstCode N hN ∧ cfg.tag k.castSucc = false)
    (hMiddle : ∀ k : Fin r, j ≤ k.val → k.val < target.val →
      cfg.tag k.castSucc = true)
    (hTargetUntagged : cfg.tag target.castSucc = false)
    (hTargetPos : 0 < (cfg.x target.castSucc).val)
    (hReach : ∃ q : Fin (r + 1), cfg.tag q = true ∧
      ReachesWithin P (2 ^ j) (cfg.x q) (cfg.x target.castSucc)) :
    ∃ final,
      Relation.ReflTransGen (fun a b : ZDConfig r N => zdStep P hN a = some b)
        cfg final ∧ TwoThreeOutcome hN cfg final target := by
  exact lemma_two_three P hN j (p + 1) cfg target hTarget hPrefix hMiddle
    hTargetUntagged hTargetPos hReach

/-- Abstract completeness: with one extra working register, any target
reachable within `2^r` edges is eventually tagged. -/
theorem savitch_abstract_completeness (P : AbstractProblem N) (hN : 1 < N)
    (r : ℕ) (source target : ValidCode N)
    (hReach : ReachesWithin P (2 ^ r) source.val target.val) :
    ∃ final,
      Relation.ReflTransGen
        (fun a b : ZDConfig (r + 1) N => zdStep P hN a = some b)
        (zdInitial (r + 1) N hN source) final ∧
      final.tag (Fin.last r).castSucc = true ∧
      final.x (Fin.last r).castSucc = target.val := by
  let initial := zdInitial (r + 1) N hN source
  have hPrefix : LemmaOnePrefix hN initial (Fin.last r) := by
    intro k hk
    have hkLe : k.val ≤ r := by simpa using hk
    have hNe : k.val ≠ r + 1 := by omega
    simp [initial, zdInitial, Fin.val_castSucc, hNe]
  obtain ⟨middleCfg, hRunMiddle, hOutcomeMiddle⟩ :=
    lemma_one P hN initial (Fin.last r) target.val hPrefix target.property.1
  have hMiddleA : LemmaOneOutcomeA hN initial (Fin.last r) target.val middleCfg := by
    rcases hOutcomeMiddle with hA | hB
    · exact hA
    · rcases hB with ⟨q, hq, hRest⟩
      have hImpossible : r < q.val := by simpa using hq
      omega
  rcases hMiddleA with ⟨hValue, hTag, hPrefixReset, hSuffix⟩
  have hSourceValue : middleCfg.x (Fin.last (r + 1)) = source.val := by
    have h := hSuffix (Fin.last (r + 1)) (by simp)
    rw [zdInitial_source] at h
    exact h.1
  have hSourceTag : middleCfg.tag (Fin.last (r + 1)) = true := by
    have h := hSuffix (Fin.last (r + 1)) (by simp)
    rw [zdInitial_source_tag] at h
    exact h.2
  have hPrefixTwoThree : ∀ k : Fin (r + 1), k.val < r →
      middleCfg.x k.castSucc = firstCode N hN ∧ middleCfg.tag k.castSucc = false := by
    intro k hk
    exact hPrefixReset k hk
  have hTargetUntagged : middleCfg.tag (Fin.last r).castSucc = false := hTag
  have hTargetPos : 0 < (middleCfg.x (Fin.last r).castSucc).val := by
    rw [hValue]
    exact target.property.1
  have hReachMiddle : ReachesWithin P (2 ^ r)
      (middleCfg.x (Fin.last (r + 1)))
      (middleCfg.x (Fin.last r).castSucc) := by
    simpa [hSourceValue, hValue] using hReach
  obtain ⟨final, hRunFinal, hOutcomeFinal⟩ :=
    lemma_two_three P hN r 0 middleCfg (Fin.last r) (by simp)
      hPrefixTwoThree (by intro k hlo hhi; omega) hTargetUntagged hTargetPos
      ⟨Fin.last (r + 1), hSourceTag, hReachMiddle⟩
  rcases hOutcomeFinal with ⟨_, hFinalValue, hFinalTag, _⟩
  exact ⟨final, hRunMiddle.trans hRunFinal, hFinalTag, hFinalValue.trans hValue⟩

end SavitchLemma

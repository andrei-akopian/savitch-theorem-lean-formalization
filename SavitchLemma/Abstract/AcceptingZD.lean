module

public import SavitchLemma.Abstract.LemmasTwoThree

@[expose] public section

/-!
# Accepting version of Savitch's abstract register machine

This module formalizes the unmodified `D2` rule from Savitch (1970, p. 181),
which immediately accepts whenever a newly verified ID is accepting, and `D3`'s
explicit rejection when all working registers reach the maximum code.
-/

namespace SavitchLemma

variable {r N : ℕ}

/-- Result of one step of the unmodified register machine. -/
inductive ZDOutcome (r N : ℕ) where
  | running (cfg : ZDConfig r N)
  | accept
  | reject

/-- One step of the unmodified `D1`/`D2`/`D3` machine with explicit acceptance
and rejection outcomes. -/
noncomputable def zdAcceptingStep (P : AbstractProblem N) (hN : 1 < N)
    (isAccepting : Fin (N + 1) → Bool) (cfg : ZDConfig r N) : ZDOutcome r N := by
  classical
  match firstUntagged cfg with
  | none =>
    match zdBacktrack hN cfg with
    | none => exact .reject
    | some next => exact .running next
  | some j =>
    if h : ∃ i : Fin (r + 1), cfg.tag i = true ∧
        (cfg.x i = cfg.x j.castSucc ∨ P.step (cfg.x i) (cfg.x j.castSucc)) then
      if isAccepting (cfg.x j.castSucc) then
        exact .accept
      else
        exact .running (updateAndReset hN cfg j (cfg.x j.castSucc) true)
    else
      match zdBacktrack hN cfg with
      | none => exact .reject
      | some next => exact .running next

/-- Single-step relation on `ZDOutcome`, where `accept` and `reject` are
terminal. -/
def zdOutcomeStep (P : AbstractProblem N) (hN : 1 < N)
    (isAccepting : Fin (N + 1) → Bool) : ZDOutcome r N → ZDOutcome r N → Prop
  | .running cfg, next => zdAcceptingStep P hN isAccepting cfg = next
  | .accept, _ => False
  | .reject, _ => False

/-- Whenever the accepting machine produces a running configuration, it agrees
with the modified register machine `zdStep`. -/
theorem zdAcceptingStep_running_eq_zdStep (P : AbstractProblem N) (hN : 1 < N)
    (isAccepting : Fin (N + 1) → Bool) {cfg next : ZDConfig r N}
    (hStep : zdAcceptingStep P hN isAccepting cfg = .running next) :
    zdStep P hN cfg = some next := by
  classical
  unfold zdAcceptingStep at hStep
  unfold zdStep
  cases hFind : firstUntagged cfg with
  | none =>
    simp only [hFind] at hStep ⊢
    cases hBack : zdBacktrack hN cfg with
    | none => simp [hBack] at hStep
    | some cfg' =>
      simp only [hBack, ZDOutcome.running.injEq] at hStep
      simp [hStep]
  | some j =>
    simp only [hFind] at hStep ⊢
    by_cases hTest : ∃ i : Fin (r + 1), cfg.tag i = true ∧
        (cfg.x i = cfg.x j.castSucc ∨ P.step (cfg.x i) (cfg.x j.castSucc))
    · simp only [hTest, ↓reduceDIte] at hStep ⊢
      by_cases hAcc : isAccepting (cfg.x j.castSucc) = true
      · simp [hAcc] at hStep
      · simp [hAcc] at hStep
        exact congrArg some hStep
    · simp only [hTest, ↓reduceDIte] at hStep ⊢
      cases hBack : zdBacktrack hN cfg with
      | none => simp [hBack] at hStep
      | some cfg' =>
        simp only [hBack, ZDOutcome.running.injEq] at hStep
        simp [hStep]

/-- Any prefix of an accepting run reaching `.running cfg` corresponds to a run
of `zdStep` reaching `cfg`. -/
theorem zdOutcomeStep_running_to_zdStep (P : AbstractProblem N) (hN : 1 < N)
    (isAccepting : Fin (N + 1) → Bool) {cfg₀ cfg : ZDConfig r N}
    (hRun : Relation.ReflTransGen (zdOutcomeStep P hN isAccepting)
      (.running cfg₀) (.running cfg)) :
    Relation.ReflTransGen (fun a b => zdStep P hN a = some b) cfg₀ cfg := by
  generalize hInit : ZDOutcome.running cfg₀ = out₀ at hRun
  generalize hFinal : ZDOutcome.running cfg = out₁ at hRun
  induction hRun generalizing cfg₀ cfg with
  | refl =>
    have hEq := hInit.trans hFinal.symm
    cases hEq
    exact Relation.ReflTransGen.refl
  | @tail prev curr hPref hStep ih =>
    subst hFinal
    cases prev with
    | accept => cases hStep
    | reject => cases hStep
    | running prevCfg =>
      have hPrefRun := ih hInit rfl
      have hStep' : zdStep P hN prevCfg = some cfg :=
        zdAcceptingStep_running_eq_zdStep P hN isAccepting hStep
      exact Relation.ReflTransGen.tail hPrefRun hStep'

/-- Soundness of the accepting abstract machine: reaching `.accept` implies an
accepting ID is reachable from `source` in `P`. -/
theorem zdAcceptingStep_soundness (P : AbstractProblem N) (r : ℕ) (hN : 1 < N)
    (isAccepting : Fin (N + 1) → Bool) (source : ValidCode N)
    (hAcc : Relation.ReflTransGen (zdOutcomeStep P hN isAccepting)
      (.running (zdInitial r N hN source)) .accept) :
    ∃ target : Fin (N + 1), isAccepting target = true ∧
      Relation.ReflTransGen P.step source.val target := by
  generalize hInit : ZDOutcome.running (zdInitial r N hN source) = out₀ at hAcc
  generalize hFinal : (ZDOutcome.accept : ZDOutcome r N) = out₁ at hAcc
  cases hAcc with
  | refl =>
    have hEq := hInit.trans hFinal.symm
    cases hEq
  | tail hPref hStep =>
    rename_i prev
    cases prev with
    | accept => exact False.elim hStep
    | reject => exact False.elim hStep
    | running prevCfg =>
      have hZdRun : Relation.ReflTransGen (fun a b => zdStep P hN a = some b)
          (zdInitial r N hN source) prevCfg := by
        rw [← hInit] at hPref
        exact zdOutcomeStep_running_to_zdStep P hN isAccepting hPref
      have hSound := zd_soundness P r hN source hZdRun
      have hStepAcc : zdAcceptingStep P hN isAccepting prevCfg = .accept := by
        simpa [zdOutcomeStep, ← hFinal] using hStep
      classical
      unfold zdAcceptingStep at hStepAcc
      cases hFind : firstUntagged prevCfg with
      | none =>
        simp only [hFind] at hStepAcc
        cases hBack : zdBacktrack hN prevCfg <;> simp [hBack] at hStepAcc
      | some j =>
        simp only [hFind] at hStepAcc
        by_cases hTest : ∃ i : Fin (r + 1), prevCfg.tag i = true ∧
            (prevCfg.x i = prevCfg.x j.castSucc ∨ P.step (prevCfg.x i) (prevCfg.x j.castSucc))
        · simp only [hTest, ↓reduceDIte] at hStepAcc
          by_cases hTagAcc : isAccepting (prevCfg.x j.castSucc) = true
          · rcases hTest with ⟨i, hiTag, hEdge⟩
            exact ⟨prevCfg.x j.castSucc, hTagAcc,
              reaches_of_eq_or_step P (hSound i hiTag) hEdge⟩
          · simp [hTagAcc] at hStepAcc
        · simp only [hTest, ↓reduceDIte] at hStepAcc
          cases hBack : zdBacktrack hN prevCfg <;> simp [hBack] at hStepAcc

/-- Along any run of `zdStep`, either `zdAcceptingStep` already accepts or it
reaches the same running configuration. -/
theorem zdStep_run_lifts_to_zdOutcome (P : AbstractProblem N) (hN : 1 < N)
    (isAccepting : Fin (N + 1) → Bool) {cfg₀ cfg₁ : ZDConfig r N}
    (hRun : Relation.ReflTransGen (fun a b => zdStep P hN a = some b) cfg₀ cfg₁) :
    Relation.ReflTransGen (zdOutcomeStep P hN isAccepting) (.running cfg₀) .accept ∨
    Relation.ReflTransGen (zdOutcomeStep P hN isAccepting) (.running cfg₀) (.running cfg₁) := by
  induction hRun with
  | refl => exact Or.inr Relation.ReflTransGen.refl
  | @tail prev curr hPref hStep ih =>
    rcases ih with hAcc | hRunPrev
    · exact Or.inl hAcc
    · cases hOut : zdAcceptingStep P hN isAccepting prev with
      | accept =>
        exact Or.inl (Relation.ReflTransGen.tail hRunPrev hOut)
      | running next =>
        have hZd : zdStep P hN prev = some next :=
          zdAcceptingStep_running_eq_zdStep P hN isAccepting hOut
        have hEq : next = curr := Option.some.inj (hZd.symm.trans hStep)
        subst hEq
        exact Or.inr (Relation.ReflTransGen.tail hRunPrev hOut)
      | reject =>
        exfalso
        classical
        unfold zdAcceptingStep at hOut
        unfold zdStep at hStep
        cases hFind : firstUntagged prev with
        | none =>
          simp only [hFind] at hOut hStep
          cases hBack : zdBacktrack hN prev <;> simp [hBack] at hOut hStep
        | some j =>
          simp only [hFind] at hOut hStep
          by_cases hTest : ∃ i : Fin (r + 1), prev.tag i = true ∧
              (prev.x i = prev.x j.castSucc ∨ P.step (prev.x i) (prev.x j.castSucc))
          · simp only [hTest, ↓reduceDIte] at hOut hStep
            by_cases hAcc : isAccepting (prev.x j.castSucc) <;> simp [hAcc] at hOut
          · simp only [hTest, ↓reduceDIte] at hOut hStep
            cases hBack : zdBacktrack hN prev <;> simp [hBack] at hOut hStep

/-- If a `zdStep` run takes an untagged register to a tagged accepting value,
the accepting machine reaches `.accept`. -/
theorem zdStep_tagged_accepting_reaches_accept (P : AbstractProblem N) (hN : 1 < N)
    (isAccepting : Fin (N + 1) → Bool) (idx : Fin (r + 1)) {cfg₀ cfg₁ : ZDConfig r N}
    (hRun : Relation.ReflTransGen (fun a b => zdStep P hN a = some b) cfg₀ cfg₁)
    (hInitUntagged : cfg₀.tag idx = false)
    (hFinalTagged : cfg₁.tag idx = true)
    (hFinalAcc : isAccepting (cfg₁.x idx) = true) :
    Relation.ReflTransGen (zdOutcomeStep P hN isAccepting) (.running cfg₀) .accept := by
  induction hRun with
  | refl =>
    rw [hInitUntagged] at hFinalTagged
    cases hFinalTagged
  | @tail prev curr hPref hStep ih =>
    by_cases hPrevTag : prev.tag idx = true
    · -- If `idx` was already tagged in `prev`, `curr.tag idx = true` forces `curr.x idx = prev.x idx`.
      have hPreserved : curr.x idx = prev.x idx := by
        classical
        unfold zdStep at hStep
        cases hFind : firstUntagged prev with
        | none =>
          have hBack : zdBacktrack hN prev = some curr := by simpa [hFind] using hStep
          rcases (zdBacktrack_eq_some_iff hN prev curr).1 hBack with ⟨k, _, _, hEq⟩
          subst curr
          by_cases hEqIdx : idx.val = k.val
          · simp [updateAndReset, hEqIdx] at hFinalTagged
          · by_cases hLtIdx : idx.val < k.val
            · simp [updateAndReset, hEqIdx, hLtIdx] at hFinalTagged
            · simp [updateAndReset, hEqIdx, hLtIdx]
        | some j =>
          by_cases hTest : ∃ i : Fin (r + 1), prev.tag i = true ∧
              (prev.x i = prev.x j.castSucc ∨ P.step (prev.x i) (prev.x j.castSucc))
          · have hEq : updateAndReset hN prev j (prev.x j.castSucc) true = curr :=
              Option.some.inj (by simpa [hFind, hTest] using hStep)
            subst curr
            by_cases hEqIdx : idx.val = j.val
            · simp only [updateAndReset, hEqIdx, ↓reduceIte]
              exact congrArg prev.x (Fin.ext hEqIdx).symm
            · by_cases hLtIdx : idx.val < j.val
              · simp [updateAndReset, hEqIdx, hLtIdx] at hFinalTagged
              · simp [updateAndReset, hEqIdx, hLtIdx]
          · have hBack : zdBacktrack hN prev = some curr := by simpa [hFind, hTest] using hStep
            rcases (zdBacktrack_eq_some_iff hN prev curr).1 hBack with ⟨k, _, _, hEq⟩
            subst curr
            by_cases hEqIdx : idx.val = k.val
            · simp [updateAndReset, hEqIdx] at hFinalTagged
            · by_cases hLtIdx : idx.val < k.val
              · simp [updateAndReset, hEqIdx, hLtIdx] at hFinalTagged
              · simp [updateAndReset, hEqIdx, hLtIdx]
      rw [hPreserved] at hFinalAcc
      exact ih hPrevTag hFinalAcc
    · have hPrevFalse : prev.tag idx = false := Bool.eq_false_iff.mpr hPrevTag
      -- Since `curr.tag idx = true` and `prev.tag idx = false`, `hStep` must be D2 at `idx`.
      have hStepAccept : zdAcceptingStep P hN isAccepting prev = .accept := by
        classical
        unfold zdStep at hStep
        unfold zdAcceptingStep
        cases hFind : firstUntagged prev with
        | none =>
          have hBack : zdBacktrack hN prev = some curr := by simpa [hFind] using hStep
          rcases (zdBacktrack_eq_some_iff hN prev curr).1 hBack with ⟨k, _, _, hEq⟩
          subst curr
          by_cases hEqIdx : idx.val = k.val
          · simp [updateAndReset, hEqIdx] at hFinalTagged
          · by_cases hLtIdx : idx.val < k.val
            · simp [updateAndReset, hEqIdx, hLtIdx] at hFinalTagged
            · simp [updateAndReset, hEqIdx, hLtIdx, hPrevFalse] at hFinalTagged
        | some j =>
          by_cases hTest : ∃ i : Fin (r + 1), prev.tag i = true ∧
              (prev.x i = prev.x j.castSucc ∨ P.step (prev.x i) (prev.x j.castSucc))
          · have hEq : updateAndReset hN prev j (prev.x j.castSucc) true = curr :=
              Option.some.inj (by simpa [hFind, hTest] using hStep)
            subst curr
            have hIdxEqJ : idx.val = j.val := by
              by_contra hNe
              by_cases hLtIdx : idx.val < j.val
              · simp [updateAndReset, hNe, hLtIdx] at hFinalTagged
              · simp [updateAndReset, hNe, hLtIdx, hPrevFalse] at hFinalTagged
            have hValEq : prev.x j.castSucc = (updateAndReset hN prev j (prev.x j.castSucc) true).x idx := by
              simp [updateAndReset, hIdxEqJ]
            simp only [hTest, ↓reduceDIte]
            rw [hValEq]
            simp [hFinalAcc]
          · have hBack : zdBacktrack hN prev = some curr := by simpa [hFind, hTest] using hStep
            rcases (zdBacktrack_eq_some_iff hN prev curr).1 hBack with ⟨k, _, _, hEq⟩
            subst curr
            by_cases hEqIdx : idx.val = k.val
            · simp [updateAndReset, hEqIdx] at hFinalTagged
            · by_cases hLtIdx : idx.val < k.val
              · simp [updateAndReset, hEqIdx, hLtIdx] at hFinalTagged
              · simp [updateAndReset, hEqIdx, hLtIdx, hPrevFalse] at hFinalTagged
      rcases zdStep_run_lifts_to_zdOutcome P hN isAccepting hPref with hAcc | hRunPrev
      · exact hAcc
      · exact Relation.ReflTransGen.tail hRunPrev hStepAccept

/-- Completeness of the accepting abstract machine: if an accepting valid ID is
reachable from `source` within `2 ^ r` steps, then the accepting machine with
`r + 1` working registers reaches `.accept`. -/
theorem zdAcceptingStep_completeness (P : AbstractProblem N) (hN : 1 < N)
    (isAccepting : Fin (N + 1) → Bool) (r : ℕ) (source target : ValidCode N)
    (hAcc : isAccepting target.val = true)
    (hReach : ReachesWithin P (2 ^ r) source.val target.val) :
    Relation.ReflTransGen (zdOutcomeStep P hN isAccepting)
      (.running (zdInitial (r + 1) N hN source)) .accept := by
  obtain ⟨final, hRun, hTag, hVal⟩ :=
    savitch_abstract_completeness P hN r source target hReach
  have hInitUntagged : (zdInitial (r + 1) N hN source).tag (Fin.last r).castSucc = false := by
    simp [zdInitial]
  have hFinalAcc : isAccepting (final.x (Fin.last r).castSucc) = true := by
    rw [hVal]
    exact hAcc
  exact zdStep_tagged_accepting_reaches_accept P hN isAccepting (Fin.last r).castSucc
    hRun hInitUntagged hTag hFinalAcc

/-- The accepting abstract machine terminates from every configuration in either
`.accept` or `.reject`. -/
theorem zdAcceptingStep_terminates (P : AbstractProblem N) (hN : 1 < N)
    (isAccepting : Fin (N + 1) → Bool) (r : ℕ) (cfg : ZDConfig r N) :
    ∃ res : ZDOutcome r N, (res = .accept ∨ res = .reject) ∧
      Relation.ReflTransGen (zdOutcomeStep P hN isAccepting) (.running cfg) res := by
  induction cfg using (InvImage.wf zdMeasure (zdMeasure_wellFounded r)).induction with
  | h current ih =>
    cases hStep : zdAcceptingStep P hN isAccepting current with
    | accept =>
      exact ⟨.accept, Or.inl rfl, Relation.ReflTransGen.single hStep⟩
    | reject =>
      exact ⟨.reject, Or.inr rfl, Relation.ReflTransGen.single hStep⟩
    | running next =>
      have hZd : zdStep P hN current = some next :=
        zdAcceptingStep_running_eq_zdStep P hN isAccepting hStep
      have hDec : zdMeasure next < zdMeasure current :=
        zdStep_decreases_measure P hN current next hZd
      obtain ⟨res, hRes, hRest⟩ := ih next hDec
      exact ⟨res, hRes, Relation.ReflTransGen.head hStep hRest⟩

end SavitchLemma

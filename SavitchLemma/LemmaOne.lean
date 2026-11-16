module

public import SavitchLemma.Termination

@[expose] public section

/-!
# Lemma 1: incrementing a register

This module states the two outcomes in the paper using zero-based working
registers.  The target register is `j`; its initial prefix consists of indices
`k ≤ j`.
-/

namespace SavitchLemma

/-- The initial prefix shape for Lemma 1. -/
def LemmaOnePrefix (hN : 1 < N) (cfg : ZDConfig r N) (j : Fin r) : Prop :=
  ∀ k : Fin r, k.val ≤ j.val →
    cfg.x k.castSucc = firstCode N hN ∧ cfg.tag k.castSucc = false

/-- Before the target outcome, the target register is below its requested code
and all higher registers retain their initial contents. -/
def LemmaOneSafe (initial : ZDConfig r N) (j : Fin r) (target : Fin (N + 1))
    (cfg : ZDConfig r N) : Prop :=
  (cfg.x j.castSucc).val < target.val ∧
    ∀ i : Fin (r + 1), j.val < i.val →
      cfg.x i = initial.x i ∧ cfg.tag i = initial.tag i

/-- Outcome (2): the requested code occupies register `j`, with the prefix
reset and the suffix unchanged. -/
def LemmaOneOutcomeA (hN : 1 < N) (initial : ZDConfig r N) (j : Fin r)
    (target : Fin (N + 1)) (cfg : ZDConfig r N) : Prop :=
  cfg.x j.castSucc = target ∧ cfg.tag j.castSucc = false ∧
    (∀ k : Fin r, k.val < j.val →
      cfg.x k.castSucc = firstCode N hN ∧ cfg.tag k.castSucc = false) ∧
    (∀ i : Fin (r + 1), j.val < i.val →
      cfg.x i = initial.x i ∧ cfg.tag i = initial.tag i)

/-- Outcome (3): the least initially untagged suffix register is tagged, after
resetting the prefix to its left. -/
def LemmaOneOutcomeB (hN : 1 < N) (initial : ZDConfig r N) (j : Fin r)
    (cfg : ZDConfig r N) : Prop :=
  ∃ q : Fin r, j.val < q.val ∧ initial.tag q.castSucc = false ∧
    (∀ k : Fin r, j.val < k.val → k.val < q.val →
      initial.tag k.castSucc = true) ∧
    cfg.x q.castSucc = initial.x q.castSucc ∧ cfg.tag q.castSucc = true ∧
    (∀ k : Fin r, k.val < q.val →
      cfg.x k.castSucc = firstCode N hN ∧ cfg.tag k.castSucc = false) ∧
    (∀ i : Fin (r + 1), q.val < i.val →
      cfg.x i = initial.x i ∧ cfg.tag i = initial.tag i)

/-- Either of the two conclusions of Savitch's Lemma 1. -/
def LemmaOneOutcome (hN : 1 < N) (initial : ZDConfig r N) (j : Fin r)
    (target : Fin (N + 1)) (cfg : ZDConfig r N) : Prop :=
  LemmaOneOutcomeA hN initial j target cfg ∨ LemmaOneOutcomeB hN initial j cfg

/-- Initially, the target is either already the first code (Outcome A), or the
configuration satisfies the progress invariant. -/
theorem lemmaOne_initial (hN : 1 < N) (initial : ZDConfig r N) (j : Fin r)
    (target : Fin (N + 1)) (hPrefix : LemmaOnePrefix hN initial j)
    (hTarget : 0 < target.val) :
    LemmaOneOutcomeA hN initial j target initial ∨
      LemmaOneSafe initial j target initial := by
  by_cases hOne : target.val = 1
  · left
    have hAtJ := hPrefix j le_rfl
    rcases hAtJ with ⟨hValue, hTag⟩
    have hTargetEq : target = firstCode N hN := by
      apply Fin.ext
      simpa [firstCode] using hOne
    refine ⟨hValue.trans hTargetEq.symm, hTag, ?_, ?_⟩
    · intro k hk
      exact hPrefix k (Nat.le_of_lt hk)
    · intro i hi
      exact ⟨rfl, rfl⟩
  · right
    have hAtJ := (hPrefix j le_rfl).1
    have hFirstLt : 1 < target.val := by omega
    refine ⟨?_, ?_⟩
    · rw [hAtJ]
      simp [firstCode]
      exact hFirstLt
    · intro i hi
      exact ⟨rfl, rfl⟩

/-- Updating at or to the left of the target preserves the progress invariant. -/
theorem lemmaOne_safe_after_update (hN : 1 < N) (initial cfg : ZDConfig r N)
    (j k : Fin r) (target value : Fin (N + 1)) (newTag : Bool)
    (hSafe : LemmaOneSafe initial j target cfg)
    (hSelected : k.val = j.val → value = cfg.x k.castSucc) (hk : k.val ≤ j.val) :
    LemmaOneSafe initial j target (updateAndReset hN cfg k value newTag) := by
  constructor
  · by_cases hEq : k.val = j.val
    · have hIndex : k = j := Fin.ext hEq
      have hSelectedValue : value = cfg.x j.castSucc := by
        simpa [hIndex] using hSelected hEq
      subst k
      obtain ⟨hValue, _⟩ := updateAndReset_at_current hN cfg j value newTag
      rw [hValue, hSelectedValue]
      exact hSafe.1
    · have hkj : k.val < j.val := by omega
      obtain ⟨hValue, _⟩ :=
        updateAndReset_at_after hN cfg k value newTag j.castSucc hkj
      rw [hValue]
      exact hSafe.1
  · intro i hi
    have hki : k.val < i.val := by omega
    obtain ⟨hValue, hTag⟩ := updateAndReset_at_after hN cfg k value newTag i hki
    rw [hValue, hTag]
    exact hSafe.2 i hi

/-- A D3 update at the target register produces Outcome A when it writes the
requested code. -/
theorem lemmaOne_outcomeA_after_update (hN : 1 < N) (initial cfg : ZDConfig r N)
    (j : Fin r) (target value : Fin (N + 1)) (hSafe : LemmaOneSafe initial j target cfg)
    (hValue : value = target) :
    LemmaOneOutcomeA hN initial j target (updateAndReset hN cfg j value false) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (updateAndReset_at_current hN cfg j value false).1 |>.trans hValue
  · exact (updateAndReset_at_current hN cfg j value false).2
  · intro k hk
    have hBefore : k.castSucc.val < j.val := by simpa using hk
    exact updateAndReset_at_before hN cfg j value false k.castSucc hBefore
  · intro i hi
    obtain ⟨hValue', hTag'⟩ := updateAndReset_at_after hN cfg j value false i hi
    rw [hValue', hTag']
    exact hSafe.2 i hi

/-- A successful D2 update strictly to the right of the target yields Outcome B
for the least initially untagged suffix register. -/
theorem lemmaOne_outcomeB_after_update (hN : 1 < N) (initial cfg : ZDConfig r N)
    (j k : Fin r) (target : Fin (N + 1)) (hSafe : LemmaOneSafe initial j target cfg)
    (hjk : j.val < k.val) (hFind : firstUntagged cfg = some k) :
    LemmaOneOutcomeB hN initial j
      (updateAndReset hN cfg k (cfg.x k.castSucc) true) := by
  have hFindFacts := (firstUntagged_eq_some_iff cfg k).mp hFind
  have hInitialTag : initial.tag k.castSucc = false := by
    calc
      initial.tag k.castSucc = cfg.tag k.castSucc :=
        (hSafe.2 k.castSucc (by simpa using hjk)).2.symm
      _ = false := hFindFacts.1
  refine ⟨k, hjk, hInitialTag, ?_, ?_, ?_, ?_, ?_⟩
  · intro l hjl hlk
    have hlkFin : l < k := by simpa using hlk
    have hlTag := hFindFacts.2 l hlkFin
    calc
      initial.tag l.castSucc = cfg.tag l.castSucc :=
        (hSafe.2 l.castSucc (by simpa using hjl)).2.symm
      _ = true := hlTag
  · have hValue := (hSafe.2 k.castSucc (by simpa using hjk)).1
    exact (updateAndReset_at_current hN cfg k (cfg.x k.castSucc) true).1 |>.trans hValue
  · exact (updateAndReset_at_current hN cfg k (cfg.x k.castSucc) true).2
  · intro l hlk
    have hlkFin : l.castSucc.val < k.val := by simpa using hlk
    exact updateAndReset_at_before hN cfg k (cfg.x k.castSucc) true l.castSucc hlkFin
  · intro i hik
    obtain ⟨hValue, hTag⟩ :=
      updateAndReset_at_after hN cfg k (cfg.x k.castSucc) true i hik
    rw [hValue, hTag]
    exact hSafe.2 i (by omega)

/-- D3 either reaches Outcome A at the target register or preserves the safe
progress invariant. -/
theorem lemmaOne_backtrack_progress (hN : 1 < N)
    (initial cfg : ZDConfig r N) (j : Fin r) (target : Fin (N + 1))
    (next : ZDConfig r N) (hSafe : LemmaOneSafe initial j target cfg)
    (hBack : zdBacktrack hN cfg = some next) :
    LemmaOneOutcomeA hN initial j target next ∨
      LemmaOneOutcomeB hN initial j next ∨ LemmaOneSafe initial j target next := by
  rcases zdBacktrack_selected_shape hN cfg next hBack with
    ⟨k, hFind, hPrefixMax, hLt, hEq⟩
  subst next
  have hNotJltK : ¬ j.val < k.val := by
    intro hjk
    have hMax := hPrefixMax j (by simpa using hjk)
    have hMaxVal : (cfg.x j.castSucc).val = N := by
      have h := congrArg Fin.val hMax
      simpa [maxCode] using h
    have hTargetLe : target.val ≤ N := Nat.le_of_lt_succ target.isLt
    have hBelow : (cfg.x j.castSucc).val < N := lt_of_lt_of_le hSafe.1 hTargetLe
    omega
  have hkLe : k.val ≤ j.val := Nat.le_of_not_gt hNotJltK
  by_cases hEqIndex : k.val = j.val
  · have hk : k = j := Fin.ext hEqIndex
    subst k
    let newValue : Fin (N + 1) :=
      ⟨(cfg.x j.castSucc).val + 1, Nat.succ_lt_succ hLt⟩
    have hNewLe : (cfg.x j.castSucc).val + 1 ≤ target.val := Nat.succ_le_of_lt hSafe.1
    by_cases hTargetEq : (cfg.x j.castSucc).val + 1 = target.val
    · left
      have hValueEq : newValue = target := by
        apply Fin.ext
        exact hTargetEq
      exact lemmaOne_outcomeA_after_update hN initial cfg j target newValue hSafe hValueEq
    · right
      right
      have hNewLt : (cfg.x j.castSucc).val + 1 < target.val := by omega
      refine ⟨?_, ?_⟩
      · rw [(updateAndReset_at_current hN cfg j newValue false).1]
        exact hNewLt
      · intro i hi
        obtain ⟨hValue, hTag⟩ := updateAndReset_at_after hN cfg j newValue false i hi
        rw [hValue, hTag]
        exact hSafe.2 i hi
  · right
    right
    have hKlt : k.val < j.val := by omega
    exact lemmaOne_safe_after_update hN initial cfg j k target
      ⟨(cfg.x k.castSucc).val + 1, Nat.succ_lt_succ hLt⟩ false hSafe
      (by intro heq; omega) hkLe

/-- Every machine step either realizes one of Lemma 1's outcomes or preserves
the progress invariant. -/
theorem lemmaOne_step_progress (P : AbstractProblem N) (hN : 1 < N)
    (initial cfg : ZDConfig r N) (j : Fin r) (target : Fin (N + 1))
    (next : ZDConfig r N) (hSafe : LemmaOneSafe initial j target cfg)
    (hStep : zdStep P hN cfg = some next) :
    LemmaOneOutcomeA hN initial j target next ∨
      LemmaOneOutcomeB hN initial j next ∨ LemmaOneSafe initial j target next := by
  classical
  unfold zdStep at hStep
  cases hFind : firstUntagged cfg with
  | none =>
    have hBack : zdBacktrack hN cfg = some next := by simpa [hFind] using hStep
    exact lemmaOne_backtrack_progress hN initial cfg j target next hSafe hBack
  | some k =>
    by_cases hTest : ∃ i : Fin (r + 1), cfg.tag i = true ∧
        (cfg.x i = cfg.x k.castSucc ∨ P.step (cfg.x i) (cfg.x k.castSucc))
    · have hEq : updateAndReset hN cfg k (cfg.x k.castSucc) true = next :=
        Option.some.inj (by simpa [hFind, hTest] using hStep)
      subst next
      by_cases hJltK : j.val < k.val
      · exact Or.inr (Or.inl <| lemmaOne_outcomeB_after_update hN initial cfg j k
          target hSafe hJltK hFind)
      · right
        right
        exact lemmaOne_safe_after_update hN initial cfg j k target
          (cfg.x k.castSucc) true hSafe (by intro _; rfl) (Nat.le_of_not_gt hJltK)
    · have hBack : zdBacktrack hN cfg = some next := by
        simpa [hFind, hTest] using hStep
      exact lemmaOne_backtrack_progress hN initial cfg j target next hSafe hBack

/-- An outcome of Lemma 1 has occurred somewhere along the run from `initial`. -/
def LemmaOneHasOutcome (P : AbstractProblem N) (hN : 1 < N)
    (initial : ZDConfig r N) (j : Fin r) (target : Fin (N + 1)) : Prop :=
  ∃ eventCfg,
    Relation.ReflTransGen (fun a b : ZDConfig r N => zdStep P hN a = some b)
      initial eventCfg ∧ LemmaOneOutcome hN initial j target eventCfg

/-- Along a finite run, either a Lemma 1 outcome has already appeared or the
progress invariant still holds. -/
theorem lemmaOne_run_progress (P : AbstractProblem N) (hN : 1 < N)
    (initial : ZDConfig r N) (j : Fin r) (target : Fin (N + 1))
    {cfg : ZDConfig r N} (hStart :
      LemmaOneOutcome hN initial j target initial ∨ LemmaOneSafe initial j target initial)
    (hRun : Relation.ReflTransGen
      (fun a b : ZDConfig r N => zdStep P hN a = some b) initial cfg) :
    LemmaOneHasOutcome P hN initial j target ∨ LemmaOneSafe initial j target cfg := by
  induction hRun with
  | refl =>
    rcases hStart with hOutcome | hSafe
    · exact Or.inl ⟨initial, Relation.ReflTransGen.refl, hOutcome⟩
    · exact Or.inr hSafe
  | @tail prev current hRun hStep ih =>
    rcases ih with hReached | hSafe
    · exact Or.inl hReached
    · rcases lemmaOne_step_progress P hN initial prev j target current hSafe hStep with
        hA | hOther
      · exact Or.inl ⟨current, Relation.ReflTransGen.tail hRun hStep, Or.inl hA⟩
      · rcases hOther with hB | hSafe'
        · exact Or.inl ⟨current, Relation.ReflTransGen.tail hRun hStep,
            Or.inr hB⟩
        · exact Or.inr hSafe'

/-- Savitch's Lemma 1 for the abstract register machine: starting with a prefix
of first-code, untagged registers, the requested value is eventually placed in
the last prefix register with its tag clear, unless an initially untagged
suffix register is tagged first. -/
theorem lemma_one (P : AbstractProblem N) (hN : 1 < N)
    (initial : ZDConfig r N) (j : Fin r) (target : Fin (N + 1))
    (hPrefix : LemmaOnePrefix hN initial j) (hTarget : 0 < target.val) :
    ∃ final,
      Relation.ReflTransGen (fun a b : ZDConfig r N => zdStep P hN a = some b)
        initial final ∧ LemmaOneOutcome hN initial j target final := by
  obtain ⟨stuck, hRun, hStop⟩ := zdStep_reaches_stuck P hN r initial
  have hInit := lemmaOne_initial hN initial j target hPrefix hTarget
  have hStart : LemmaOneOutcome hN initial j target initial ∨
      LemmaOneSafe initial j target initial := by
    rcases hInit with hA | hSafe
    · exact Or.inl (Or.inl hA)
    · exact Or.inr hSafe
  rcases lemmaOne_run_progress P hN initial j target hStart hRun with hOutcome | hSafe
  · rcases hOutcome with ⟨eventCfg, hEventRun, hEvent⟩
    exact ⟨eventCfg, hEventRun, hEvent⟩
  · have hMax := zdStep_none_forces_max P hN stuck hStop j
    have hMaxVal : (stuck.x j.castSucc).val = N := by
      have h := congrArg Fin.val hMax
      simpa [maxCode] using h
    have hTargetLe : target.val ≤ N := Nat.le_of_lt_succ target.isLt
    have hTargetStuck : (stuck.x j.castSucc).val < target.val := hSafe.1
    have hFalse : False := by omega
    exact hFalse.elim

end SavitchLemma

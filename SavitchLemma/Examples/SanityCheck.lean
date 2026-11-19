module

public import SavitchLemma.MainTheorem

@[expose] public section

/-!
# Non-vacuity sanity check for `savitch_theorem_one_full`

Constructs a concrete 2-state, 1-work-tape nondeterministic Turing machine
accepting the non-trivial language `A n _ := 0 < n` (non-empty `Bool` strings)
within space `L n := n + 1`, and applies `savitch_theorem_one_full` to verify
that all hypotheses of Theorem 1 are satisfiable.
-/

namespace SavitchLemma.Examples

/-- Two-state NTM over `Bool` inputs that moves its input head right from the
left end-marker and accepts iff position `1` holds a symbol (i.e., `0 < n`). -/
def nonEmptyNTM : MultitapeNTM Bool Bool Unit 1 where
  startState := false
  blank := ()
  accepting := fun q => q = true
  transitions q inSym _ :=
    match q, inSym with
    | false, .leftEnd =>
      [⟨false, .right, fun _ => (), fun _ => .stay⟩]
    | false, .symbol _ =>
      [⟨true, .stay, fun _ => (), fun _ => .stay⟩]
    | _, _ => []

private theorem n_le_two_pow_succ (n : ℕ) : n ≤ 2 ^ (n + 1) := by
  induction n with
  | zero => decide
  | succ k ih =>
    calc k + 1 ≤ 2 ^ (k + 1) + 1 := Nat.add_le_add_right ih 1
      _ ≤ 2 ^ (k + 1) + 2 ^ (k + 1) := Nat.add_le_add_left (Nat.one_le_pow _ _ (by decide)) _
      _ = 2 ^ (k + 2) := by rw [show 2 ^ (k + 2) = 2 ^ (k + 1) * 2 from Nat.pow_succ ..]; omega

theorem nonEmptyNTM_accepts :
    nonEmptyNTM.AcceptsLanguageWithinSpace (fun n (_ : Fin n → Bool) => 0 < n) (fun n => n + 1) := by
  constructor
  · intro n input hn
    let c0 : OneSidedTMConfig Bool Unit 1 n := nonEmptyNTM.oneSidedInitialConfig
    let c1 : OneSidedTMConfig Bool Unit 1 n :=
      { state := false, inputHead := ⟨1, by omega⟩, workTapes := fun _ => ⟨fun _ => (), 0⟩ }
    let c2 : OneSidedTMConfig Bool Unit 1 n :=
      { state := true, inputHead := ⟨1, by omega⟩, workTapes := fun _ => ⟨fun _ => (), 0⟩ }
    have h01 : nonEmptyNTM.oneSidedStep input c0 c1 := by
      refine ⟨⟨false, .right, fun _ => (), fun _ => .stay⟩, ?_, rfl, ⟨1, by omega⟩, ?_, rfl, ?_⟩
      · simp [nonEmptyNTM, c0, MultitapeNTM.oneSidedInitialConfig, readInput]
      · simp [c0, MultitapeNTM.oneSidedInitialConfig, moveHead]
      · intro _; simp [c0, c1, MultitapeNTM.oneSidedInitialConfig, OneSidedTape.updateAndMove, moveOneSidedHead]
    have h12 : nonEmptyNTM.oneSidedStep input c1 c2 := by
      refine ⟨⟨true, .stay, fun _ => (), fun _ => .stay⟩, ?_, rfl, ⟨1, by omega⟩, ?_, rfl, ?_⟩
      · have hnNe : n ≠ 0 := by omega
        simp [nonEmptyNTM, c1, readInput, hnNe]
      · simp [c1, moveHead]
      · intro _; simp [c1, c2, OneSidedTape.updateAndMove, moveOneSidedHead]
    have hW0 : c0.HeadsWithin (n + 1) := fun _ => by simp [c0, MultitapeNTM.oneSidedInitialConfig]
    have hW1 : c1.HeadsWithin (n + 1) := fun _ => by simp [c1]
    have hW2 : c2.HeadsWithin (n + 1) := fun _ => by simp [c2]
    refine ⟨c2, Relation.ReflTransGen.tail (Relation.ReflTransGen.single ⟨h01, hW0, hW1⟩) ⟨h12, hW1, hW2⟩, rfl⟩
  · intro n input ⟨final, hRun, hAcc⟩
    by_contra hZero
    have hn : n = 0 := by omega
    subst hn
    have hStuck : ∀ c : OneSidedTMConfig Bool Unit 1 0,
        c.state = false → ∀ next, nonEmptyNTM.oneSidedStep input c next → next.state = false := by
      intro c hc next ⟨a, ha, hNextState, _⟩
      have hIn : c.inputHead.val = 0 ∨ c.inputHead.val = 1 := by omega
      rcases hIn with h0 | h1
      · simp [nonEmptyNTM, hc, readInput, h0] at ha
        subst ha; exact hNextState
      · simp [nonEmptyNTM, hc, readInput, h1] at ha
    have hFalse : final.state = false := by
      have hInit : (nonEmptyNTM.oneSidedInitialConfig (n := 0)).state = false := rfl
      clear hAcc
      induction hRun with
      | refl => exact hInit
      | tail _ hStep ih => exact hStuck _ ih _ hStep
    rw [hFalse] at hAcc
    cases hAcc

/-- Non-vacuity check: `savitch_theorem_one_full` applies to `nonEmptyNTM`. -/
theorem nonEmpty_savitch_sanity :
    ∃ (QD : Type) (_ : Fintype QD) (D : MultitapeDTM QD Bool SimSym 5)
      (L' : ℕ → ℕ) (C : ℕ),
      D.AcceptsLanguageWithinSpace (fun n (_ : Fin n → Bool) => 0 < n) L' ∧
      ∀ n, L' n ≤ C * ((n + 1) + 1) ^ 2 :=
  savitch_theorem_one_full nonEmptyNTM (fun n _ => 0 < n) (fun n => n + 1)
    (fun n => ⟨by omega, n_le_two_pow_succ n⟩) nonEmptyNTM_accepts

end SavitchLemma.Examples

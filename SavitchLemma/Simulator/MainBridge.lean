module

public import SavitchLemma.Simulator.SavitchDriver

@[expose] public section

/-!
# Bridge from the simulator component to a `MultitapeDTM`

`savitchSimulator M` assumes its tapes are already prepared (ruler `1^S` on `tRuler`,
`[leftMark]` elsewhere). A `MultitapeDTM` starts on blank tapes, so we compose with an
abstract *prefix* component `P` that builds those tapes from blank (for measurable `S`
this is a ruler-writing run of a measuring machine; constructing it is a separate step).
The result is compiled with `TMComponent.toDTM`, giving a deterministic machine that
accepts within space `B` iff `M` accepts within capacity `S`, and never accepts otherwise.
-/

namespace SavitchLemma

/-- Prefix hypothesis: from blank tapes (all heads `0`), `P` reaches its exit with every
head below `B`, leaving the tapes in the clean state expected by `savitchSimulator`. -/
def PrefixPrepares {QP InputAlphabet : Type*} {n : ℕ}
    (P : TMComponent QP InputAlphabet SimSym 5 Unit) (input : Fin n → InputAlphabet)
    (S B : ℕ) (initTapes : Fin 5 → OneSidedTape SimSym) (inHead : Fin (n + 2)) : Prop :=
  P.ReachesExit input (fun _ => B) (fun _ => ⟨fun _ => .blank, 0⟩) ⟨0, by omega⟩ ()
    initTapes inHead ∧
  TapeMatches (initTapes tRuler) (.leftMark :: List.replicate S (.bit true) ++ [.endMark]) 1 ∧
  TapeMatches (initTapes tRegs) [.leftMark] 1 ∧
  TapeMatches (initTapes tArgA) [.leftMark] 1 ∧
  TapeMatches (initTapes tArgB) [.leftMark] 1 ∧
  TapeMatches (initTapes tScratch) [.leftMark] 1

/-- Deterministic machine obtained from a prefix `P` followed by the Savitch simulator. -/
noncomputable def savitchDTM {QP Q InputAlphabet Γ : Type*} {k : ℕ}
    [Fintype QP] [Fintype Q] [Fintype InputAlphabet] [Fintype Γ]
    (P : TMComponent QP InputAlphabet SimSym 5 Unit)
    (M : MultitapeNTM Q InputAlphabet Γ k) :=
  (P.seq (savitchSimulator M)).toDTM SimSym.blank

/-- Correctness of the compiled deterministic machine for a fixed input: if `M` accepts
within capacity `S`, `savitchDTM P M` accepts within space `B`; otherwise it accepts
nowhere. -/
theorem savitchDTM_correct {QP Q InputAlphabet Γ : Type*} {k n : ℕ}
    [Fintype QP] [Fintype Q] [Fintype InputAlphabet] [Fintype Γ]
    (P : TMComponent QP InputAlphabet SimSym 5 Unit)
    (M : MultitapeNTM Q InputAlphabet Γ k) (input : Fin n → InputAlphabet)
    (S B : ℕ) (hS : 1 ≤ S) (hInput : n ≤ 2 ^ S)
    (hBoundR : S + 2 ≤ B)
    (hBoundRegs : 1 + (configBitWidth Q Γ k S + 1) * (configBitWidth Q Γ k S + 2) +
      (configBitWidth Q Γ k S + 3) ≤ B)
    (hBoundA : configBitWidth Q Γ k S + 2 ≤ B)
    (hBoundB : configBitWidth Q Γ k S + 2 ≤ B)
    (hBoundS : S + 4 ≤ B)
    {initTapes : Fin 5 → OneSidedTape SimSym} {inHead : Fin (n + 2)}
    (hPrep : PrefixPrepares P input S B initTapes inHead) :
    (M.AcceptsWithinCapacity input S (by omega) →
      (savitchDTM P M).AcceptsOneSidedWithin input B) ∧
    (¬ M.AcceptsWithinCapacity input S (by omega) →
      ¬ (savitchDTM P M).AcceptsOneSided input) := by
  obtain ⟨hP, hMR, hMReg, hMA, hMB, hMS⟩ := hPrep
  obtain ⟨res, finalTapes, finalInHead, hRun, hIff⟩ :=
    savitchSimulator_reachesExit M input (fun _ => B) S hS hInput hBoundR hBoundRegs
      hBoundA hBoundB hBoundS initTapes inHead hMR hMReg hMA hMB hMS
  have hReach := P.seq_reachesExit (savitchSimulator M) input (fun _ => B) hP hRun
  cases res with
  | true =>
    refine ⟨fun _ => ?_, fun hNot => absurd (hIff.1 rfl) hNot⟩
    exact TMComponent.toDTM_acceptsWithin _ SimSym.blank input (fun _ => B) B
      (fun _ => le_rfl) hReach
  | false =>
    refine ⟨fun hAcc => by simpa using hIff.2 hAcc, fun _ => ?_⟩
    exact TMComponent.toDTM_rejects _ SimSym.blank input (fun _ => B) hReach

end SavitchLemma

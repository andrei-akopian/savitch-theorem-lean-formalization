module

public import SavitchLemma.Simulator.Initialize
public import SavitchLemma.Simulator.StepDriver

@[expose] public section

/-!
# Top-Level Savitch Simulator Driver (D0–D3)

Composes `initSavitchTapes` (D0) with `loopWithState () (fun _ => zdConcreteStep M)` (D1–D3)
to obtain `savitchSimulator M`, and proves soundness and completeness against
`M.AcceptsWithinCapacity input S`.
-/

namespace SavitchLemma

/-- Full 5-tape deterministic Savitch simulator for a multitape NTM `M`. -/
noncomputable def savitchSimulator {Q InputAlphabet Γ : Type*} {k : ℕ}
    [Fintype Q] [Fintype InputAlphabet] [Fintype Γ]
    (M : MultitapeNTM Q InputAlphabet Γ k) :=
  (initSavitchTapes M).seq (loopWithState () fun _ => zdConcreteStep M)

private theorem zdOutcomeStep_deterministic_terminal {r N : ℕ}
    (P : AbstractProblem N) (hN : 1 < N) (isAccepting : Fin (N + 1) → Bool)
    {s t₁ t₂ : ZDOutcome r N}
    (h₁ : Relation.ReflTransGen (zdOutcomeStep P hN isAccepting) s t₁)
    (h₂ : Relation.ReflTransGen (zdOutcomeStep P hN isAccepting) s t₂)
    (ht₁ : t₁ = .accept ∨ t₁ = .reject)
    (ht₂ : t₂ = .accept ∨ t₂ = .reject) :
    t₁ = t₂ := by
  induction h₁ using Relation.ReflTransGen.head_induction_on with
  | refl =>
    cases h₂ using Relation.ReflTransGen.head_induction_on with
    | refl => rfl
    | @head b _ hStep _ =>
      rcases ht₁ with rfl | rfl <;> simp [zdOutcomeStep] at hStep
  | @head a b hStep₁ _ ih =>
    cases h₂ using Relation.ReflTransGen.head_induction_on with
    | refl =>
      rcases ht₂ with rfl | rfl <;> simp [zdOutcomeStep] at hStep₁
    | head hStep₂ hRest₂ =>
      cases a with
      | accept => simp [zdOutcomeStep] at hStep₁
      | reject => simp [zdOutcomeStep] at hStep₁
      | running cfg =>
        simp only [zdOutcomeStep] at hStep₁ hStep₂
        have hEq := hStep₁.symm.trans hStep₂
        subst hEq
        exact ih hRest₂

private theorem loop_lift_unit {Q InputAlphabet Γ : Type*} {k n : ℕ}
    (body : Unit → TMComponent Q InputAlphabet Γ k (Unit ⊕ Bool))
    (input : Fin n → InputAlphabet) (bound : Fin k → ℕ)
    (a b : OneSidedTMConfig (Q ⊕ (Unit ⊕ Bool)) Γ k n)
    (hR : Relation.ReflTransGen
      (fun x y => (body ()).CompStep input x y ∧
        (∀ t, (x.workTapes t).head < bound t) ∧
        (∀ t, (y.workTapes t).head < bound t)) a b) :
    Relation.ReflTransGen
      (fun x y => (loopWithState () body).CompStep input x y ∧
        (∀ t, (x.workTapes t).head < bound t) ∧
        (∀ t, (y.workTapes t).head < bound t))
      ⟨match a.state with
       | .inl q => .inl ((), q)
       | .inr (.inl st') => .inl (st', (body st').start)
       | .inr (.inr e) => .inr e, a.inputHead, a.workTapes⟩
      ⟨match b.state with
       | .inl q => .inl ((), q)
       | .inr (.inl st') => .inl (st', (body st').start)
       | .inr (.inr e) => .inr e, b.inputHead, b.workTapes⟩ := by
  induction hR with
  | refl => exact Relation.ReflTransGen.refl
  | @tail prev curr _ hS ih =>
    rcases hS.1 with ⟨q, hState, hNext, ihC, hInM, hInC, hTps⟩
    refine Relation.ReflTransGen.tail ih ⟨?_, hS.2.1, hS.2.2⟩
    have hScanned :
        ({ state := Sum.inl ((), q), inputHead := prev.inputHead,
           workTapes := prev.workTapes } :
          OneSidedTMConfig ((Unit × Q) ⊕ Bool) Γ k n).scannedWork =
        prev.scannedWork := rfl
    refine ⟨((), q), by simp [hState], ?_, ihC, ?_, hInC, ?_⟩
    · simp only [loopWithState, TMAction.mapState, hState, hScanned, hNext]
      cases ((body ()).step q (readInput input prev.inputHead) prev.scannedWork).nextState with
      | inl q' => rfl
      | inr e => cases e <;> rfl
    · simpa [loopWithState, TMAction.mapState, hState, hScanned] using hInM
    · simpa [loopWithState, TMAction.mapState, hState, hScanned] using hTps

/-- Running the D1–D3 loop from a valid `ZDConfig` terminates with `true` iff
`zdOutcomeStep` reaches `.accept`, and on `false` leaves `tRuler` intact and
`tRegs`/`tArgA`/`tArgB`/`tScratch` clean (with no `.blank` inside `tRegs`). -/
theorem savitchLoop_reachesExit_clean {Q InputAlphabet Γ : Type*} {k n : ℕ}
    [Fintype Q] [Fintype InputAlphabet] [Fintype Γ]
    (M : MultitapeNTM Q InputAlphabet Γ k)
    (input : Fin n → InputAlphabet) (bound : Fin 5 → ℕ)
    (S : ℕ) (hS : 1 ≤ S) (hInput : n ≤ 2 ^ S)
    (r : ℕ) (hr : 1 ≤ r)
    (hBoundR : S + 2 ≤ bound tRuler)
    (hBoundRegs : 1 + r * (configBitWidth Q Γ k S + 2) +
      (configBitWidth Q Γ k S + 3) ≤ bound tRegs)
    (hBoundA : configBitWidth Q Γ k S + 2 ≤ bound tArgA)
    (hBoundB : configBitWidth Q Γ k S + 2 ≤ bound tArgB)
    (hBoundS : S + 4 ≤ bound tScratch)
    (cfg : ZDConfig r (2 ^ configBitWidth Q Γ k S - 1))
    (hValid : ValidZDTags Q Γ n S cfg)
    (initTapes : Fin 5 → OneSidedTape SimSym) (inHead : Fin (n + 2))
    (hMatchR : TapeMatches (initTapes tRuler)
      (.leftMark :: List.replicate S (.bit true) ++ [.endMark]) 1)
    (hMatchRegs : TapeMatches (initTapes tRegs)
      (zdRegsContents (configBitWidth Q Γ k S) cfg) 1)
    (hMatchA : TapeMatches (initTapes tArgA) [.leftMark] 1)
    (hMatchB : TapeMatches (initTapes tArgB) [.leftMark] 1)
    (hMatchS : TapeMatches (initTapes tScratch) [.leftMark] 1) :
    let W := configBitWidth Q Γ k S
    let hN : 1 < 2 ^ W - 1 := one_lt_two_pow_sub_one' (two_le_configBitWidth' Q Γ k S)
    ∃ (res : Bool) (finalTapes : Fin 5 → OneSidedTape SimSym) (finalInHead : Fin (n + 2)),
      (loopWithState () fun _ => zdConcreteStep M).ReachesExit
        input bound initTapes inHead res finalTapes finalInHead ∧
      Relation.ReflTransGen (zdOutcomeStep (bitProblem M input S) hN (bitIsAccepting M n S))
        (.running cfg) (if res then .accept else .reject) ∧
      (res = false →
        TapeMatches (finalTapes tRuler)
          (.leftMark :: List.replicate S (.bit true) ++ [.endMark]) 1 ∧
        (∃ prefixSyms : List SimSym,
          (∀ s ∈ prefixSyms, s ≠ .endMark) ∧
          prefixSyms.length + 2 ≤ 1 + r * (W + 2) + (W + 3) ∧
          TapeMatches (finalTapes tRegs) (.leftMark :: prefixSyms ++ [.endMark]) 1) ∧
        TapeMatches (finalTapes tArgA) [.leftMark] 1 ∧
        TapeMatches (finalTapes tArgB) [.leftMark] 1 ∧
        TapeMatches (finalTapes tScratch) [.leftMark] 1) := by
  classical
  let W := configBitWidth Q Γ k S
  let hN : 1 < 2 ^ W - 1 := one_lt_two_pow_sub_one' (two_le_configBitWidth' Q Γ k S)
  let body := fun (_ : Unit) => zdConcreteStep M
  have hMain : ∀ cfg : ZDConfig r (2 ^ W - 1),
      ValidZDTags Q Γ n S cfg →
      ∀ tapes inHead,
        TapeMatches (tapes tRuler) (.leftMark :: List.replicate S (.bit true) ++ [.endMark]) 1 →
        TapeMatches (tapes tRegs) (zdRegsContents W cfg) 1 →
        TapeMatches (tapes tArgA) [.leftMark] 1 →
        TapeMatches (tapes tArgB) [.leftMark] 1 →
        TapeMatches (tapes tScratch) [.leftMark] 1 →
        ∃ (res : Bool) (finalTapes : Fin 5 → OneSidedTape SimSym) (finalInHead : Fin (n + 2)),
          (loopWithState () body).ReachesExit
            input bound tapes inHead res finalTapes finalInHead ∧
          Relation.ReflTransGen (zdOutcomeStep (bitProblem M input S) hN (bitIsAccepting M n S))
            (.running cfg) (if res then .accept else .reject) ∧
          (res = false →
            TapeMatches (finalTapes tRuler)
              (.leftMark :: List.replicate S (.bit true) ++ [.endMark]) 1 ∧
            (∃ prefixSyms : List SimSym,
              (∀ s ∈ prefixSyms, s ≠ .endMark) ∧
              prefixSyms.length + 2 ≤ 1 + r * (W + 2) + (W + 3) ∧
              TapeMatches (finalTapes tRegs) (.leftMark :: prefixSyms ++ [.endMark]) 1) ∧
            TapeMatches (finalTapes tArgA) [.leftMark] 1 ∧
            TapeMatches (finalTapes tArgB) [.leftMark] 1 ∧
            TapeMatches (finalTapes tScratch) [.leftMark] 1) := by
    intro cfg0
    induction cfg0 using (InvImage.wf zdMeasure (zdMeasure_wellFounded r)).induction with
    | h cur ih =>
      intro hValidCur tapes inHead hMR hMRegs hMA hMB hMS
      obtain ⟨stepRes, midTapes, midHead, hStep, hPost⟩ :=
        zdConcreteStep_reachesExit M input bound S hS hInput r hr cur hValidCur
          hBoundR hBoundRegs hBoundA hBoundB hBoundS tapes inHead hMR hMRegs hMA hMB hMS
      have hLifted := loop_lift_unit body input bound _ _ hStep
      cases hOut : zdAcceptingStep (bitProblem M input S) hN (bitIsAccepting M n S) cur with
      | accept =>
        rw [hOut] at hPost
        subst hPost
        exact ⟨true, midTapes, midHead, hLifted, Relation.ReflTransGen.single hOut, fun h => by cases h⟩
      | reject =>
        rw [hOut] at hPost
        rcases hPost with ⟨rfl, hClean⟩
        exact ⟨false, midTapes, midHead, hLifted, Relation.ReflTransGen.single hOut, fun _ => hClean⟩
      | running next =>
        rw [hOut] at hPost
        rcases hPost with ⟨rfl, hValidNext, hR', hRegs', hA', hB', hS'⟩
        have hZd : zdStep (bitProblem M input S) hN cur = some next :=
          zdAcceptingStep_running_eq_zdStep (bitProblem M input S) hN (bitIsAccepting M n S) hOut
        have hDec : zdMeasure next < zdMeasure cur :=
          zdStep_decreases_measure (bitProblem M input S) hN cur next hZd
        obtain ⟨res, finalTapes, finalInHead, hRest, hOutcomeRest, hCleanRest⟩ :=
          ih next hDec hValidNext midTapes midHead hR' hRegs' hA' hB' hS'
        exact ⟨res, finalTapes, finalInHead, hLifted.trans hRest,
          Relation.ReflTransGen.head hOut hOutcomeRest, hCleanRest⟩
  exact hMain cfg hValid initTapes inHead hMatchR hMatchRegs hMatchA hMatchB hMatchS

/-- Running the D1–D3 loop from a valid `ZDConfig` terminates with `true` iff
`zdOutcomeStep` reaches `.accept`. -/
theorem savitchLoop_reachesExit {Q InputAlphabet Γ : Type*} {k n : ℕ}
    [Fintype Q] [Fintype InputAlphabet] [Fintype Γ]
    (M : MultitapeNTM Q InputAlphabet Γ k)
    (input : Fin n → InputAlphabet) (bound : Fin 5 → ℕ)
    (S : ℕ) (hS : 1 ≤ S) (hInput : n ≤ 2 ^ S)
    (r : ℕ) (hr : 1 ≤ r)
    (hBoundR : S + 2 ≤ bound tRuler)
    (hBoundRegs : 1 + r * (configBitWidth Q Γ k S + 2) +
      (configBitWidth Q Γ k S + 3) ≤ bound tRegs)
    (hBoundA : configBitWidth Q Γ k S + 2 ≤ bound tArgA)
    (hBoundB : configBitWidth Q Γ k S + 2 ≤ bound tArgB)
    (hBoundS : S + 4 ≤ bound tScratch)
    (cfg : ZDConfig r (2 ^ configBitWidth Q Γ k S - 1))
    (hValid : ValidZDTags Q Γ n S cfg)
    (initTapes : Fin 5 → OneSidedTape SimSym) (inHead : Fin (n + 2))
    (hMatchR : TapeMatches (initTapes tRuler)
      (.leftMark :: List.replicate S (.bit true) ++ [.endMark]) 1)
    (hMatchRegs : TapeMatches (initTapes tRegs)
      (zdRegsContents (configBitWidth Q Γ k S) cfg) 1)
    (hMatchA : TapeMatches (initTapes tArgA) [.leftMark] 1)
    (hMatchB : TapeMatches (initTapes tArgB) [.leftMark] 1)
    (hMatchS : TapeMatches (initTapes tScratch) [.leftMark] 1) :
    let W := configBitWidth Q Γ k S
    let hN : 1 < 2 ^ W - 1 := one_lt_two_pow_sub_one' (two_le_configBitWidth' Q Γ k S)
    ∃ (res : Bool) (finalTapes : Fin 5 → OneSidedTape SimSym) (finalInHead : Fin (n + 2)),
      (loopWithState () fun _ => zdConcreteStep M).ReachesExit
        input bound initTapes inHead res finalTapes finalInHead ∧
      Relation.ReflTransGen (zdOutcomeStep (bitProblem M input S) hN (bitIsAccepting M n S))
        (.running cfg) (if res then .accept else .reject) := by
  obtain ⟨res, ft, fih, h1, h2, _⟩ := savitchLoop_reachesExit_clean M input bound S hS hInput r hr
    hBoundR hBoundRegs hBoundA hBoundB hBoundS cfg hValid initTapes inHead
    hMatchR hMatchRegs hMatchA hMatchB hMatchS
  exact ⟨res, ft, fih, h1, h2⟩

/-- Main simulation theorem with clean-tape postcondition on `res = false`. -/
theorem savitchSimulator_reachesExit_clean {Q InputAlphabet Γ : Type*} {k n : ℕ}
    [Fintype Q] [Fintype InputAlphabet] [Fintype Γ]
    (M : MultitapeNTM Q InputAlphabet Γ k)
    (input : Fin n → InputAlphabet) (bound : Fin 5 → ℕ)
    (S : ℕ) (hS : 1 ≤ S) (hInput : n ≤ 2 ^ S)
    (hBoundR : S + 2 ≤ bound tRuler)
    (hBoundRegs : 1 + (configBitWidth Q Γ k S + 1) * (configBitWidth Q Γ k S + 2) +
      (configBitWidth Q Γ k S + 3) ≤ bound tRegs)
    (hBoundA : configBitWidth Q Γ k S + 2 ≤ bound tArgA)
    (hBoundB : configBitWidth Q Γ k S + 2 ≤ bound tArgB)
    (hBoundS : S + 4 ≤ bound tScratch)
    (initTapes : Fin 5 → OneSidedTape SimSym) (inHead : Fin (n + 2))
    (hMatchR : TapeMatches (initTapes tRuler)
      (.leftMark :: List.replicate S (.bit true) ++ [.endMark]) 1)
    (hMatchRegs : TapeMatches (initTapes tRegs) [.leftMark] 1)
    (hMatchA : TapeMatches (initTapes tArgA) [.leftMark] 1)
    (hMatchB : TapeMatches (initTapes tArgB) [.leftMark] 1)
    (hMatchS : TapeMatches (initTapes tScratch) [.leftMark] 1) :
    ∃ (res : Bool) (finalTapes : Fin 5 → OneSidedTape SimSym) (finalInHead : Fin (n + 2)),
      (savitchSimulator M).ReachesExit input bound initTapes inHead res finalTapes finalInHead ∧
      (res = true ↔ M.AcceptsWithinCapacity input S (by omega)) ∧
      (res = false →
        TapeMatches (finalTapes tRuler)
          (.leftMark :: List.replicate S (.bit true) ++ [.endMark]) 1 ∧
        (∃ prefixSyms : List SimSym,
          (∀ s ∈ prefixSyms, s ≠ .endMark) ∧
          prefixSyms.length + 2 ≤ 1 + (configBitWidth Q Γ k S + 1) * (configBitWidth Q Γ k S + 2) +
            (configBitWidth Q Γ k S + 3) ∧
          TapeMatches (finalTapes tRegs) (.leftMark :: prefixSyms ++ [.endMark]) 1) ∧
        TapeMatches (finalTapes tArgA) [.leftMark] 1 ∧
        TapeMatches (finalTapes tArgB) [.leftMark] 1 ∧
        TapeMatches (finalTapes tScratch) [.leftMark] 1) := by
  let W := configBitWidth Q Γ k S
  have hBoundSHead : (initTapes tScratch).head < bound tScratch := by
    rw [hMatchS.head_eq]; omega
  obtain ⟨ftR, ftReg, ftA, ftB, hInit, hMR, hMReg, hMA, hMB⟩ :=
    initSavitchTapes_reachesExit M input bound S hS
      hBoundR hBoundRegs hBoundA hBoundB initTapes inHead hBoundSHead
      hMatchR hMatchRegs hMatchA hMatchB
  let tInit := fun j =>
    if j = tRuler then ftR else if j = tRegs then ftReg
    else if j = tArgA then ftA else if j = tArgB then ftB else initTapes j
  let cfg₀ := zdInitial (W + 1) (2 ^ W - 1) (configBitWidth_gt_one_pow Q Γ k S)
    (bitEncodeConfig Q Γ (M.initialConfig (n := n) S (by omega)))
  have hValid0 : ValidZDTags Q Γ n S cfg₀ := by
    refine ⟨zdInitial_source_tag _ _ _ _, ?_⟩
    intro i hi
    have hiLast : i.val = W + 1 := by
      simpa [cfg₀, zdInitial] using hi
    have hFinEq : i = Fin.last (W + 1) := by ext; exact hiLast
    rw [hFinEq]
    exact ⟨M.initialConfig (n := n) S (by omega), zdInitial_source _ _ _ _⟩
  obtain ⟨res, finalTapes, finalInHead, hLoop, hOutcome, hClean⟩ :=
    savitchLoop_reachesExit_clean M input bound S hS hInput (W + 1) (by omega)
      hBoundR hBoundRegs hBoundA hBoundB hBoundS cfg₀ hValid0 tInit inHead
      (by simpa [tInit, tRuler] using hMR)
      (by simpa [tInit, tRuler, tRegs] using hMReg)
      (by simpa [tInit, tRuler, tRegs, tArgA] using hMA)
      (by simpa [tInit, tRuler, tRegs, tArgA, tArgB] using hMB)
      (by simpa [tInit, tRuler, tRegs, tArgA, tArgB, tScratch] using hMatchS)
  refine ⟨res, finalTapes, finalInHead,
    TMComponent.seq_reachesExit _ _ input bound hInit hLoop, ?_, hClean⟩
  constructor
  · intro hTrue
    rw [hTrue] at hOutcome
    exact bitProblem_accepting_sound M input S hS hInput (W + 1) hOutcome
  · intro hAcc
    have hAccOutcome := bitProblem_accepting_complete M input S hS hInput hAcc
    have hDet := zdOutcomeStep_deterministic_terminal
      (bitProblem M input S) (configBitWidth_gt_one_pow Q Γ k S) (bitIsAccepting M n S)
      hOutcome hAccOutcome
      (by cases res <;> simp) (Or.inl rfl)
    cases res <;> simp at hDet ⊢

/-- Main simulation theorem: from cleanly initialized tapes, `savitchSimulator M`
halts and returns `true` iff `M` accepts `input` within tape capacity `S`. -/
theorem savitchSimulator_reachesExit {Q InputAlphabet Γ : Type*} {k n : ℕ}
    [Fintype Q] [Fintype InputAlphabet] [Fintype Γ]
    (M : MultitapeNTM Q InputAlphabet Γ k)
    (input : Fin n → InputAlphabet) (bound : Fin 5 → ℕ)
    (S : ℕ) (hS : 1 ≤ S) (hInput : n ≤ 2 ^ S)
    (hBoundR : S + 2 ≤ bound tRuler)
    (hBoundRegs : 1 + (configBitWidth Q Γ k S + 1) * (configBitWidth Q Γ k S + 2) +
      (configBitWidth Q Γ k S + 3) ≤ bound tRegs)
    (hBoundA : configBitWidth Q Γ k S + 2 ≤ bound tArgA)
    (hBoundB : configBitWidth Q Γ k S + 2 ≤ bound tArgB)
    (hBoundS : S + 4 ≤ bound tScratch)
    (initTapes : Fin 5 → OneSidedTape SimSym) (inHead : Fin (n + 2))
    (hMatchR : TapeMatches (initTapes tRuler)
      (.leftMark :: List.replicate S (.bit true) ++ [.endMark]) 1)
    (hMatchRegs : TapeMatches (initTapes tRegs) [.leftMark] 1)
    (hMatchA : TapeMatches (initTapes tArgA) [.leftMark] 1)
    (hMatchB : TapeMatches (initTapes tArgB) [.leftMark] 1)
    (hMatchS : TapeMatches (initTapes tScratch) [.leftMark] 1) :
    ∃ (res : Bool) (finalTapes : Fin 5 → OneSidedTape SimSym) (finalInHead : Fin (n + 2)),
      (savitchSimulator M).ReachesExit input bound initTapes inHead res finalTapes finalInHead ∧
      (res = true ↔ M.AcceptsWithinCapacity input S (by omega)) := by
  obtain ⟨res, ft, fih, h1, h2, _⟩ := savitchSimulator_reachesExit_clean M input bound S hS hInput
    hBoundR hBoundRegs hBoundA hBoundB hBoundS initTapes inHead
    hMatchR hMatchRegs hMatchA hMatchB hMatchS
  exact ⟨res, ft, fih, h1, h2⟩

end SavitchLemma

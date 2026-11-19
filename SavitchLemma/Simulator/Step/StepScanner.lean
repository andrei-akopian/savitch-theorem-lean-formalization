module

public import SavitchLemma.Simulator.Step.StepScanTape

@[expose] public section

/-!
# Full Serialized Transition Checker (`checkStep`)

Composes `readControlStates`, `readInputHeadAndCheck`, and `scanAllWorkTapes`
to implement `checkStep`, and proves `checkStep_reachesExit`: `checkStep`
returns `true` iff `M.step input S before after` holds.
-/

namespace SavitchLemma

/-! ## 5. Full `checkStep` component and equivalence with `MultitapeNTM.step` -/

/-- Evaluate the transition table given decoded control states, input-head symbol
and movement relation, and per-tape summaries. -/
noncomputable def checkStepEval {Q InputAlphabet Γ : Type*} {k : ℕ}
    [Fintype Q] [Fintype InputAlphabet] [Fintype Γ] [DecidableEq Γ]
    (M : MultitapeNTM Q InputAlphabet Γ k)
    (qOpt : Option (Q × Q)) (inPair : InputSymbol InputAlphabet × BitRelState)
    (sumOpt : Option (Fin k → TapeSummary Γ)) : Bool :=
  letI := Classical.propDecidable
  match qOpt, sumOpt with
  | some (qA, qB), some summaries =>
    (M.transitions qA inPair.1 (fun t => (summaries t).scanned)).any fun action =>
      decide (qB = action.nextState) &&
      relMatchesInputMove inPair.1 inPair.2 action.inputMove &&
      decide (∀ t, (summaries t).matchesAction (action.write t) (action.workMove t) = true)
  | _, _ => false

/-- Sealed `checkStep` packaging its `Fintype` state instance. -/
noncomputable def sealedCheckStep {Q InputAlphabet Γ : Type*} {k : ℕ}
    [Fintype Q] [Fintype InputAlphabet] [Fintype Γ]
    (M : MultitapeNTM Q InputAlphabet Γ k) :
    SealedTMComponent InputAlphabet SimSym 5 Bool :=
  ⟨_, letI := Classical.propDecidable
    (rewindInput InputAlphabet 5).seq
      (bindComponent (readControlStates Q InputAlphabet) fun qOpt =>
        bindComponent (readInputHeadAndCheck InputAlphabet) fun inPair =>
          bindComponent (scanAllWorkTapes InputAlphabet Γ k M.blank) fun sumOpt =>
            ((rewindTape InputAlphabet tArgA).seq (rewindTape InputAlphabet tArgB)).seq
              (TMComponent.atom fun _ scanned =>
                mkWorkAction (checkStepEval M qOpt inPair sumOpt) scanned (fun _ => .stay)))⟩

/-- Full serialized transition-table checker comparing `tArgA` (`before`) and
`tArgB` (`after`) against `M.transitions`, rewinding `tArgA`, `tArgB`, `tRuler`,
`tScratch`, and the physical input head to their initial positions. -/
noncomputable def checkStep {Q InputAlphabet Γ : Type*} {k : ℕ}
    [Fintype Q] [Fintype InputAlphabet] [Fintype Γ]
    (M : MultitapeNTM Q InputAlphabet Γ k) :=
  (sealedCheckStep M).comp

theorem checkStep_reachesExit {Q InputAlphabet Γ : Type*} {k n : ℕ}
    [Fintype Q] [Fintype InputAlphabet] [Fintype Γ]
    (M : MultitapeNTM Q InputAlphabet Γ k)
    (input : Fin n → InputAlphabet) (bound : Fin 5 → ℕ)
    (S : ℕ) (hS : 1 ≤ S) (hInput : n ≤ 2 ^ S)
    (before after : TMConfig Q Γ k n S)
    (hBoundR : S + 2 ≤ bound tRuler)
    (hBoundA : configBitWidth Q Γ k S + 2 ≤ bound tArgA)
    (hBoundB : configBitWidth Q Γ k S + 2 ≤ bound tArgB)
    (hBoundS : S + 4 ≤ bound tScratch)
    (initTapes : Fin 5 → OneSidedTape SimSym) (inHead : Fin (n + 2))
    (hOther : (initTapes tRegs).head < bound tRegs)
    (hMatchR : TapeMatches (initTapes tRuler)
      (.leftMark :: List.replicate S (.bit true) ++ [.endMark]) 1)
    (hMatchA : TapeMatches (initTapes tArgA)
      (.leftMark :: (encodeConfigBits Q Γ before).map SimSym.bit ++ [.endMark]) 1)
    (hMatchB : TapeMatches (initTapes tArgB)
      (.leftMark :: (encodeConfigBits Q Γ after).map SimSym.bit ++ [.endMark]) 1)
    (hMatchS : TapeMatches (initTapes tScratch) [.leftMark] 1) :
    ∃ finalTapes,
      (checkStep M).ReachesExit input bound initTapes inHead
        (M.checkStepSummary input S before after) finalTapes ⟨0, by omega⟩ ∧
      TapeMatches (finalTapes tRuler)
        (.leftMark :: List.replicate S (.bit true) ++ [.endMark]) 1 ∧
      TapeMatches (finalTapes tArgA)
        (.leftMark :: (encodeConfigBits Q Γ before).map SimSym.bit ++ [.endMark]) 1 ∧
      TapeMatches (finalTapes tArgB)
        (.leftMark :: (encodeConfigBits Q Γ after).map SimSym.bit ++ [.endMark]) 1 ∧
      TapeMatches (finalTapes tScratch) [.leftMark] 1 ∧
      finalTapes tRegs = initTapes tRegs := by
  classical
  have hInitBounds : ∀ j, (initTapes j).head < bound j := by
    intro j
    match j with
    | ⟨0, _⟩ => change (initTapes tRuler).head < bound tRuler; rw [hMatchR.head_eq]; omega
    | ⟨1, _⟩ => exact hOther
    | ⟨2, _⟩ => change (initTapes tArgA).head < bound tArgA; rw [hMatchA.head_eq]; omega
    | ⟨3, _⟩ => change (initTapes tArgB).head < bound tArgB; rw [hMatchB.head_eq]; omega
    | ⟨4, _⟩ => change (initTapes tScratch).head < bound tScratch; rw [hMatchS.head_eq]; omega
  -- Step 0: rewindInput
  have hRewIn := rewindInput_reachesExit input bound initTapes hInitBounds inHead
  -- Decompose encodeConfigBits into state, inputHead, workTapes, [true, false]
  let qBitsA := natToBits (qBits Q) (Fintype.equivFin Q before.state).val
  let qBitsB := natToBits (qBits Q) (Fintype.equivFin Q after.state).val
  let inBitsA := natToBits (S + 2) before.inputHead.val
  let inBitsB := natToBits (S + 2) after.inputHead.val
  let workBitsA := (List.finRange k).flatMap (fun t => encodeTapeBits Γ (before.workTapes t))
  let workBitsB := (List.finRange k).flatMap (fun t => encodeTapeBits Γ (after.workTapes t))
  let fullA := SimSym.leftMark :: (encodeConfigBits Q Γ before).map SimSym.bit ++ [SimSym.endMark]
  let fullB := SimSym.leftMark :: (encodeConfigBits Q Γ after).map SimSym.bit ++ [SimSym.endMark]
  have hFullALen : fullA.length = configBitWidth Q Γ k S + 2 := by
    simp [fullA, encodeConfigBits_length]
  have hFullBLen : fullB.length = configBitWidth Q Γ k S + 2 := by
    simp [fullB, encodeConfigBits_length]
  have hWorkALen : workBitsA.length = k * tapeBitWidth Γ S := by
    rw [List.length_flatMap, List.map_congr_left (fun t _ => encodeTapeBits_length Γ _),
      List.map_const', List.sum_replicate, List.length_finRange, smul_eq_mul]
  have hWorkBLen : workBitsB.length = k * tapeBitWidth Γ S := by
    rw [List.length_flatMap, List.map_congr_left (fun t _ => encodeTapeBits_length Γ _),
      List.map_const', List.sum_replicate, List.length_finRange, smul_eq_mul]
  have hFullAEq : fullA = [SimSym.leftMark] ++ qBitsA.map SimSym.bit ++
      (inBitsA.map SimSym.bit ++ workBitsA.map SimSym.bit ++
        [SimSym.bit true, SimSym.bit false, SimSym.endMark]) := by
    simp [fullA, encodeConfigBits, qBitsA, inBitsA, workBitsA, List.append_assoc]
  have hFullBEq : fullB = [SimSym.leftMark] ++ qBitsB.map SimSym.bit ++
      (inBitsB.map SimSym.bit ++ workBitsB.map SimSym.bit ++
        [SimSym.bit true, SimSym.bit false, SimSym.endMark]) := by
    simp [fullB, encodeConfigBits, qBitsB, inBitsB, workBitsB, List.append_assoc]
  -- Step 1: readControlStates
  have hBoundA_q : ([SimSym.leftMark] : List SimSym).length + qBits Q < bound tArgA := by
    simp only [List.length_singleton, configBitWidth] at *
    omega
  have hBoundB_q : ([SimSym.leftMark] : List SimSym).length + qBits Q < bound tArgB := by
    simp only [List.length_singleton, configBitWidth] at *
    omega
  obtain ⟨ftA1, ftB1, hReadQ, hA1, hB1⟩ :=
    readControlStates_reachesExit input bound before.state after.state
      [SimSym.leftMark] (inBitsA.map SimSym.bit ++ workBitsA.map SimSym.bit ++
        [SimSym.bit true, SimSym.bit false, SimSym.endMark])
      [SimSym.leftMark] (inBitsB.map SimSym.bit ++ workBitsB.map SimSym.bit ++
        [SimSym.bit true, SimSym.bit false, SimSym.endMark])
      hBoundA_q hBoundB_q initTapes ⟨0, by omega⟩ (fun j hjA hjB => hInitBounds j)
      (by
        have hM := hMatchA
        change TapeMatches (initTapes tArgA) fullA 1 at hM
        rw [hFullAEq] at hM
        simpa [qBitsA, List.append_assoc] using hM)
      (by
        have hM := hMatchB
        change TapeMatches (initTapes tArgB) fullB 1 at hM
        rw [hFullBEq] at hM
        simpa [qBitsB, List.append_assoc] using hM)
  let t1 := fun j => if j = tArgA then ftA1 else if j = tArgB then ftB1 else initTapes j
  -- Step 2: readInputHeadAndCheck
  let pA1 := [SimSym.leftMark] ++ qBitsA.map SimSym.bit
  let pB1 := [SimSym.leftMark] ++ qBitsB.map SimSym.bit
  let sA1 := workBitsA.map SimSym.bit ++ [SimSym.bit true, SimSym.bit false, SimSym.endMark]
  let sB1 := workBitsB.map SimSym.bit ++ [SimSym.bit true, SimSym.bit false, SimSym.endMark]
  have hPA1Len : pA1.length = 1 + qBits Q := by
    simp [pA1, qBitsA, natToBits_length, Nat.add_comm]
  have hPB1Len : pB1.length = 1 + qBits Q := by
    simp [pB1, qBitsB, natToBits_length, Nat.add_comm]
  have hBoundA_in : pA1.length + (S + 2) < bound tArgA := by
    rw [hPA1Len]; simp only [configBitWidth] at hBoundA; omega
  have hBoundB_in : pB1.length + (S + 2) < bound tArgB := by
    rw [hPB1Len]; simp only [configBitWidth] at hBoundB; omega
  have hA1' : TapeMatches (t1 tArgA) (pA1 ++ inBitsA.map SimSym.bit ++ sA1) pA1.length := by
    change TapeMatches ftA1 _ _
    rw [hPA1Len]
    simpa [pA1, sA1, List.append_assoc] using hA1
  have hB1' : TapeMatches (t1 tArgB) (pB1 ++ inBitsB.map SimSym.bit ++ sB1) pB1.length := by
    have hNe : tArgB ≠ tArgA := by decide
    change TapeMatches (if tArgB = tArgA then ftA1 else ftB1) _ _
    simp only [hNe, ↓reduceIte]
    rw [hPB1Len]
    simpa [pB1, sB1, List.append_assoc] using hB1
  obtain ⟨t2, hReadIn, hR2, hA2, hB2, hS2, hReg2⟩ :=
    readInputHeadAndCheck_reachesExit input bound S hS hInput before.inputHead after.inputHead
      pA1 sA1 pB1 sB1 hBoundR hBoundA_in hBoundB_in hBoundS t1 hOther
      hMatchR hA1' hB1' hMatchS
  -- Step 3: scanAllWorkTapes
  let pA2 := pA1 ++ inBitsA.map SimSym.bit
  let pB2 := pB1 ++ inBitsB.map SimSym.bit
  let sA2 := [SimSym.bit true, SimSym.bit false, SimSym.endMark]
  let sB2 := [SimSym.bit true, SimSym.bit false, SimSym.endMark]
  have hPA2Len : pA2.length = 1 + qBits Q + (S + 2) := by
    simp [pA2, hPA1Len, inBitsA, natToBits_length, Nat.add_assoc]
  have hPB2Len : pB2.length = 1 + qBits Q + (S + 2) := by
    simp [pB2, hPB1Len, inBitsB, natToBits_length, Nat.add_assoc]
  have hBoundA_w : pA2.length + k * tapeBitWidth Γ S < bound tArgA := by
    rw [hPA2Len]; simp only [configBitWidth] at hBoundA; omega
  have hBoundB_w : pB2.length + k * tapeBitWidth Γ S < bound tArgB := by
    rw [hPB2Len]; simp only [configBitWidth] at hBoundB; omega
  have hA2' : TapeMatches (t2 tArgA) (pA2 ++ workBitsA.map SimSym.bit ++ sA2) pA2.length := by
    rw [hPA2Len]
    simpa [pA2, sA2, List.append_assoc, Nat.add_assoc, hPA1Len] using hA2
  have hB2' : TapeMatches (t2 tArgB) (pB2 ++ workBitsB.map SimSym.bit ++ sB2) pB2.length := by
    rw [hPB2Len]
    simpa [pB2, sB2, List.append_assoc, Nat.add_assoc, hPB1Len] using hB2
  have hOther2 : (t2 tRegs).head < bound tRegs := by rw [hReg2]; exact hOther
  obtain ⟨t3, hScanAll, hR3, hA3, hB3, hS3, hReg3⟩ :=
    scanAllWorkTapes_reachesExit input bound S M.blank before.workTapes after.workTapes
      pA2 sA2 pB2 sB2 hBoundR hBoundA_w hBoundB_w (by omega) t2 ⟨0, by omega⟩
      hOther2 hR2 hA2' hB2' hS2
  -- Step 4: rewind tArgA and tArgB
  have hFullA_eq2 : fullA = pA2 ++ workBitsA.map SimSym.bit ++ sA2 := by
    simpa [pA2, pA1, sA2, List.append_assoc] using hFullAEq
  have hFullB_eq2 : fullB = pB2 ++ workBitsB.map SimSym.bit ++ sB2 := by
    simpa [pB2, pB1, sB2, List.append_assoc] using hFullBEq
  have hFullANoLeft : ∀ i, 1 ≤ i → i < fullA.length → fullA[i]? ≠ some SimSym.leftMark := by
    intro i hi1 hiLt
    cases i with
    | zero => omega
    | succ i =>
      simp only [fullA, List.length_cons, List.length_append, List.length_map,
        List.length_nil] at hiLt
      by_cases hiB : i < (encodeConfigBits Q Γ before).length
      · simp only [fullA]
        rw [List.getElem?_append_left (by simp [hiB]), List.getElem?_eq_getElem (by simp [hiB])]
        simp
      · have hiEq : i = (encodeConfigBits Q Γ before).length := by omega
        subst hiEq
        simp only [fullA]
        rw [List.getElem?_append_right (by simp)]
        simp
  have hFullBNoLeft : ∀ i, 1 ≤ i → i < fullB.length → fullB[i]? ≠ some SimSym.leftMark := by
    intro i hi1 hiLt
    cases i with
    | zero => omega
    | succ i =>
      simp only [fullB, List.length_cons, List.length_append, List.length_map,
        List.length_nil] at hiLt
      by_cases hiB : i < (encodeConfigBits Q Γ after).length
      · simp only [fullB]
        rw [List.getElem?_append_left (by simp [hiB]), List.getElem?_eq_getElem (by simp [hiB])]
        simp
      · have hiEq : i = (encodeConfigBits Q Γ after).length := by omega
        subst hiEq
        simp only [fullB]
        rw [List.getElem?_append_right (by simp)]
        simp
  have hT3OtherA : ∀ j, j ≠ tArgA → (t3 j).head < bound j := by
    intro j hjA
    match j with
    | ⟨0, _⟩ => change (t3 tRuler).head < bound tRuler; rw [hR3.head_eq]; omega
    | ⟨1, _⟩ => change (t3 tRegs).head < bound tRegs; rw [hReg3]; exact hOther2
    | ⟨2, _⟩ => exact False.elim (hjA rfl)
    | ⟨3, _⟩ => change (t3 tArgB).head < bound tArgB; rw [hB3.head_eq]; omega
    | ⟨4, _⟩ => change (t3 tScratch).head < bound tScratch; rw [hS3.head_eq]; omega
  obtain ⟨t4, hRewA, hA4, hOthers4⟩ :=
    rewindTape_reachesExit (InputAlphabet := InputAlphabet) tArgA input bound
      fullA (by simp [fullA]) (by simp [fullA]) hFullANoLeft
      (by rw [hFullALen]; exact hBoundA) t3 ⟨0, by omega⟩ hT3OtherA
      (pA2.length + k * tapeBitWidth Γ S) (by omega)
      (by rw [hFullALen, hPA2Len]; simp only [configBitWidth]; omega)
      (by simpa [hFullA_eq2] using hA3)
  have hT4OtherB : ∀ j, j ≠ tArgB → (t4 j).head < bound j := by
    intro j hjB
    by_cases hjA : j = tArgA
    · subst hjA; rw [hA4.head_eq]; omega
    · rw [hOthers4 j hjA]; exact hT3OtherA j hjA
  obtain ⟨t5, hRewB, hB5, hOthers5⟩ :=
    rewindTape_reachesExit (InputAlphabet := InputAlphabet) tArgB input bound
      fullB (by simp [fullB]) (by simp [fullB]) hFullBNoLeft
      (by rw [hFullBLen]; exact hBoundB) t4 ⟨0, by omega⟩ hT4OtherB
      (pB2.length + k * tapeBitWidth Γ S) (by omega)
      (by rw [hFullBLen, hPB2Len]; simp only [configBitWidth]; omega)
      (by rw [hOthers4 tArgB (by decide)]; simpa [hFullB_eq2] using hB3)
  -- Step 5: final evaluation atom
  have hT5Bounds : ∀ j, (t5 j).head < bound j := by
    intro j
    by_cases hjB : j = tArgB
    · subst hjB; rw [hB5.head_eq]; omega
    · rw [hOthers5 j hjB]; exact hT4OtherB j hjB
  let relIn := BitRelState.init.runList inBitsA inBitsB
  let sums : Fin k → TapeSummary Γ :=
    fun t => TapeSummary.ofBoundedTapes (before.workTapes t) (after.workTapes t)
  let okVal : Bool :=
    checkStepEval M (some (before.state, after.state)) (readInput input before.inputHead, relIn)
      (some sums)
  have hOkEq : okVal = M.checkStepSummary input S before after := by
    unfold okVal checkStepEval MultitapeNTM.checkStepSummary
    have hScannedEq : (fun t => (sums t).scanned) = before.scannedWork := rfl
    simp only [hScannedEq]
    congr 1
    funext action
    have hInIff : relMatchesInputMove (readInput input before.inputHead) relIn action.inputMove = true ↔
        moveHead (n + 2) before.inputHead action.inputMove = some after.inputHead := by
      rw [relMatchesInputMove_iff input before.inputHead after.inputHead.val inBitsA inBitsB
        (by simp [inBitsA, inBitsB, natToBits_length])
        (by
          have h2S : 2 ≤ 2 ^ S := by
            calc 2 = 2 ^ 1 := by decide
              _ ≤ 2 ^ S := Nat.pow_le_pow_right (by decide : 0 < 2) hS
          have hLt : before.inputHead.val < 2 ^ (S + 2) := by
            have := before.inputHead.isLt
            have : n + 2 ≤ 2 ^ (S + 1) := by rw [pow_succ']; omega
            have : 2 ^ (S + 1) ≤ 2 ^ (S + 2) := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
            omega
          exact bitsToNat_natToBits_of_lt hLt)
        (by
          have h2S : 2 ≤ 2 ^ S := by
            calc 2 = 2 ^ 1 := by decide
              _ ≤ 2 ^ S := Nat.pow_le_pow_right (by decide : 0 < 2) hS
          have hLt : after.inputHead.val < 2 ^ (S + 2) := by
            have := after.inputHead.isLt
            have : n + 2 ≤ 2 ^ (S + 1) := by rw [pow_succ']; omega
            have : 2 ^ (S + 1) ≤ 2 ^ (S + 2) := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
            omega
          exact bitsToNat_natToBits_of_lt hLt)
        action.inputMove]
      constructor
      · rintro ⟨h₂, hM, hVal⟩; rwa [Fin.ext hVal] at hM
      · intro hM; exact ⟨after.inputHead, hM, rfl⟩
    have hBoolEq :
        relMatchesInputMove (readInput input before.inputHead) relIn action.inputMove =
        decide (moveHead (n + 2) before.inputHead action.inputMove = some after.inputHead) :=
      Bool.eq_iff_iff.mpr (hInIff.trans decide_eq_true_iff.symm)
    rw [hBoolEq]
    congr 1
    exact decide_eq_decide.mpr (by simp [sums])
  have hAtom :
      (TMComponent.atom fun (_ : InputSymbol InputAlphabet) (scanned : Fin 5 → SimSym) =>
        mkWorkAction okVal scanned (fun _ => .stay)).ReachesExit
        input bound t5 ⟨0, by omega⟩ okVal t5 ⟨0, by omega⟩ := by
    apply TMComponent.atom_reachesExit _ input bound t5 ⟨0, by omega⟩ hT5Bounds ⟨0, by omega⟩
    · simp [mkWorkAction, moveHead]
    · intro j; exact OneSidedTape.updateAndMove_stay_self (t5 j)
    · exact hT5Bounds
  have hRewAB := TMComponent.seq_reachesExit (rewindTape InputAlphabet tArgA)
    (rewindTape InputAlphabet tArgB) input bound hRewA hRewB
  have hSeqAtom := TMComponent.seq_reachesExit
    ((rewindTape InputAlphabet tArgA).seq (rewindTape InputAlphabet tArgB))
    (TMComponent.atom fun _ scanned => mkWorkAction okVal scanned (fun _ => .stay))
    input bound hRewAB hAtom
  have hBind3 := bindComponent_reachesExit (scanAllWorkTapes InputAlphabet Γ k M.blank)
    (fun sumOpt => ((rewindTape InputAlphabet tArgA).seq (rewindTape InputAlphabet tArgB)).seq
      (TMComponent.atom fun _ scanned =>
        mkWorkAction (checkStepEval M (some (before.state, after.state))
          (readInput input before.inputHead, relIn) sumOpt) scanned (fun _ => .stay)))
    input bound hScanAll hSeqAtom
  have hBind2 := bindComponent_reachesExit (readInputHeadAndCheck InputAlphabet)
    (fun inPair => bindComponent (scanAllWorkTapes InputAlphabet Γ k M.blank) fun sumOpt =>
      ((rewindTape InputAlphabet tArgA).seq (rewindTape InputAlphabet tArgB)).seq
        (TMComponent.atom fun _ scanned =>
          mkWorkAction (checkStepEval M (some (before.state, after.state)) inPair sumOpt)
            scanned (fun _ => .stay)))
    input bound hReadIn hBind3
  have hBind1 := bindComponent_reachesExit (readControlStates Q InputAlphabet)
    (fun qOpt => bindComponent (readInputHeadAndCheck InputAlphabet) fun inPair =>
      bindComponent (scanAllWorkTapes InputAlphabet Γ k M.blank) fun sumOpt =>
        ((rewindTape InputAlphabet tArgA).seq (rewindTape InputAlphabet tArgB)).seq
          (TMComponent.atom fun _ scanned =>
            mkWorkAction (checkStepEval M qOpt inPair sumOpt) scanned (fun _ => .stay)))
    input bound hReadQ hBind2
  have hFull := TMComponent.seq_reachesExit (rewindInput InputAlphabet 5) _ input bound hRewIn hBind1
  rw [hOkEq] at hFull
  refine ⟨t5, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [checkStep, sealedCheckStep] using hFull
  · rw [hOthers5 tRuler (by decide), hOthers4 tRuler (by decide)]
    exact hR3
  · rw [hOthers5 tArgA (by decide)]
    simpa [fullA] using hA4
  · simpa [fullB] using hB5
  · rw [hOthers5 tScratch (by decide), hOthers4 tScratch (by decide)]
    exact hS3
  · rw [hOthers5 tRegs (by decide), hOthers4 tRegs (by decide), hReg3, hReg2]
    rfl

theorem checkStep_reachesExit_iff_step {Q InputAlphabet Γ : Type*} {k n : ℕ}
    [Fintype Q] [Fintype InputAlphabet] [Fintype Γ]
    (M : MultitapeNTM Q InputAlphabet Γ k)
    (input : Fin n → InputAlphabet) (bound : Fin 5 → ℕ)
    (S : ℕ) (hS : 1 ≤ S) (hInput : n ≤ 2 ^ S)
    (before after : TMConfig Q Γ k n S)
    (hBoundR : S + 2 ≤ bound tRuler)
    (hBoundA : configBitWidth Q Γ k S + 2 ≤ bound tArgA)
    (hBoundB : configBitWidth Q Γ k S + 2 ≤ bound tArgB)
    (hBoundS : S + 4 ≤ bound tScratch)
    (initTapes : Fin 5 → OneSidedTape SimSym) (inHead : Fin (n + 2))
    (hOther : (initTapes tRegs).head < bound tRegs)
    (hMatchR : TapeMatches (initTapes tRuler)
      (.leftMark :: List.replicate S (.bit true) ++ [.endMark]) 1)
    (hMatchA : TapeMatches (initTapes tArgA)
      (.leftMark :: (encodeConfigBits Q Γ before).map SimSym.bit ++ [.endMark]) 1)
    (hMatchB : TapeMatches (initTapes tArgB)
      (.leftMark :: (encodeConfigBits Q Γ after).map SimSym.bit ++ [.endMark]) 1)
    (hMatchS : TapeMatches (initTapes tScratch) [.leftMark] 1) :
    ∃ res finalTapes,
      (checkStep M).ReachesExit input bound initTapes inHead res finalTapes ⟨0, by omega⟩ ∧
      (res = true ↔ M.step input S before after) ∧
      TapeMatches (finalTapes tRuler)
        (.leftMark :: List.replicate S (.bit true) ++ [.endMark]) 1 ∧
      TapeMatches (finalTapes tArgA)
        (.leftMark :: (encodeConfigBits Q Γ before).map SimSym.bit ++ [.endMark]) 1 ∧
      TapeMatches (finalTapes tArgB)
        (.leftMark :: (encodeConfigBits Q Γ after).map SimSym.bit ++ [.endMark]) 1 ∧
      TapeMatches (finalTapes tScratch) [.leftMark] 1 ∧
      finalTapes tRegs = initTapes tRegs := by
  obtain ⟨finalTapes, hRun, hR, hA, hB, hS', hReg⟩ :=
    checkStep_reachesExit M input bound S hS hInput before after
      hBoundR hBoundA hBoundB hBoundS initTapes inHead hOther hMatchR hMatchA hMatchB hMatchS
  exact ⟨M.checkStepSummary input S before after, finalTapes, hRun,
    M.checkStepSummary_correct input S before after, hR, hA, hB, hS', hReg⟩

module

public import SavitchLemma.Simulator.Valid.CheckValidBTop

@[expose] public section

/-!
# Combined configuration-validity and transition checker (`checkValidAndStep`)

Runs `checkValidB` first; if valid (`Q`, work-tape heads `< S`, `Γ` cells, and
trailing `[true, false]`), runs `checkStep M`. Handles the remaining case where
the `(S + 2)`-bit input-head field decodes to `≥ n + 2` (in which case
`checkStep M` returns `false` and rewinds all tapes).
-/

namespace SavitchLemma

private theorem readInputHeadAndCheck_reachesExit_arbitrary {InputAlphabet : Type*} {n : ℕ}
    (input : Fin n → InputAlphabet) (bound : Fin 5 → ℕ)
    (S : ℕ) (hS : 1 ≤ S) (hInput : n ≤ 2 ^ S) (hA : Fin (n + 2))
    (inBs : List Bool) (hInBsLen : inBs.length = S + 2)
    (pA sA pB sB : List SimSym)
    (hBoundR : S + 2 ≤ bound tRuler)
    (hBoundA : pA.length + (S + 2) < bound tArgA)
    (hBoundB : pB.length + (S + 2) < bound tArgB)
    (hBoundS : S + 4 ≤ bound tScratch)
    (initTapes : Fin 5 → OneSidedTape SimSym)
    (hOther : (initTapes tRegs).head < bound tRegs)
    (hMatchR : TapeMatches (initTapes tRuler)
      (.leftMark :: List.replicate S (.bit true) ++ [.endMark]) 1)
    (hMatchA : TapeMatches (initTapes tArgA)
      (pA ++ (natToBits (S + 2) hA.val).map SimSym.bit ++ sA) pA.length)
    (hMatchB : TapeMatches (initTapes tArgB)
      (pB ++ inBs.map SimSym.bit ++ sB) pB.length)
    (hMatchS : TapeMatches (initTapes tScratch) [.leftMark] 1) :
    ∃ finalTapes,
      (readInputHeadAndCheck InputAlphabet).ReachesExit input bound initTapes ⟨0, by omega⟩
        (readInput input hA, BitRelState.init.runList (natToBits (S + 2) hA.val) inBs)
        finalTapes ⟨0, by omega⟩ ∧
      TapeMatches (finalTapes tRuler)
        (.leftMark :: List.replicate S (.bit true) ++ [.endMark]) 1 ∧
      TapeMatches (finalTapes tArgA)
        (pA ++ (natToBits (S + 2) hA.val).map SimSym.bit ++ sA) (pA.length + (S + 2)) ∧
      TapeMatches (finalTapes tArgB)
        (pB ++ inBs.map SimSym.bit ++ sB) (pB.length + (S + 2)) ∧
      TapeMatches (finalTapes tScratch) [.leftMark] 1 ∧
      finalTapes tRegs = initTapes tRegs := by
  let ua := natToBits (S + 2) hA.val
  have hUALen : ua.length = (if (⟨0, by decide⟩ : Fin 3).val = 0 then 2 else 0) + S := by
    simp [ua, natToBits_length]; omega
  have hUBLen : inBs.length = (if (⟨0, by decide⟩ : Fin 3).val = 0 then 2 else 0) + S := by
    simp [hInBsLen]; omega
  obtain ⟨t1, hRead, hR1, hA1, hB1, hS1, hReg1⟩ :=
    readHeadBlock_reachesExit ⟨0, by decide⟩ (Or.inl rfl) input bound S
      pA (ua.map SimSym.bit) sA pB (inBs.map SimSym.bit) sB ua inBs
      hUALen hUBLen rfl rfl hBoundR
      (by rw [hUALen]; omega)
      (by rw [hUBLen]; omega)
      (by rw [hUALen]; omega)
      initTapes ⟨0, by omega⟩ hOther hMatchR hMatchA hMatchB hMatchS
  have hT1OtherS : ∀ j, j ≠ tScratch → (t1 j).head < bound j := by
    intro j hjS
    match j with
    | ⟨0, _⟩ => change (t1 tRuler).head < bound tRuler; rw [hR1.head_eq]; omega
    | ⟨1, _⟩ => change (t1 tRegs).head < bound tRegs; rw [hReg1]; exact hOther
    | ⟨2, _⟩ => change (t1 tArgA).head < bound tArgA; rw [hA1.head_eq, hUALen]; omega
    | ⟨3, _⟩ => change (t1 tArgB).head < bound tArgB; rw [hB1.head_eq, hUBLen]; omega
    | ⟨4, _⟩ => exact False.elim (hjS rfl)
  obtain ⟨t2, hSeek, hS2, hOthers2⟩ :=
    seekInputHeadAndRead_reachesExit input bound S hS hInput hA
      (by omega) t1 hT1OtherS hS1
  have hT2Bounds : ∀ j, (t2 j).head < bound j := by
    intro j
    by_cases hjS : j = tScratch
    · subst hjS; rw [hS2.head_eq]; omega
    · rw [hOthers2 j hjS]; exact hT1OtherS j hjS
  have hRew := rewindInput_reachesExit input bound t2 (inHead := hA) hT2Bounds
  have hT2OtherS : ∀ j, j ≠ tScratch → (t2 j).head < bound j := fun j hj => hT2Bounds j
  obtain ⟨ftS, hClr, hS3⟩ :=
    clearTape_reachesExit tScratch input bound (List.replicate (S + 2) (SimSym.bit false))
      (by simp; omega) (by intro s hs; simp at hs; rcases hs with ⟨_, rfl⟩; simp)
      t2 ⟨0, by omega⟩ hT2OtherS (by simpa [List.map_replicate] using hS2)
  have hSeqRC := TMComponent.seq_reachesExit (rewindInput InputAlphabet 5)
    (clearTape InputAlphabet tScratch) input bound hRew hClr
  have hMapRC := TMComponent.mapExit_reachesExit
    ((rewindInput InputAlphabet 5).seq (clearTape InputAlphabet tScratch))
    (fun _ => (readInput input hA, BitRelState.init.runList ua inBs)) input bound hSeqRC
  have hBind2 := bindComponent_reachesExit (seekInputHeadAndRead InputAlphabet)
    (fun inSym => ((rewindInput InputAlphabet 5).seq (clearTape InputAlphabet tScratch)).mapExit
      (fun _ => (inSym, BitRelState.init.runList ua inBs)))
    input bound hSeek hMapRC
  have hBind1 := bindComponent_reachesExit (readHeadBlock InputAlphabet ⟨0, by decide⟩)
    (fun relInput => bindComponent (seekInputHeadAndRead InputAlphabet) fun inSym =>
      ((rewindInput InputAlphabet 5).seq (clearTape InputAlphabet tScratch)).mapExit
        (fun _ => (inSym, relInput)))
    input bound hRead hBind2
  let tFinal := fun j => if j = tScratch then ftS else t2 j
  refine ⟨tFinal, hBind1, ?_, ?_, ?_, ?_, ?_⟩
  · have hNe : tRuler ≠ tScratch := by decide
    simpa [tFinal, hNe, hOthers2 tRuler hNe] using hR1
  · have hNe : tArgA ≠ tScratch := by decide
    simpa [tFinal, hNe, hOthers2 tArgA hNe, hUALen, show 2 + S = S + 2 by omega] using hA1
  · have hNe : tArgB ≠ tScratch := by decide
    simpa [tFinal, hNe, hOthers2 tArgB hNe, hUBLen, show 2 + S = S + 2 by omega] using hB1
  · simpa [tFinal] using hS3
  · have hNe : tRegs ≠ tScratch := by decide
    simpa [tFinal, hNe, hOthers2 tRegs hNe] using hReg1

private theorem checkStep_reachesExit_invalidInHead {Q InputAlphabet Γ : Type*} {k n : ℕ}
    [Fintype Q] [Fintype InputAlphabet] [Fintype Γ]
    (M : MultitapeNTM Q InputAlphabet Γ k)
    (input : Fin n → InputAlphabet) (bound : Fin 5 → ℕ)
    (S : ℕ) (hS : 1 ≤ S) (hInput : n ≤ 2 ^ S)
    (before : TMConfig Q Γ k n S)
    (qB : Q) (inBs : List Bool) (hInBsLen : inBs.length = S + 2)
    (hInBsGe : n + 2 ≤ bitsToNat inBs)
    (tapesB : Fin k → BoundedTape Γ S)
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
      (.leftMark :: (natToBits (qBits Q) (Fintype.equivFin Q qB).val ++ inBs ++
        (List.finRange k).flatMap (fun t => encodeTapeBits Γ (tapesB t)) ++ [true, false]).map
          SimSym.bit ++ [.endMark]) 1)
    (hMatchS : TapeMatches (initTapes tScratch) [.leftMark] 1) :
    ∃ finalTapes,
      (checkStep M).ReachesExit input bound initTapes inHead false finalTapes ⟨0, by omega⟩ ∧
      TapeMatches (finalTapes tRuler)
        (.leftMark :: List.replicate S (.bit true) ++ [.endMark]) 1 ∧
      TapeMatches (finalTapes tArgA)
        (.leftMark :: (encodeConfigBits Q Γ before).map SimSym.bit ++ [.endMark]) 1 ∧
      TapeMatches (finalTapes tArgB)
        (.leftMark :: (natToBits (qBits Q) (Fintype.equivFin Q qB).val ++ inBs ++
          (List.finRange k).flatMap (fun t => encodeTapeBits Γ (tapesB t)) ++ [true, false]).map
            SimSym.bit ++ [.endMark]) 1 ∧
      TapeMatches (finalTapes tScratch) [.leftMark] 1 ∧
      finalTapes tRegs = initTapes tRegs := by
  classical
  let bsB := natToBits (qBits Q) (Fintype.equivFin Q qB).val ++ inBs ++
    (List.finRange k).flatMap (fun t => encodeTapeBits Γ (tapesB t)) ++ [true, false]
  have hBsBLen : bsB.length = configBitWidth Q Γ k S := by
    simp only [bsB, List.length_append, natToBits_length, hInBsLen, List.length_cons,
      List.length_nil]
    have hT : ((List.finRange k).flatMap (fun t => encodeTapeBits Γ (tapesB t))).length =
        k * tapeBitWidth Γ S := by
      rw [List.length_flatMap]
      have hC : ∀ t ∈ List.finRange k, (encodeTapeBits Γ (tapesB t)).length = tapeBitWidth Γ S :=
        fun t _ => encodeTapeBits_length Γ (tapesB t)
      rw [List.map_congr_left hC, List.map_const', List.sum_replicate, List.length_finRange,
        smul_eq_mul]
    rw [hT]; rfl
  have hInitBounds : ∀ j, (initTapes j).head < bound j := by
    intro j
    match j with
    | ⟨0, _⟩ => change (initTapes tRuler).head < bound tRuler; rw [hMatchR.head_eq]; omega
    | ⟨1, _⟩ => exact hOther
    | ⟨2, _⟩ => change (initTapes tArgA).head < bound tArgA; rw [hMatchA.head_eq]; omega
    | ⟨3, _⟩ => change (initTapes tArgB).head < bound tArgB; rw [hMatchB.head_eq]; omega
    | ⟨4, _⟩ => change (initTapes tScratch).head < bound tScratch; rw [hMatchS.head_eq]; omega
  have hRewIn := rewindInput_reachesExit input bound initTapes (inHead := inHead) hInitBounds
  -- 1. readControlStates
  let sufA1 := (natToBits (S + 2) before.inputHead.val ++
    (List.finRange k).flatMap (fun t => encodeTapeBits Γ (before.workTapes t)) ++
    [true, false]).map SimSym.bit ++ [.endMark]
  let sufB1 := (inBs ++ (List.finRange k).flatMap (fun t => encodeTapeBits Γ (tapesB t)) ++
    [true, false]).map SimSym.bit ++ [.endMark]
  have hFullA1 : .leftMark :: (encodeConfigBits Q Γ before).map SimSym.bit ++ [.endMark] =
      [.leftMark] ++ (natToBits (qBits Q) (Fintype.equivFin Q before.state).val).map SimSym.bit ++
        sufA1 := by
    simp [encodeConfigBits, sufA1, List.map_append, List.append_assoc]
  have hFullB1 : .leftMark :: bsB.map SimSym.bit ++ [.endMark] =
      [.leftMark] ++ (natToBits (qBits Q) (Fintype.equivFin Q qB).val).map SimSym.bit ++
        sufB1 := by
    simp [bsB, sufB1, List.map_append, List.append_assoc]
  have hOtherAB0 : ∀ j, j ≠ tArgA → j ≠ tArgB → (initTapes j).head < bound j :=
    fun j _ _ => hInitBounds j
  obtain ⟨ftA1, ftB1, hReadQ, hFA1, hFB1⟩ :=
    readControlStates_reachesExit input bound before.state qB [SimSym.leftMark] sufA1
      [SimSym.leftMark] sufB1
      (by simp only [List.length_singleton]; unfold configBitWidth at hBoundA; omega)
      (by simp only [List.length_singleton]; unfold configBitWidth at hBoundB; omega)
      initTapes ⟨0, by omega⟩ hOtherAB0
      (by simpa [hFullA1] using hMatchA)
      (by simpa [hFullB1, sufB1, List.map_append, List.append_assoc] using hMatchB)
  let t1 := fun j => if j = tArgA then ftA1 else if j = tArgB then ftB1 else initTapes j
  -- 2. readInputHeadAndCheck
  let pA2 := SimSym.leftMark :: (natToBits (qBits Q) (Fintype.equivFin Q before.state).val).map
    SimSym.bit
  let sA2 := ((List.finRange k).flatMap (fun t => encodeTapeBits Γ (before.workTapes t)) ++
    [true, false]).map SimSym.bit ++ [.endMark]
  let pB2 := SimSym.leftMark :: (natToBits (qBits Q) (Fintype.equivFin Q qB).val).map SimSym.bit
  let sB2 := ((List.finRange k).flatMap (fun t => encodeTapeBits Γ (tapesB t)) ++
    [true, false]).map SimSym.bit ++ [.endMark]
  have hFullA2 : .leftMark :: (encodeConfigBits Q Γ before).map SimSym.bit ++ [.endMark] =
      pA2 ++ (natToBits (S + 2) before.inputHead.val).map SimSym.bit ++ sA2 := by
    simp [encodeConfigBits, pA2, sA2, List.map_append, List.append_assoc]
  have hFullB2 : .leftMark :: bsB.map SimSym.bit ++ [.endMark] =
      pB2 ++ inBs.map SimSym.bit ++ sB2 := by
    simp [bsB, pB2, sB2, List.map_append, List.append_assoc]
  have hPA2Len : pA2.length = 1 + qBits Q := by simp [pA2, natToBits_length]; omega
  have hPB2Len : pB2.length = 1 + qBits Q := by simp [pB2, natToBits_length]; omega
  obtain ⟨t2, hReadIn, hR2, hA2, hB2, hS2, hReg2⟩ :=
    readInputHeadAndCheck_reachesExit_arbitrary input bound S hS hInput before.inputHead
      inBs hInBsLen pA2 sA2 pB2 sB2 hBoundR
      (by rw [hPA2Len]; unfold configBitWidth at hBoundA; omega)
      (by rw [hPB2Len]; unfold configBitWidth at hBoundB; omega)
      hBoundS t1 hOther
      (by simpa [t1, show tRuler ≠ tArgA by decide, show tRuler ≠ tArgB by decide] using hMatchR)
      (by simpa [t1, ← hFullA2, hFullA1, hPA2Len, Nat.add_assoc] using hFA1)
      (by simpa [t1, show tArgB ≠ tArgA by decide, ← hFullB2, hFullB1, hPB2Len, Nat.add_assoc] using hFB1)
      (by simpa [t1, show tScratch ≠ tArgA by decide, show tScratch ≠ tArgB by decide] using hMatchS)
  -- 3. scanAllWorkTapes
  let pA3 := SimSym.leftMark :: (natToBits (qBits Q) (Fintype.equivFin Q before.state).val ++
    natToBits (S + 2) before.inputHead.val).map SimSym.bit
  let sA3 := ([true, false] : List Bool).map SimSym.bit ++ [.endMark]
  let pB3 := SimSym.leftMark :: (natToBits (qBits Q) (Fintype.equivFin Q qB).val ++ inBs).map
    SimSym.bit
  let sB3 := ([true, false] : List Bool).map SimSym.bit ++ [.endMark]
  have hFullA3 : .leftMark :: (encodeConfigBits Q Γ before).map SimSym.bit ++ [.endMark] =
      pA3 ++ ((List.finRange k).flatMap (fun t => encodeTapeBits Γ (before.workTapes t))).map
        SimSym.bit ++ sA3 := by
    simp [encodeConfigBits, pA3, sA3, List.map_append, List.append_assoc]
  have hFullB3 : .leftMark :: bsB.map SimSym.bit ++ [.endMark] =
      pB3 ++ ((List.finRange k).flatMap (fun t => encodeTapeBits Γ (tapesB t))).map
        SimSym.bit ++ sB3 := by
    simp [bsB, pB3, sB3, List.map_append, List.append_assoc]
  have hPA3Len : pA3.length = 1 + qBits Q + (S + 2) := by
    simp [pA3, natToBits_length]; omega
  have hPB3Len : pB3.length = 1 + qBits Q + (S + 2) := by
    simp [pB3, natToBits_length, hInBsLen]; omega
  obtain ⟨t3, hScanAll, hR3, hA3, hB3, hS3, hReg3⟩ :=
    scanAllWorkTapes_reachesExit input bound S M.blank before.workTapes tapesB
      pA3 sA3 pB3 sB3 hBoundR
      (by rw [hPA3Len]; unfold configBitWidth at hBoundA; omega)
      (by rw [hPB3Len]; unfold configBitWidth at hBoundB; omega)
      (by omega)
      t2 ⟨0, by omega⟩ (by rw [hReg2]; exact hOther) hR2
      (by simpa [← hFullA3, hFullA2, hPA3Len, hPA2Len, Nat.add_assoc] using hA2)
      (by simpa [← hFullB3, hFullB2, hPB3Len, hPB2Len, Nat.add_assoc] using hB2)
      hS2
  -- 4. rewind tArgA, tArgB
  let listA := .leftMark :: (encodeConfigBits Q Γ before).map SimSym.bit ++ [.endMark]
  let listB := .leftMark :: bsB.map SimSym.bit ++ [.endMark]
  have hALen : listA.length = configBitWidth Q Γ k S + 2 := by
    simp [listA, encodeConfigBits_length]
  have hBLen : listB.length = configBitWidth Q Γ k S + 2 := by
    simp [listB, hBsBLen]
  have hListANoLeft : ∀ i, 1 ≤ i → i < listA.length → listA[i]? ≠ some SimSym.leftMark := by
    intro i hi1 hiLt
    cases i with
    | zero => omega
    | succ i =>
      simp only [listA, List.length_append, List.length_cons, List.length_map,
        List.length_nil, encodeConfigBits_length] at hiLt
      by_cases hiW : i < configBitWidth Q Γ k S
      · simp only [listA]
        rw [List.getElem?_append_left (by simp [encodeConfigBits_length]; omega),
          List.getElem?_cons_succ, List.getElem?_eq_getElem (by simp [encodeConfigBits_length, hiW])]
        simp
      · have hiEq : i = configBitWidth Q Γ k S := by omega
        subst hiEq
        simp only [listA]
        rw [List.getElem?_append_right (by simp [encodeConfigBits_length])]
        simp [encodeConfigBits_length]
  have hListBNoLeft : ∀ i, 1 ≤ i → i < listB.length → listB[i]? ≠ some SimSym.leftMark := by
    intro i hi1 hiLt
    cases i with
    | zero => omega
    | succ i =>
      simp only [listB, List.length_append, List.length_cons, List.length_map,
        List.length_nil, hBsBLen] at hiLt
      by_cases hiW : i < configBitWidth Q Γ k S
      · simp only [listB]
        rw [List.getElem?_append_left (by simp [hBsBLen]; omega),
          List.getElem?_cons_succ, List.getElem?_eq_getElem (by simp [hBsBLen, hiW])]
        simp
      · have hiEq : i = configBitWidth Q Γ k S := by omega
        subst hiEq
        simp only [listB]
        rw [List.getElem?_append_right (by simp [hBsBLen])]
        simp [hBsBLen]
  have hT3OtherA : ∀ j, j ≠ tArgA → (t3 j).head < bound j := by
    intro j hjA
    match j with
    | ⟨0, _⟩ => change (t3 tRuler).head < bound tRuler; rw [hR3.head_eq]; omega
    | ⟨1, _⟩ => change (t3 tRegs).head < bound tRegs; rw [hReg3, hReg2]; exact hOther
    | ⟨2, _⟩ => exact False.elim (hjA rfl)
    | ⟨3, _⟩ => change (t3 tArgB).head < bound tArgB; rw [hB3.head_eq, hPB3Len]; unfold configBitWidth at hBoundB; omega
    | ⟨4, _⟩ => change (t3 tScratch).head < bound tScratch; rw [hS3.head_eq]; omega
  obtain ⟨t4, hRewA, hA4, hOthers4⟩ :=
    rewindTape_reachesExit (InputAlphabet := InputAlphabet) tArgA input bound
      listA (by simp [listA]) (by simp [listA]) hListANoLeft
      (by rw [hALen]; exact hBoundA) t3 ⟨0, by omega⟩ hT3OtherA
      (pA3.length + k * tapeBitWidth Γ S) (by rw [hPA3Len]; omega)
      (by rw [hALen, hPA3Len]; unfold configBitWidth; omega)
      (by rw [← hFullA3] at hA3; exact hA3)
  have hT4OtherB : ∀ j, j ≠ tArgB → (t4 j).head < bound j := by
    intro j hjB
    by_cases hjA : j = tArgA
    · subst hjA; rw [hA4.head_eq]; omega
    · rw [hOthers4 j hjA]; exact hT3OtherA j hjA
  have hB3' : TapeMatches (t4 tArgB) listB (pB3.length + k * tapeBitWidth Γ S) := by
    rw [hOthers4 tArgB (by decide)]
    rw [← hFullB3] at hB3
    exact hB3
  obtain ⟨t5, hRewB, hB5, hOthers5⟩ :=
    rewindTape_reachesExit (InputAlphabet := InputAlphabet) tArgB input bound
      listB (by simp [listB]) (by simp [listB]) hListBNoLeft
      (by rw [hBLen]; exact hBoundB) t4 ⟨0, by omega⟩ hT4OtherB
      (pB3.length + k * tapeBitWidth Γ S) (by rw [hPB3Len]; omega)
      (by rw [hBLen, hPB3Len]; unfold configBitWidth; omega)
      hB3'
  have hT5Bounds : ∀ j, (t5 j).head < bound j := by
    intro j
    by_cases hjB : j = tArgB
    · subst hjB; rw [hB5.head_eq]; omega
    · rw [hOthers5 j hjB]; exact hT4OtherB j hjB
  -- 5. checkStepEval = false since relMatchesInputMove is false
  have hEvalFalse : checkStepEval M (some (before.state, qB))
      (readInput input before.inputHead,
        BitRelState.init.runList (natToBits (S + 2) before.inputHead.val) inBs)
      (some (fun t => TapeSummary.ofBoundedTapes (before.workTapes t) (tapesB t))) = false := by
    unfold checkStepEval
    dsimp only
    rw [List.any_eq_false]
    intro action _
    have hRelFalse : relMatchesInputMove (readInput input before.inputHead)
        (BitRelState.init.runList (natToBits (S + 2) before.inputHead.val) inBs)
        action.inputMove = false := by
      cases hR : relMatchesInputMove (readInput input before.inputHead)
          (BitRelState.init.runList (natToBits (S + 2) before.inputHead.val) inBs)
          action.inputMove
      · rfl
      · exfalso
        have hIff := (relMatchesInputMove_iff input before.inputHead (bitsToNat inBs)
          (natToBits (S + 2) before.inputHead.val) inBs
          (by rw [natToBits_length, hInBsLen])
          (bitsToNat_natToBits_of_lt (by
            have h1 : before.inputHead.val < n + 2 := before.inputHead.isLt
            have hPow1 : 1 ≤ 2 ^ S := Nat.one_le_pow S 2 (by decide)
            have h2 : n + 2 ≤ 2 ^ (S + 2) := by
              have : 2 ^ (S + 2) = 4 * 2 ^ S := by rw [pow_add, show 2 ^ 2 = 4 from rfl, Nat.mul_comm]
              omega
            omega)) rfl action.inputMove).mp hR
        rcases hIff with ⟨h₂, _, hVal⟩
        have := h₂.isLt
        omega
    simp [hRelFalse]
  have hAtom : (TMComponent.atom fun (_ : InputSymbol InputAlphabet) (scanned : Fin 5 → SimSym) =>
      mkWorkAction false scanned (fun _ => .stay)).ReachesExit
      input bound t5 ⟨0, by omega⟩ false t5 ⟨0, by omega⟩ := by
    convert TMComponent.atom_reachesExit _ input bound t5 ⟨0, by omega⟩ hT5Bounds ⟨0, by omega⟩
      _ t5 _ hT5Bounds
    · simp [mkWorkAction]
    · simp [mkWorkAction, moveHead]
    · intro j; simpa [mkWorkAction] using OneSidedTape.updateAndMove_stay_self (t5 j)
  have hSeqRew := TMComponent.seq_reachesExit (rewindTape InputAlphabet tArgA)
    (rewindTape InputAlphabet tArgB) input bound hRewA hRewB
  have hSeqAtom := TMComponent.seq_reachesExit _ _ input bound hSeqRew
    (by simpa [hEvalFalse] using hAtom)
  have hB3' := bindComponent_reachesExit (scanAllWorkTapes InputAlphabet Γ k M.blank)
    (fun sumOpt =>
      ((rewindTape InputAlphabet tArgA).seq (rewindTape InputAlphabet tArgB)).seq
        (TMComponent.atom fun _ scanned =>
          mkWorkAction
            (checkStepEval M (some (before.state, qB))
              (readInput input before.inputHead,
                BitRelState.init.runList (natToBits (S + 2) before.inputHead.val) inBs)
              sumOpt)
            scanned (fun _ => .stay)))
    input bound hScanAll
    (by simpa [← hEvalFalse] using hSeqAtom)
  have hB2 := bindComponent_reachesExit (readInputHeadAndCheck InputAlphabet)
    (fun inPair =>
      bindComponent (scanAllWorkTapes InputAlphabet Γ k M.blank) fun sumOpt =>
        ((rewindTape InputAlphabet tArgA).seq (rewindTape InputAlphabet tArgB)).seq
          (TMComponent.atom fun _ scanned =>
            mkWorkAction (checkStepEval M (some (before.state, qB)) inPair sumOpt)
              scanned (fun _ => .stay)))
    input bound hReadIn hB3'
  have hB1 := bindComponent_reachesExit (readControlStates Q InputAlphabet)
    (fun qOpt =>
      bindComponent (readInputHeadAndCheck InputAlphabet) fun inPair =>
        bindComponent (scanAllWorkTapes InputAlphabet Γ k M.blank) fun sumOpt =>
          ((rewindTape InputAlphabet tArgA).seq (rewindTape InputAlphabet tArgB)).seq
            (TMComponent.atom fun _ scanned =>
              mkWorkAction (checkStepEval M qOpt inPair sumOpt) scanned (fun _ => .stay)))
    input bound hReadQ hB2
  have hFull := TMComponent.seq_reachesExit (rewindInput InputAlphabet 5) _
    input bound hRewIn hB1
  refine ⟨t5, by dsimp only [checkStep]; rw [hEvalFalse] at hFull; exact hFull, ?_, ?_, hB5, ?_, ?_⟩
  · rw [hOthers5 tRuler (by decide), hOthers4 tRuler (by decide)]; exact hR3
  · rw [hOthers5 tArgA (by decide)]; exact hA4
  · rw [hOthers5 tScratch (by decide), hOthers4 tScratch (by decide)]; exact hS3
  · rw [hOthers5 tRegs (by decide), hOthers4 tRegs (by decide), hReg3, hReg2]
    simp [t1, show tRegs ≠ tArgA by decide, show tRegs ≠ tArgB by decide]

/-- Combined validity + transition checker on `tArgA` (`before`) and `tArgB`
(arbitrary `configBitWidth Q Γ k S`-bit list `bs`). -/
noncomputable def checkValidAndStep {Q InputAlphabet Γ : Type*} {k : ℕ}
    [Fintype Q] [Fintype InputAlphabet] [Fintype Γ]
    (M : MultitapeNTM Q InputAlphabet Γ k) :=
  TMComponent.branch
    (checkValidB Q InputAlphabet Γ k)
    (checkStep M)
    (TMComponent.atom fun (_ : InputSymbol InputAlphabet) (scanned : Fin 5 → SimSym) =>
      mkWorkAction false scanned (fun _ => .stay))

theorem checkValidAndStep_reachesExit {Q InputAlphabet Γ : Type*} {k n : ℕ}
    [Fintype Q] [Fintype InputAlphabet] [Fintype Γ]
    (M : MultitapeNTM Q InputAlphabet Γ k)
    (input : Fin n → InputAlphabet) (bound : Fin 5 → ℕ)
    (S : ℕ) (hS : 1 ≤ S) (hInput : n ≤ 2 ^ S)
    (before : TMConfig Q Γ k n S)
    (bs : List Bool) (hLen : bs.length = configBitWidth Q Γ k S)
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
      (.leftMark :: bs.map SimSym.bit ++ [.endMark]) 1)
    (hMatchS : TapeMatches (initTapes tScratch) [.leftMark] 1) :
    ∃ (res : Bool) (finalTapes : Fin 5 → OneSidedTape SimSym) (finalInHead : Fin (n + 2)),
      (checkValidAndStep M).ReachesExit input bound initTapes inHead res finalTapes finalInHead ∧
      (res = true ↔ ∃ after : TMConfig Q Γ k n S,
        bs = encodeConfigBits Q Γ after ∧ M.step input S before after) ∧
      TapeMatches (finalTapes tRuler)
        (.leftMark :: List.replicate S (.bit true) ++ [.endMark]) 1 ∧
      TapeMatches (finalTapes tArgA)
        (.leftMark :: (encodeConfigBits Q Γ before).map SimSym.bit ++ [.endMark]) 1 ∧
      TapeMatches (finalTapes tArgB)
        (.leftMark :: bs.map SimSym.bit ++ [.endMark]) 1 ∧
      TapeMatches (finalTapes tScratch) [.leftMark] 1 ∧
      finalTapes tRegs = initTapes tRegs := by
  have hOtherB : ∀ j, j ≠ tRuler → j ≠ tArgB → j ≠ tScratch → (initTapes j).head < bound j := by
    intro j hjR hjB hjS
    match j with
    | ⟨0, _⟩ => exact False.elim (hjR rfl)
    | ⟨1, _⟩ => exact hOther
    | ⟨2, _⟩ => change (initTapes tArgA).head < bound tArgA; rw [hMatchA.head_eq]; omega
    | ⟨3, _⟩ => exact False.elim (hjB rfl)
    | ⟨4, _⟩ => exact False.elim (hjS rfl)
  obtain ⟨validRes, ftR1, ftB1, ftS1, hValidRun, hR1, hB1, hS1, hValidIff⟩ :=
    checkValidB_reachesExit input bound S bs hLen hBoundR hBoundB (by omega)
      initTapes inHead hOtherB hMatchR hMatchB hMatchS
  let t1 := fun j => if j = tRuler then ftR1 else if j = tArgB then ftB1
    else if j = tScratch then ftS1 else initTapes j
  have hT1A : TapeMatches (t1 tArgA)
      (.leftMark :: (encodeConfigBits Q Γ before).map SimSym.bit ++ [.endMark]) 1 := by
    have h1 : tArgA ≠ tRuler := by decide
    have h2 : tArgA ≠ tArgB := by decide
    have h3 : tArgA ≠ tScratch := by decide
    simpa [t1, h1, h2, h3] using hMatchA
  have hT1Reg : t1 tRegs = initTapes tRegs := by
    have h1 : tRegs ≠ tRuler := by decide
    have h2 : tRegs ≠ tArgB := by decide
    have h3 : tRegs ≠ tScratch := by decide
    simp [t1, h1, h2, h3]
  cases hV : validRes
  · have hNotValid : ¬ ∃ after : TMConfig Q Γ k n S, bs = encodeConfigBits Q Γ after := by
      rintro ⟨after, rfl⟩
      have hVTrue : validRes = true := hValidIff.mpr
        ⟨after.state, natToBits (S + 2) after.inputHead.val, after.workTapes,
          natToBits_length _ _, rfl⟩
      rw [hV] at hVTrue
      cases hVTrue
    have hT1Bounds : ∀ j, (t1 j).head < bound j := by
      intro j
      match j with
      | ⟨0, _⟩ => change ftR1.head < bound tRuler; rw [hR1.head_eq]; omega
      | ⟨1, _⟩ => change (t1 tRegs).head < bound tRegs; rw [hT1Reg]; exact hOther
      | ⟨2, _⟩ => change (t1 tArgA).head < bound tArgA; rw [hT1A.head_eq]; omega
      | ⟨3, _⟩ => change ftB1.head < bound tArgB; rw [hB1.head_eq]; omega
      | ⟨4, _⟩ => change ftS1.head < bound tScratch; rw [hS1.head_eq]; omega
    have hFalseAtom : (TMComponent.atom fun (_ : InputSymbol InputAlphabet) (scanned : Fin 5 → SimSym) =>
        mkWorkAction false scanned (fun _ => .stay)).ReachesExit
        input bound t1 inHead false t1 inHead := by
      convert TMComponent.atom_reachesExit _ input bound t1 inHead hT1Bounds inHead _ t1 _ hT1Bounds
      · simp [mkWorkAction]
      · simp [mkWorkAction, moveHead]
      · intro j; simpa [mkWorkAction] using OneSidedTape.updateAndMove_stay_self (t1 j)
    have hBranch := TMComponent.branch_reachesExit (checkValidB Q InputAlphabet Γ k)
      (checkStep M) _ input bound false (by simpa [hV] using hValidRun) hFalseAtom
    refine ⟨false, t1, inHead, hBranch, ?_, hR1, hT1A, hB1, hS1, hT1Reg⟩
    simp only [Bool.false_eq_true, false_iff, not_exists, not_and]
    intro after hEq _
    exact hNotValid ⟨after, hEq⟩
  · obtain ⟨qB, inBs, tapesB, hInBsLen, rfl⟩ := hValidIff.mp hV
    by_cases hInLt : bitsToNat inBs < n + 2
    · let after : TMConfig Q Γ k n S :=
        { state := qB, inputHead := ⟨bitsToNat inBs, hInLt⟩, workTapes := tapesB }
      have hBsEq : natToBits (qBits Q) (Fintype.equivFin Q qB).val ++ inBs ++
          (List.finRange k).flatMap (fun t => encodeTapeBits Γ (tapesB t)) ++ [true, false] =
          encodeConfigBits Q Γ after := by
        simp only [encodeConfigBits, after]
        rw [← hInBsLen, natToBits_bitsToNat inBs]
      rw [hBsEq] at hB1 ⊢
      have hT1B : TapeMatches (t1 tArgB)
          (.leftMark :: (encodeConfigBits Q Γ after).map SimSym.bit ++ [.endMark]) 1 := by
        simpa [t1, show tArgB ≠ tRuler by decide] using hB1
      have hT1S : TapeMatches (t1 tScratch) [.leftMark] 1 := by
        simpa [t1, show tScratch ≠ tRuler by decide, show tScratch ≠ tArgB by decide] using hS1
      obtain ⟨res, finalTapes, hStepRun, hStepIff, hR2, hA2, hB2, hS2, hReg2⟩ :=
        checkStep_reachesExit_iff_step M input bound S hS hInput before after
          hBoundR hBoundA hBoundB hBoundS t1 inHead (by rw [hT1Reg]; exact hOther)
          (by simpa [t1] using hR1) hT1A hT1B hT1S
      have hBranch := TMComponent.branch_reachesExit (checkValidB Q InputAlphabet Γ k)
        (checkStep M)
        (TMComponent.atom fun (_ : InputSymbol InputAlphabet) (scanned : Fin 5 → SimSym) =>
          mkWorkAction false scanned (fun _ => .stay))
        input bound true (by simpa [hV] using hValidRun) hStepRun
      refine ⟨res, finalTapes, ⟨0, by omega⟩, hBranch, ?_, hR2, hA2, hB2, hS2,
        hReg2.trans hT1Reg⟩
      rw [hStepIff]
      constructor
      · intro hStep; exact ⟨after, rfl, hStep⟩
      · rintro ⟨after', hEnc, hStep⟩
        have hEq := encodeConfigBits_injective Q Γ hS hInput hEnc
        subst hEq; exact hStep
    · have hInGe : n + 2 ≤ bitsToNat inBs := by omega
      have hT1B : TapeMatches (t1 tArgB)
          (.leftMark :: (natToBits (qBits Q) (Fintype.equivFin Q qB).val ++ inBs ++
            (List.finRange k).flatMap (fun t => encodeTapeBits Γ (tapesB t)) ++ [true, false]).map
              SimSym.bit ++ [.endMark]) 1 := by
        simpa [t1, show tArgB ≠ tRuler by decide] using hB1
      have hT1S : TapeMatches (t1 tScratch) [.leftMark] 1 := by
        simpa [t1, show tScratch ≠ tRuler by decide, show tScratch ≠ tArgB by decide] using hS1
      obtain ⟨finalTapes, hStepRun, hR2, hA2, hB2, hS2, hReg2⟩ :=
        checkStep_reachesExit_invalidInHead M input bound S hS hInput before qB inBs
          hInBsLen hInGe tapesB hBoundR hBoundA hBoundB hBoundS t1 inHead
          (by rw [hT1Reg]; exact hOther)
          (by simpa [t1] using hR1) hT1A hT1B hT1S
      have hBranch := TMComponent.branch_reachesExit (checkValidB Q InputAlphabet Γ k)
        (checkStep M)
        (TMComponent.atom fun (_ : InputSymbol InputAlphabet) (scanned : Fin 5 → SimSym) =>
          mkWorkAction false scanned (fun _ => .stay))
        input bound true (by simpa [hV] using hValidRun) hStepRun
      refine ⟨false, finalTapes, ⟨0, by omega⟩, hBranch, ?_, hR2, hA2, hB2, hS2,
        hReg2.trans hT1Reg⟩
      simp only [Bool.false_eq_true, false_iff, not_exists, not_and]
      intro after hEnc _
      have hInEq : inBs = natToBits (S + 2) after.inputHead.val := by
        have h1 : (natToBits (qBits Q) (Fintype.equivFin Q qB).val).length = qBits Q :=
          natToBits_length _ _
        have h2 : (natToBits (qBits Q) (Fintype.equivFin Q after.state).val).length = qBits Q :=
          natToBits_length _ _
        have hDrop := congrArg (List.drop (qBits Q)) hEnc
        simp only [encodeConfigBits, List.append_assoc] at hDrop
        rw [List.drop_append, List.drop_of_length_le h1.le, List.nil_append, h1, Nat.sub_self,
          List.drop_zero] at hDrop
        rw [List.drop_append, List.drop_of_length_le h2.le, List.nil_append, h2, Nat.sub_self,
          List.drop_zero] at hDrop
        have hTake := congrArg (List.take (S + 2)) hDrop
        rw [List.take_append_of_le_length hInBsLen.symm.le, List.take_of_length_le hInBsLen.le] at hTake
        rw [List.take_append_of_le_length (natToBits_length _ _).symm.le,
          List.take_of_length_le (natToBits_length _ _).le] at hTake
        exact hTake
      have hNat := congrArg bitsToNat hInEq
      rw [bitsToNat_natToBits_of_lt (by
        have h1 : after.inputHead.val < n + 2 := after.inputHead.isLt
        have hPow1 : 1 ≤ 2 ^ S := Nat.one_le_pow S 2 (by decide)
        have h2 : n + 2 ≤ 2 ^ (S + 2) := by
          have : 2 ^ (S + 2) = 4 * 2 ^ S := by rw [pow_add, show 2 ^ 2 = 4 from rfl, Nat.mul_comm]
          omega
        omega)] at hNat
      have := after.inputHead.isLt
      omega

end SavitchLemma

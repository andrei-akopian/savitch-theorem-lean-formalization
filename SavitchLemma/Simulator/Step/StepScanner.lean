module

public import SavitchLemma.Simulator.Step.StepScanCells

@[expose] public section

/-!
# Serialized configuration scanner and full `checkStep`

Implements `scanWorkTape`, `scanAllWorkTapes`, and `checkStep`, and proves
`checkStep_reachesExit_iff_step`.
-/

namespace SavitchLemma

/-- Build an `Option (TapeSummary Γ)` from the head-relation DFA and cell scan state. -/
def mkTapeSummary {Γ : Type*} (relHead : BitRelState) (st : CellScanState Γ) :
    Option (TapeSummary Γ) :=
  if st.valid then
    some
      { ok := st.ok
        scanned := st.scanned
        written := st.written
        leftValid := relHead.decOk && !relHead.decCarry
        stayValid := relHead.eqOk
        rightValid := relHead.incOk && !relHead.incCarry }
  else
    none

/-- Scan one serialized work tape (`S`-bit head + `S` cells of `gammaBits Γ` bits)
and return its `TapeSummary`, rewinding `tRuler` and clearing `tScratch`. -/
noncomputable def scanWorkTape (InputAlphabet Γ : Type*) [Fintype Γ] [DecidableEq Γ]
    (blank : Γ) :=
  bindComponent (readHeadBlock InputAlphabet ⟨2, by decide⟩) fun relHead =>
    bindComponent (scanTapeCells InputAlphabet Γ blank) fun st =>
      ((rewindTape InputAlphabet tRuler).seq (clearTape InputAlphabet tScratch)).mapExit fun _ =>
        mkTapeSummary relHead st

private theorem tapeSummary_eq_ofBoundedTapes {Γ : Type*} {S : ℕ}
    [Fintype Γ] [DecidableEq Γ] (tapeA tapeB : BoundedTape Γ S)
    (st : CellScanState Γ) (relHead : BitRelState)
    (hOk : st.ok = true ↔ ∀ c : Fin S, c ≠ tapeA.head → tapeB.cells c = tapeA.cells c)
    (hScan : st.scanned = tapeA.cells tapeA.head)
    (hWrit : st.written = tapeB.cells tapeA.head)
    (hEq : relHead.eqOk = true ↔ tapeA.head.val = tapeB.head.val)
    (hInc : (relHead.incOk && !relHead.incCarry) = true ↔ tapeB.head.val = tapeA.head.val + 1)
    (hDec : (relHead.decOk && !relHead.decCarry) = true ↔ tapeA.head.val = tapeB.head.val + 1) :
    ({ ok := st.ok
       scanned := st.scanned
       written := st.written
       leftValid := relHead.decOk && !relHead.decCarry
       stayValid := relHead.eqOk
       rightValid := relHead.incOk && !relHead.incCarry } : TapeSummary Γ) =
      TapeSummary.ofBoundedTapes tapeA tapeB := by
  classical
  have hOkEq : st.ok = (TapeSummary.ofBoundedTapes tapeA tapeB).ok := by
    apply Bool.eq_iff_iff.mpr
    simpa [TapeSummary.ofBoundedTapes] using hOk
  have hLeftEq : (relHead.decOk && !relHead.decCarry) =
      (TapeSummary.ofBoundedTapes tapeA tapeB).leftValid := by
    apply Bool.eq_iff_iff.mpr
    rw [hDec]
    simp only [TapeSummary.ofBoundedTapes, decide_eq_true_eq]
    constructor
    · intro h
      refine ⟨⟨tapeA.head.val - 1, by omega⟩, ?_, Fin.ext (by simp; omega)⟩
      simp [moveHead, (by omega : 0 < tapeA.head.val)]
    · rintro ⟨next, hM, hEqN⟩
      simp only [moveHead] at hM
      split_ifs at hM with hPos
      simp only [Option.some.injEq] at hM
      have hVal : tapeB.head.val = tapeA.head.val - 1 := by
        rw [hEqN, ← hM]
      omega
  have hStayEq : relHead.eqOk = (TapeSummary.ofBoundedTapes tapeA tapeB).stayValid := by
    apply Bool.eq_iff_iff.mpr
    rw [hEq]
    simp only [TapeSummary.ofBoundedTapes, moveHead, Option.some.injEq, decide_eq_true_eq]
    constructor
    · intro h; exact ⟨tapeA.head, rfl, Fin.ext h.symm⟩
    · rintro ⟨next, rfl, hEqN⟩; exact (congrArg Fin.val hEqN).symm
  have hRightEq : (relHead.incOk && !relHead.incCarry) =
      (TapeSummary.ofBoundedTapes tapeA tapeB).rightValid := by
    apply Bool.eq_iff_iff.mpr
    rw [hInc]
    simp only [TapeSummary.ofBoundedTapes, decide_eq_true_eq]
    constructor
    · intro h
      have hLt : tapeA.head.val + 1 < S := by have := tapeB.head.isLt; omega
      refine ⟨⟨tapeA.head.val + 1, hLt⟩, ?_, Fin.ext (by simp [h])⟩
      simp [moveHead, hLt]
    · rintro ⟨next, hM, hEqN⟩
      simp only [moveHead] at hM
      split_ifs at hM with hLt
      simp only [Option.some.injEq] at hM
      rw [hEqN, ← hM]
  cases hSum : TapeSummary.ofBoundedTapes tapeA tapeB
  simp only [hSum] at hOkEq hLeftEq hStayEq hRightEq
  have hScanEq : st.scanned = (TapeSummary.ofBoundedTapes tapeA tapeB).scanned := hScan
  have hWritEq : st.written = (TapeSummary.ofBoundedTapes tapeA tapeB).written := hWrit
  rw [hSum] at hScanEq hWritEq
  subst hOkEq hScanEq hWritEq hLeftEq hStayEq hRightEq
  rfl

theorem scanWorkTape_reachesExit {InputAlphabet Γ : Type*} {n : ℕ}
    [Fintype Γ] [DecidableEq Γ]
    (input : Fin n → InputAlphabet) (bound : Fin 5 → ℕ)
    (S : ℕ) (blank : Γ) (tapeA tapeB : BoundedTape Γ S)
    (pA sA pB sB : List SimSym)
    (hBoundR : S + 2 ≤ bound tRuler)
    (hBoundA : pA.length + tapeBitWidth Γ S < bound tArgA)
    (hBoundB : pB.length + tapeBitWidth Γ S < bound tArgB)
    (hBoundS : S + 2 ≤ bound tScratch)
    (initTapes : Fin 5 → OneSidedTape SimSym) (inHead : Fin (n + 2))
    (hOther : (initTapes tRegs).head < bound tRegs)
    (hMatchR : TapeMatches (initTapes tRuler)
      (.leftMark :: List.replicate S (.bit true) ++ [.endMark]) 1)
    (hMatchA : TapeMatches (initTapes tArgA)
      (pA ++ (encodeTapeBits Γ tapeA).map SimSym.bit ++ sA) pA.length)
    (hMatchB : TapeMatches (initTapes tArgB)
      (pB ++ (encodeTapeBits Γ tapeB).map SimSym.bit ++ sB) pB.length)
    (hMatchS : TapeMatches (initTapes tScratch) [.leftMark] 1) :
    ∃ finalTapes,
      (scanWorkTape InputAlphabet Γ blank).ReachesExit input bound initTapes inHead
        (some (TapeSummary.ofBoundedTapes tapeA tapeB)) finalTapes inHead ∧
      TapeMatches (finalTapes tRuler)
        (.leftMark :: List.replicate S (.bit true) ++ [.endMark]) 1 ∧
      TapeMatches (finalTapes tArgA)
        (pA ++ (encodeTapeBits Γ tapeA).map SimSym.bit ++ sA) (pA.length + tapeBitWidth Γ S) ∧
      TapeMatches (finalTapes tArgB)
        (pB ++ (encodeTapeBits Γ tapeB).map SimSym.bit ++ sB) (pB.length + tapeBitWidth Γ S) ∧
      TapeMatches (finalTapes tScratch) [.leftMark] 1 ∧
      finalTapes tRegs = initTapes tRegs := by
  let ha := natToBits S tapeA.head.val
  let hb := natToBits S tapeB.head.val
  let ca := (List.finRange S).flatMap (fun c =>
    natToBits (gammaBits Γ) (Fintype.equivFin Γ (tapeA.cells c)).val)
  let cb := (List.finRange S).flatMap (fun c =>
    natToBits (gammaBits Γ) (Fintype.equivFin Γ (tapeB.cells c)).val)
  have hEncA : encodeTapeBits Γ tapeA = ha ++ ca := rfl
  have hEncB : encodeTapeBits Γ tapeB = hb ++ cb := rfl
  have hHALen : ha.length = S := natToBits_length S _
  have hHBLen : hb.length = S := natToBits_length S _
  have hCA_len : ca.length = S * gammaBits Γ := by
    rw [List.length_flatMap, List.map_congr_left (fun c _ => natToBits_length _ _),
      List.map_const', List.sum_replicate, List.length_finRange, smul_eq_mul]
  have hCB_len : cb.length = S * gammaBits Γ := by
    rw [List.length_flatMap, List.map_congr_left (fun c _ => natToBits_length _ _),
      List.map_const', List.sum_replicate, List.length_finRange, smul_eq_mul]
  have hSplitA : pA ++ (encodeTapeBits Γ tapeA).map SimSym.bit ++ sA =
      pA ++ ha.map SimSym.bit ++ (ca.map SimSym.bit ++ sA) := by
    simp [hEncA, List.append_assoc]
  have hSplitB : pB ++ (encodeTapeBits Γ tapeB).map SimSym.bit ++ sB =
      pB ++ hb.map SimSym.bit ++ (cb.map SimSym.bit ++ sB) := by
    simp [hEncB, List.append_assoc]
  have hBoundA_h : pA.length + ha.length < bound tArgA := by
    simp only [tapeBitWidth] at hBoundA
    omega
  have hBoundB_h : pB.length + hb.length < bound tArgB := by
    simp only [tapeBitWidth] at hBoundB
    omega
  obtain ⟨t1, hReadH, hR1, hA1, hB1, hS1, hReg1⟩ :=
    readHeadBlock_reachesExit ⟨2, by decide⟩ (Or.inr rfl) input bound S
      pA (ha.map SimSym.bit) (ca.map SimSym.bit ++ sA)
      pB (hb.map SimSym.bit) (cb.map SimSym.bit ++ sB)
      ha hb (by simp [hHALen]) (by simp [hHBLen]) rfl rfl
      hBoundR hBoundA_h hBoundB_h (by simpa [hHALen] using hBoundS)
      initTapes inHead hOther hMatchR
      (by simpa [hSplitA] using hMatchA) (by simpa [hSplitB] using hMatchB) hMatchS
  let pA' := pA ++ ha.map SimSym.bit
  let pB' := pB ++ hb.map SimSym.bit
  have hA1' : TapeMatches (t1 tArgA) (pA' ++ ca.map SimSym.bit ++ sA) pA'.length := by
    simpa [pA', List.length_append, List.length_map, hHALen, List.append_assoc] using hA1
  have hB1' : TapeMatches (t1 tArgB) (pB' ++ cb.map SimSym.bit ++ sB) pB'.length := by
    simpa [pB', List.length_append, List.length_map, hHBLen, List.append_assoc] using hB1
  have hBoundA_c : pA'.length + S * gammaBits Γ < bound tArgA := by
    simp only [pA', List.length_append, List.length_map, hHALen]
    simp only [tapeBitWidth] at hBoundA
    omega
  have hBoundB_c : pB'.length + S * gammaBits Γ < bound tArgB := by
    simp only [pB', List.length_append, List.length_map, hHBLen]
    simp only [tapeBitWidth] at hBoundB
    omega
  have hOther1 : (t1 tRegs).head < bound tRegs := by rw [hReg1]; exact hOther
  obtain ⟨st, t2, hScan, hValid, hOk, hSc, hWr, hR2, hA2, hB2, hS2, hReg2⟩ :=
    scanTapeCells_reachesExit input bound S blank tapeA tapeB pA' sA pB' sB
      hBoundR hBoundA_c hBoundB_c hBoundS t1 inHead hOther1 hR1 hA1' hB1' hS1
  let rulerList := SimSym.leftMark :: List.replicate S (SimSym.bit true) ++ [SimSym.endMark]
  have hRulerNoLeft : ∀ i, 1 ≤ i → i < rulerList.length →
      rulerList[i]? ≠ some SimSym.leftMark := by
    intro i hi1 hiLt
    cases i with
    | zero => omega
    | succ i =>
      simp only [rulerList, List.length_append, List.length_cons, List.length_replicate,
        List.length_nil] at hiLt
      by_cases hiS : i < S
      · simp only [rulerList]
        rw [List.getElem?_append_left (by simp; omega), List.getElem?_cons_succ,
          List.getElem?_eq_getElem (by simp [hiS])]
        simp
      · have hiEq : i = S := by omega
        subst hiEq
        simp only [rulerList]
        rw [List.getElem?_append_right (by simp)]
        simp
  have hT2OtherR : ∀ j, j ≠ tRuler → (t2 j).head < bound j := by
    intro j hjR
    match j with
    | ⟨0, _⟩ => exact False.elim (hjR rfl)
    | ⟨1, _⟩ => change (t2 tRegs).head < bound tRegs; rw [hReg2]; exact hOther1
    | ⟨2, _⟩ => change (t2 tArgA).head < bound tArgA; rw [hA2.head_eq]; exact hBoundA_c
    | ⟨3, _⟩ => change (t2 tArgB).head < bound tArgB; rw [hB2.head_eq]; exact hBoundB_c
    | ⟨4, _⟩ => change (t2 tScratch).head < bound tScratch; rw [hS2.head_eq]; omega
  obtain ⟨t3, hRewR, hR3, hOthersR⟩ :=
    rewindTape_reachesExit (InputAlphabet := InputAlphabet) tRuler input bound
      rulerList (by simp [rulerList]) (by simp [rulerList]) hRulerNoLeft
      (by simp [rulerList]; exact hBoundR) t2 inHead hT2OtherR (1 + S) (by omega)
      (by simp [rulerList]; omega) hR2
  have hT3OtherS : ∀ j, j ≠ tScratch → (t3 j).head < bound j := by
    intro j hjS
    by_cases hjR : j = tRuler
    · subst hjR; rw [hR3.head_eq]; omega
    · rw [hOthersR j hjR]; exact hT2OtherR j hjR
  let prefSyms := (List.replicate S false).map SimSym.bit
  have hNoEnd : ∀ s ∈ prefSyms, s ≠ SimSym.endMark := by
    intro s hs
    simp only [prefSyms, List.mem_map, List.mem_replicate] at hs
    rcases hs with ⟨_, _, rfl⟩
    simp
  have hS3In : TapeMatches (t3 tScratch) (.leftMark :: prefSyms ++ [.endMark]) 1 := by
    have hNe : tScratch ≠ tRuler := by decide
    rw [hOthersR tScratch hNe]
    simpa [prefSyms] using hS2
  obtain ⟨ftS, hClearS, hS4⟩ :=
    clearTape_reachesExit tScratch input bound prefSyms
      (by simp [prefSyms, hBoundS]) hNoEnd t3 inHead hT3OtherS hS3In
  have hSeqRC := TMComponent.seq_reachesExit (rewindTape InputAlphabet tRuler)
    (clearTape InputAlphabet tScratch) input bound hRewR hClearS
  let relHead := BitRelState.init.runList ha hb
  have hRelBits := BitRelState.init_runList ha hb (by simp [hHALen, hHBLen])
  have hHeadALt : tapeA.head.val < 2 ^ S :=
    lt_trans tapeA.head.isLt Nat.lt_two_pow_self
  have hHeadBLt : tapeB.head.val < 2 ^ S :=
    lt_trans tapeB.head.isLt Nat.lt_two_pow_self
  have hSummaryEq :
      mkTapeSummary relHead st = some (TapeSummary.ofBoundedTapes tapeA tapeB) := by
    have hSum := tapeSummary_eq_ofBoundedTapes tapeA tapeB st relHead hOk hSc hWr
      (by simpa [relHead, ha, hb, bitsToNat_natToBits_of_lt hHeadALt,
        bitsToNat_natToBits_of_lt hHeadBLt] using hRelBits.1)
      (by simpa [relHead, ha, hb, bitsToNat_natToBits_of_lt hHeadALt,
        bitsToNat_natToBits_of_lt hHeadBLt] using hRelBits.2.1)
      (by simpa [relHead, ha, hb, bitsToNat_natToBits_of_lt hHeadALt,
        bitsToNat_natToBits_of_lt hHeadBLt] using hRelBits.2.2)
    simp [mkTapeSummary, hValid, hSum]
  have hMapped := TMComponent.mapExit_reachesExit
    ((rewindTape InputAlphabet tRuler).seq (clearTape InputAlphabet tScratch))
    (fun _ => mkTapeSummary relHead st) input bound hSeqRC
  have hBind2 := bindComponent_reachesExit (scanTapeCells InputAlphabet Γ blank)
    (fun st => ((rewindTape InputAlphabet tRuler).seq (clearTape InputAlphabet tScratch)).mapExit
      fun _ => mkTapeSummary relHead st)
    input bound hScan hMapped
  have hBind1 := bindComponent_reachesExit (readHeadBlock InputAlphabet ⟨2, by decide⟩)
    (fun relHead => bindComponent (scanTapeCells InputAlphabet Γ blank) fun st =>
      ((rewindTape InputAlphabet tRuler).seq (clearTape InputAlphabet tScratch)).mapExit fun _ =>
        mkTapeSummary relHead st)
    input bound hReadH hBind2
  rw [hSummaryEq] at hBind1
  refine ⟨_, hBind1, ?_, ?_, ?_, ?_, ?_⟩
  · have hNe : tRuler ≠ tScratch := by decide
    simpa [hNe, rulerList] using hR3
  · have hNeS : tArgA ≠ tScratch := by decide
    have hNeR : tArgA ≠ tRuler := by decide
    have hPosEq : pA' ++ List.map SimSym.bit ca ++ sA =
        pA ++ List.map SimSym.bit (encodeTapeBits Γ tapeA) ++ sA := by
      simp [pA', hEncA, List.append_assoc]
    have hLenEq : pA'.length + S * gammaBits Γ = pA.length + tapeBitWidth Γ S := by
      simp [pA', hHALen, tapeBitWidth, Nat.add_assoc]
    simp only [hNeS, ↓reduceIte]
    rw [hOthersR tArgA hNeR, ← hPosEq, ← hLenEq]
    exact hA2
  · have hNeS : tArgB ≠ tScratch := by decide
    have hNeR : tArgB ≠ tRuler := by decide
    have hPosEq : pB' ++ List.map SimSym.bit cb ++ sB =
        pB ++ List.map SimSym.bit (encodeTapeBits Γ tapeB) ++ sB := by
      simp [pB', hEncB, List.append_assoc]
    have hLenEq : pB'.length + S * gammaBits Γ = pB.length + tapeBitWidth Γ S := by
      simp [pB', hHBLen, tapeBitWidth, Nat.add_assoc]
    simp only [hNeS, ↓reduceIte]
    rw [hOthersR tArgB hNeR, ← hPosEq, ← hLenEq]
    exact hB2
  · simpa using hS4
  · have hNeS : tRegs ≠ tScratch := by decide
    have hNeR : tRegs ≠ tRuler := by decide
    simp only [hNeS, ↓reduceIte]
    rw [hOthersR tRegs hNeR, hReg2, hReg1]

/-! ## 4. Scanning all `k` work tapes -/

/-- Default placeholder `TapeSummary` used to initialize the `Fin k → TapeSummary Γ`
accumulator before scanning tapes `0 .. k - 1`. -/
def defaultTapeSummary {Γ : Type*} (blank : Γ) : TapeSummary Γ where
  ok := false
  scanned := blank
  written := blank
  leftValid := false
  stayValid := false
  rightValid := false

/-- One iteration of `scanAllWorkTapes`: if `st.1.val < k`, scan the next work
tape and record its `TapeSummary`; otherwise exit with `some st.2`. -/
noncomputable def scanAllWorkTapesStep (InputAlphabet Γ : Type*) [Fintype Γ] [DecidableEq Γ]
    (k : ℕ) (blank : Γ)
    (st : Fin (k + 1) × (Fin k → TapeSummary Γ)) :=
  TMComponent.branch
    (TMComponent.atom fun _ scanned =>
      mkWorkAction (decide (st.1.val < k)) scanned (fun _ => .stay))
    ((scanWorkTape InputAlphabet Γ blank).mapExit fun
      | none => (Sum.inr none : (Fin (k + 1) × (Fin k → TapeSummary Γ)) ⊕ Option (Fin k → TapeSummary Γ))
      | some ts =>
        if h : st.1.val < k then
          let summaries' : Fin k → TapeSummary Γ :=
            fun j => if j.val = st.1.val then ts else st.2 j
          Sum.inl ((⟨st.1.val + 1, by omega⟩ : Fin (k + 1)), summaries')
        else
          Sum.inr none)
    (TMComponent.atom fun _ scanned =>
      mkWorkAction (Sum.inr (some st.2)) scanned (fun _ => .stay))

/-- Scan all `k` serialized work tapes from `tArgA` and `tArgB`, returning
`some (fun t => TapeSummary.ofBoundedTapes (tapesA t) (tapesB t))`. -/
noncomputable def scanAllWorkTapes (InputAlphabet Γ : Type*) [Fintype Γ] [DecidableEq Γ]
    (k : ℕ) (blank : Γ) :=
  loopWithState ((⟨0, Nat.zero_lt_succ k⟩ : Fin (k + 1)), fun _ : Fin k => defaultTapeSummary blank)
    (scanAllWorkTapesStep InputAlphabet Γ k blank)

theorem scanAllWorkTapes_reachesExit {InputAlphabet Γ : Type*} {k n : ℕ}
    [Fintype Γ] [DecidableEq Γ]
    (input : Fin n → InputAlphabet) (bound : Fin 5 → ℕ)
    (S : ℕ) (blank : Γ) (tapesA tapesB : Fin k → BoundedTape Γ S)
    (pA sA pB sB : List SimSym)
    (hBoundR : S + 2 ≤ bound tRuler)
    (hBoundA : pA.length + k * tapeBitWidth Γ S < bound tArgA)
    (hBoundB : pB.length + k * tapeBitWidth Γ S < bound tArgB)
    (hBoundS : S + 2 ≤ bound tScratch)
    (initTapes : Fin 5 → OneSidedTape SimSym) (inHead : Fin (n + 2))
    (hOther : (initTapes tRegs).head < bound tRegs)
    (hMatchR : TapeMatches (initTapes tRuler)
      (.leftMark :: List.replicate S (.bit true) ++ [.endMark]) 1)
    (hMatchA : TapeMatches (initTapes tArgA)
      (pA ++ ((List.finRange k).flatMap (fun t => encodeTapeBits Γ (tapesA t))).map SimSym.bit ++ sA)
      pA.length)
    (hMatchB : TapeMatches (initTapes tArgB)
      (pB ++ ((List.finRange k).flatMap (fun t => encodeTapeBits Γ (tapesB t))).map SimSym.bit ++ sB)
      pB.length)
    (hMatchS : TapeMatches (initTapes tScratch) [.leftMark] 1) :
    ∃ finalTapes,
      (scanAllWorkTapes InputAlphabet Γ k blank).ReachesExit input bound initTapes inHead
        (some (fun t => TapeSummary.ofBoundedTapes (tapesA t) (tapesB t))) finalTapes inHead ∧
      TapeMatches (finalTapes tRuler)
        (.leftMark :: List.replicate S (.bit true) ++ [.endMark]) 1 ∧
      TapeMatches (finalTapes tArgA)
        (pA ++ ((List.finRange k).flatMap (fun t => encodeTapeBits Γ (tapesA t))).map SimSym.bit ++ sA)
        (pA.length + k * tapeBitWidth Γ S) ∧
      TapeMatches (finalTapes tArgB)
        (pB ++ ((List.finRange k).flatMap (fun t => encodeTapeBits Γ (tapesB t))).map SimSym.bit ++ sB)
        (pB.length + k * tapeBitWidth Γ S) ∧
      TapeMatches (finalTapes tScratch) [.leftMark] 1 ∧
      finalTapes tRegs = initTapes tRegs := by
  let fA : Fin k → List Bool := fun t => encodeTapeBits Γ (tapesA t)
  let fB : Fin k → List Bool := fun t => encodeTapeBits Γ (tapesB t)
  let fullA := pA ++ ((List.finRange k).flatMap fA).map SimSym.bit ++ sA
  let fullB := pB ++ ((List.finRange k).flatMap fB).map SimSym.bit ++ sB
  have hTakeLen : ∀ (f : Fin k → List Bool), (∀ t, (f t).length = tapeBitWidth Γ S) →
      ∀ i : ℕ, i ≤ k → (((List.finRange k).take i).flatMap f).length = i * tapeBitWidth Γ S := by
    intro f hf i hi
    rw [List.length_flatMap, List.map_congr_left (fun t _ => hf t), List.map_const',
      List.sum_replicate, List.length_take, List.length_finRange, Nat.min_eq_left hi, smul_eq_mul]
  have hFA_len : ∀ t, (fA t).length = tapeBitWidth Γ S := fun t => encodeTapeBits_length Γ (tapesA t)
  have hFB_len : ∀ t, (fB t).length = tapeBitWidth Γ S := fun t => encodeTapeBits_length Γ (tapesB t)
  have hSplitRange : ∀ i (hi : i < k),
      List.finRange k = (List.finRange k).take i ++ ⟨i, hi⟩ :: (List.finRange k).drop (i + 1) := by
    intro i hi
    have h1 := (List.take_append_drop i (List.finRange k)).symm
    have h2 : (List.finRange k).drop i =
        (List.finRange k)[i]'(by simp [hi]) :: (List.finRange k).drop (i + 1) :=
      List.drop_eq_getElem_cons (by simp [hi])
    simpa [h2, List.getElem_finRange] using h1
  let Inv : (Fin (k + 1) × (Fin k → TapeSummary Γ)) → (Fin 5 → OneSidedTape SimSym) →
      Fin (n + 2) → Prop :=
    fun st tapes curInHead =>
      curInHead = inHead ∧
      (∀ t : Fin k, t.val < st.1.val → st.2 t = TapeSummary.ofBoundedTapes (tapesA t) (tapesB t)) ∧
      TapeMatches (tapes tRuler) (.leftMark :: List.replicate S (.bit true) ++ [.endMark]) 1 ∧
      TapeMatches (tapes tArgA) fullA (pA.length + st.1.val * tapeBitWidth Γ S) ∧
      TapeMatches (tapes tArgB) fullB (pB.length + st.1.val * tapeBitWidth Γ S) ∧
      TapeMatches (tapes tScratch) [.leftMark] 1 ∧
      tapes tRegs = initTapes tRegs
  let measure : (Fin (k + 1) × (Fin k → TapeSummary Γ)) → (Fin 5 → OneSidedTape SimSym) →
      Fin (n + 2) → ℕ :=
    fun st _ _ => k - st.1.val
  let Post : Option (Fin k → TapeSummary Γ) → (Fin 5 → OneSidedTape SimSym) →
      Fin (n + 2) → Prop :=
    fun res tapes curInHead =>
      curInHead = inHead ∧
      res = some (fun t => TapeSummary.ofBoundedTapes (tapesA t) (tapesB t)) ∧
      TapeMatches (tapes tRuler) (.leftMark :: List.replicate S (.bit true) ++ [.endMark]) 1 ∧
      TapeMatches (tapes tArgA) fullA (pA.length + k * tapeBitWidth Γ S) ∧
      TapeMatches (tapes tArgB) fullB (pB.length + k * tapeBitWidth Γ S) ∧
      TapeMatches (tapes tScratch) [.leftMark] 1 ∧
      tapes tRegs = initTapes tRegs
  have hStep : ∀ st tapes curInHead, Inv st tapes curInHead →
      (∃ st' tapes' curInHead',
        (scanAllWorkTapesStep InputAlphabet Γ k blank st).ReachesExit input bound tapes curInHead
          (.inl st') tapes' curInHead' ∧
        Inv st' tapes' curInHead' ∧
        measure st' tapes' curInHead' < measure st tapes curInHead) ∨
      (∃ e tapes' curInHead',
        (scanAllWorkTapesStep InputAlphabet Γ k blank st).ReachesExit input bound tapes curInHead
          (.inr e) tapes' curInHead' ∧
        Post e tapes' curInHead') := by
    rintro ⟨idx, summaries⟩ tapes curInHead hInv
    rcases hInv with ⟨hInEq, hPrev, hMR, hMA, hMB, hMS, hReg⟩
    dsimp only at hPrev hMA hMB
    cases hInEq
    have hIdxLe : idx.val ≤ k := Nat.lt_succ_iff.mp idx.isLt
    have hBounds : ∀ j, (tapes j).head < bound j := by
      intro j
      match j with
      | ⟨0, _⟩ => change (tapes tRuler).head < bound tRuler; rw [hMR.head_eq]; omega
      | ⟨1, _⟩ => change (tapes tRegs).head < bound tRegs; rw [hReg]; exact hOther
      | ⟨2, _⟩ =>
        change (tapes tArgA).head < bound tArgA
        rw [hMA.head_eq]
        have : idx.val * tapeBitWidth Γ S ≤ k * tapeBitWidth Γ S := Nat.mul_le_mul_right _ hIdxLe
        omega
      | ⟨3, _⟩ =>
        change (tapes tArgB).head < bound tArgB
        rw [hMB.head_eq]
        have : idx.val * tapeBitWidth Γ S ≤ k * tapeBitWidth Γ S := Nat.mul_le_mul_right _ hIdxLe
        omega
      | ⟨4, _⟩ => change (tapes tScratch).head < bound tScratch; rw [hMS.head_eq]; omega
    by_cases hLt : idx.val < k
    · left
      have hDecT : decide (idx.val < k) = true := decide_eq_true hLt
      have hAtomBranch :
          (TMComponent.atom fun (_ : InputSymbol InputAlphabet) (scanned : Fin 5 → SimSym) =>
            mkWorkAction (decide (idx.val < k)) scanned (fun _ => .stay)).ReachesExit
            input bound tapes inHead true tapes inHead := by
        rw [← hDecT]
        apply TMComponent.atom_reachesExit _ input bound tapes inHead hBounds inHead
        · simp [mkWorkAction, moveHead]
        · intro j; exact OneSidedTape.updateAndMove_stay_self (tapes j)
        · exact hBounds
      let tIdx : Fin k := ⟨idx.val, hLt⟩
      let prefA' := pA ++ (((List.finRange k).take idx.val).flatMap fA).map SimSym.bit
      let sufA' := (((List.finRange k).drop (idx.val + 1)).flatMap fA).map SimSym.bit ++ sA
      let prefB' := pB ++ (((List.finRange k).take idx.val).flatMap fB).map SimSym.bit
      let sufB' := (((List.finRange k).drop (idx.val + 1)).flatMap fB).map SimSym.bit ++ sB
      have hFullAEq : fullA = prefA' ++ (fA tIdx).map SimSym.bit ++ sufA' := by
        simp only [fullA, prefA', sufA', tIdx]
        conv_lhs => rw [hSplitRange idx.val hLt]
        rw [List.flatMap_append, List.flatMap_cons, List.map_append, List.map_append]
        simp only [List.append_assoc]
      have hFullBEq : fullB = prefB' ++ (fB tIdx).map SimSym.bit ++ sufB' := by
        simp only [fullB, prefB', sufB', tIdx]
        conv_lhs => rw [hSplitRange idx.val hLt]
        rw [List.flatMap_append, List.flatMap_cons, List.map_append, List.map_append]
        simp only [List.append_assoc]
      have hPrefALen : prefA'.length = pA.length + idx.val * tapeBitWidth Γ S := by
        simp [prefA', hTakeLen fA hFA_len idx.val hIdxLe]
      have hPrefBLen : prefB'.length = pB.length + idx.val * tapeBitWidth Γ S := by
        simp [prefB', hTakeLen fB hFB_len idx.val hIdxLe]
      have hBoundA' : prefA'.length + tapeBitWidth Γ S < bound tArgA := by
        rw [hPrefALen]
        have : (idx.val + 1) * tapeBitWidth Γ S ≤ k * tapeBitWidth Γ S :=
          Nat.mul_le_mul_right _ (by omega)
        rw [Nat.add_mul, Nat.one_mul] at this
        omega
      have hBoundB' : prefB'.length + tapeBitWidth Γ S < bound tArgB := by
        rw [hPrefBLen]
        have : (idx.val + 1) * tapeBitWidth Γ S ≤ k * tapeBitWidth Γ S :=
          Nat.mul_le_mul_right _ (by omega)
        rw [Nat.add_mul, Nat.one_mul] at this
        omega
      have hMA' : TapeMatches (tapes tArgA)
          (prefA' ++ (encodeTapeBits Γ (tapesA tIdx)).map SimSym.bit ++ sufA') prefA'.length := by
        rw [← hFullAEq, hPrefALen]; exact hMA
      have hMB' : TapeMatches (tapes tArgB)
          (prefB' ++ (encodeTapeBits Γ (tapesB tIdx)).map SimSym.bit ++ sufB') prefB'.length := by
        rw [← hFullBEq, hPrefBLen]; exact hMB
      obtain ⟨t1, hScanOne, hR1, hA1, hB1, hS1, hReg1⟩ :=
        scanWorkTape_reachesExit input bound S blank (tapesA tIdx) (tapesB tIdx)
          prefA' sufA' prefB' sufB' hBoundR hBoundA' hBoundB' hBoundS tapes inHead
          (hBounds tRegs) hMR hMA' hMB' hMS
      let summaries' : Fin k → TapeSummary Γ :=
        fun j => if j.val = idx.val then TapeSummary.ofBoundedTapes (tapesA tIdx) (tapesB tIdx)
                 else summaries j
      have hMapped := TMComponent.mapExit_reachesExit (scanWorkTape InputAlphabet Γ blank)
        (fun
          | none => (Sum.inr none : (Fin (k + 1) × (Fin k → TapeSummary Γ)) ⊕ Option (Fin k → TapeSummary Γ))
          | some ts =>
            if h : idx.val < k then
              let summaries' : Fin k → TapeSummary Γ :=
                fun j => if j.val = idx.val then ts else summaries j
              Sum.inl ((⟨idx.val + 1, by omega⟩ : Fin (k + 1)), summaries')
            else Sum.inr none)
        input bound hScanOne
      have hBranch := TMComponent.branch_reachesExit
        (TMComponent.atom fun _ scanned =>
          mkWorkAction (decide (idx.val < k)) scanned (fun _ => .stay))
        ((scanWorkTape InputAlphabet Γ blank).mapExit fun
          | none => (Sum.inr none : (Fin (k + 1) × (Fin k → TapeSummary Γ)) ⊕ Option (Fin k → TapeSummary Γ))
          | some ts =>
            if h : idx.val < k then
              let summaries' : Fin k → TapeSummary Γ :=
                fun j => if j.val = idx.val then ts else summaries j
              Sum.inl ((⟨idx.val + 1, by omega⟩ : Fin (k + 1)), summaries')
            else Sum.inr none)
        (TMComponent.atom fun _ scanned =>
          mkWorkAction (Sum.inr (some summaries)) scanned (fun _ => .stay))
        input bound true (e := Sum.inl ((⟨idx.val + 1, by omega⟩ : Fin (k + 1)), summaries'))
        hAtomBranch
        (by
          dsimp only
          have hEq :
              (match some (TapeSummary.ofBoundedTapes (tapesA tIdx) (tapesB tIdx)) with
              | none => (Sum.inr none : (Fin (k + 1) × (Fin k → TapeSummary Γ)) ⊕ Option (Fin k → TapeSummary Γ))
              | some ts =>
                if h : idx.val < k then
                  let summaries' : Fin k → TapeSummary Γ :=
                    fun j => if j.val = idx.val then ts else summaries j
                  Sum.inl ((⟨idx.val + 1, by omega⟩ : Fin (k + 1)), summaries')
                else Sum.inr none) =
              Sum.inl ((⟨idx.val + 1, by omega⟩ : Fin (k + 1)), summaries') := by
            simp only [hLt, ↓reduceDIte, summaries']
          rwa [← hEq])
      refine ⟨(⟨idx.val + 1, by omega⟩, summaries'), t1, inHead, hBranch,
        ⟨rfl, ?_, hR1, ?_, ?_, hS1, ?_⟩, by simp [measure]; omega⟩
      · intro t ht
        dsimp only at ht
        dsimp only [summaries']
        by_cases htEq : t.val = idx.val
        · have htFin : t = tIdx := Fin.ext htEq
          simp [htFin, tIdx]
        · simp only [htEq, ↓reduceIte]
          exact hPrev t (by omega)
      · have hHeadEq : pA.length + (idx.val + 1) * tapeBitWidth Γ S =
            prefA'.length + tapeBitWidth Γ S := by
          rw [hPrefALen, Nat.add_mul, Nat.one_mul, Nat.add_assoc]
        rw [hHeadEq, hFullAEq]
        exact hA1
      · have hHeadEq : pB.length + (idx.val + 1) * tapeBitWidth Γ S =
            prefB'.length + tapeBitWidth Γ S := by
          rw [hPrefBLen, Nat.add_mul, Nat.one_mul, Nat.add_assoc]
        rw [hHeadEq, hFullBEq]
        exact hB1
      · rw [hReg1, hReg]
    · right
      have hIdxEq : idx.val = k := by omega
      have hDecF : decide (idx.val < k) = false := decide_eq_false hLt
      have hAtomBranch :
          (TMComponent.atom fun (_ : InputSymbol InputAlphabet) (scanned : Fin 5 → SimSym) =>
            mkWorkAction (decide (idx.val < k)) scanned (fun _ => .stay)).ReachesExit
            input bound tapes inHead false tapes inHead := by
        rw [← hDecF]
        apply TMComponent.atom_reachesExit _ input bound tapes inHead hBounds inHead
        · simp [mkWorkAction, moveHead]
        · intro j; exact OneSidedTape.updateAndMove_stay_self (tapes j)
        · exact hBounds
      have hAtomExit :
          (TMComponent.atom fun (_ : InputSymbol InputAlphabet) (scanned : Fin 5 → SimSym) =>
            mkWorkAction (Sum.inr (some summaries) :
              (Fin (k + 1) × (Fin k → TapeSummary Γ)) ⊕ Option (Fin k → TapeSummary Γ))
              scanned (fun _ => .stay)).ReachesExit
            input bound tapes inHead (.inr (some summaries)) tapes inHead := by
        apply TMComponent.atom_reachesExit _ input bound tapes inHead hBounds inHead
        · simp [mkWorkAction, moveHead]
        · intro j; exact OneSidedTape.updateAndMove_stay_self (tapes j)
        · exact hBounds
      have hBranch := TMComponent.branch_reachesExit
        (TMComponent.atom fun _ scanned =>
          mkWorkAction (decide (idx.val < k)) scanned (fun _ => .stay))
        ((scanWorkTape InputAlphabet Γ blank).mapExit fun
          | none => (Sum.inr none : (Fin (k + 1) × (Fin k → TapeSummary Γ)) ⊕ Option (Fin k → TapeSummary Γ))
          | some ts =>
            if h : idx.val < k then
              let summaries' : Fin k → TapeSummary Γ :=
                fun j => if j.val = idx.val then ts else summaries j
              Sum.inl ((⟨idx.val + 1, by omega⟩ : Fin (k + 1)), summaries')
            else Sum.inr none)
        (TMComponent.atom fun _ scanned =>
          mkWorkAction (Sum.inr (some summaries)) scanned (fun _ => .stay))
        input bound false hAtomBranch (by simpa using hAtomExit)
      have hSumEq : summaries = fun t => TapeSummary.ofBoundedTapes (tapesA t) (tapesB t) := by
        funext t
        exact hPrev t (by omega)
      refine ⟨some summaries, tapes, inHead, hBranch, rfl, by rw [hSumEq], hMR,
        by simpa [hIdxEq] using hMA, by simpa [hIdxEq] using hMB, hMS, hReg⟩
  have hInitInv : Inv (⟨0, Nat.zero_lt_succ k⟩, fun _ => defaultTapeSummary blank)
      initTapes inHead := by
    refine ⟨rfl, fun t ht => by simp at ht, hMatchR, ?_, ?_, hMatchS, rfl⟩
    · simpa [fullA] using hMatchA
    · simpa [fullB] using hMatchB
  obtain ⟨res, finalTapes, finalInHead, hRun, hHead, hRes, hFR, hFA, hFB, hFS, hReg⟩ :=
    loopWithState_reachesExit
      (⟨0, Nat.zero_lt_succ k⟩, fun _ : Fin k => defaultTapeSummary blank)
      (scanAllWorkTapesStep InputAlphabet Γ k blank) input bound Inv measure Post hStep
      initTapes inHead hInitInv
  subst finalInHead
  subst hRes
  exact ⟨finalTapes, hRun, hFR, hFA, hFB, hFS, hReg⟩

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

/-- Full serialized transition-table checker comparing `tArgA` (`before`) and
`tArgB` (`after`) against `M.transitions`, rewinding `tArgA`, `tArgB`, `tRuler`,
`tScratch`, and the physical input head to their initial positions. -/
noncomputable def checkStep {Q InputAlphabet Γ : Type*} {k : ℕ}
    [Fintype Q] [Fintype InputAlphabet] [Fintype Γ]
    (M : MultitapeNTM Q InputAlphabet Γ k) :=
  letI := Classical.propDecidable
  (rewindInput InputAlphabet 5).seq
    (bindComponent (readControlStates Q InputAlphabet) fun qOpt =>
      bindComponent (readInputHeadAndCheck InputAlphabet) fun inPair =>
        bindComponent (scanAllWorkTapes InputAlphabet Γ k M.blank) fun sumOpt =>
          ((rewindTape InputAlphabet tArgA).seq (rewindTape InputAlphabet tArgB)).seq
            (TMComponent.atom fun _ scanned =>
              mkWorkAction (checkStepEval M qOpt inPair sumOpt) scanned (fun _ => .stay)))

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
  · simpa [checkStep] using hFull
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

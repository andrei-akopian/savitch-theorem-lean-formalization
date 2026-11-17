module

public import SavitchLemma.Simulator.ConfigCheckB

@[expose] public section

/-!
# Top-level `checkValidB` component on `tArgB`

Checks that a `configBitWidth Q Γ k S`-bit list on `tArgB` has:
1. a valid control state (`qBits Q` decodes in `Q`),
2. `k` valid work-tape blocks (head `< S` and every `gammaBits Γ` cell decodes in `Γ`), and
3. the `[true, false]` valid-ID suffix,
rewinding `tRuler`, `tArgB`, and `tScratch` back to `1`.
-/

namespace SavitchLemma

/-- Check that `tArgB` holds a `configBitWidth Q Γ k S`-bit string with valid `Q`,
valid work-tape heads (`< S`), valid `Γ` cells, and trailing `[true, false]`. -/
noncomputable def checkValidB (Q InputAlphabet Γ : Type*) [Fintype Q] [Fintype Γ] (k : ℕ) :=
  bindComponent (readFixedBits1 InputAlphabet (qBits Q) tArgB) fun qOpt =>
    let qOk := match qOpt with
      | some f => (decodeBitsOpt (qBits Q) Q f).isSome
      | none => false
    ((skipFixedBits1 InputAlphabet 2 tArgB).seq (skipRulerScaledB InputAlphabet 1)).seq
      (bindComponent
        (loopWithState ((⟨0, Nat.zero_lt_succ k⟩ : Fin (k + 1)), qOk) fun st =>
          TMComponent.branch
            (TMComponent.atom fun (_ : InputSymbol InputAlphabet) (scanned : Fin 5 → SimSym) =>
              mkWorkAction (decide (st.1.val < k)) scanned (fun _ => .stay))
            (bindComponent (copySFromBToScratch InputAlphabet) fun _ =>
              bindComponent (testScratchLtS InputAlphabet) fun hdOk =>
                bindComponent (checkCellsDecode InputAlphabet Γ) fun cellsOk =>
                  TMComponent.atom fun (_ : InputSymbol InputAlphabet) (scanned : Fin 5 → SimSym) =>
                    mkWorkAction
                      (.inl (⟨min (st.1.val + 1) k, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩,
                        st.2 && hdOk && cellsOk) :
                        Fin (k + 1) × Bool ⊕ Bool)
                      scanned (fun _ => .stay))
            (TMComponent.atom fun (_ : InputSymbol InputAlphabet) (scanned : Fin 5 → SimSym) =>
              mkWorkAction (.inr st.2 : Fin (k + 1) × Bool ⊕ Bool) scanned (fun _ => .stay)))
        fun tapesOk =>
          bindComponent (readFixedBits1 InputAlphabet 2 tArgB) fun tagOpt =>
            let tagOk := match tagOpt with
              | some f => f ⟨0, by decide⟩ && !f ⟨1, by decide⟩
              | none => false
            (rewindTape InputAlphabet tArgB).mapExit (fun _ => tapesOk && tagOk))

private theorem flatMap_finRange_take_tape {Γ : Type*} [Fintype Γ] {k S : ℕ}
    (tapesB : Fin k → BoundedTape Γ S) (m : ℕ) (hm : m ≤ k) :
    ((List.finRange k).flatMap (fun t => encodeTapeBits Γ (tapesB t))).take
        (m * tapeBitWidth Γ S) =
      (List.finRange m).flatMap (fun t =>
        encodeTapeBits Γ (tapesB ⟨t.val, by have := t.isLt; omega⟩)) := by
  have hFinRangeSucc : ∀ p, List.finRange (p + 1) =
      (List.finRange p).map Fin.castSucc ++ [Fin.last p] := by
    intro p; apply List.ext_getElem
    · simp
    · intro idx hi1 hi2
      by_cases hIdx : idx < p
      · simp [List.getElem_append_left, hIdx]
      · have hEq : idx = p := by simp at hi1; omega
        subst hEq; rw [List.getElem_append_right (by simp)]; simp [Fin.ext_iff]
  induction m with
  | zero => simp
  | succ m ih =>
    rw [hFinRangeSucc, List.flatMap_append, List.flatMap_map, List.flatMap_singleton]
    have hFlatDrop : ((List.finRange k).flatMap (fun t => encodeTapeBits Γ (tapesB t))).drop
        (m * tapeBitWidth Γ S) =
        ((List.finRange k).drop m).flatMap (fun t => encodeTapeBits Γ (tapesB t)) := by
      clear ih
      induction m with
      | zero => simp
      | succ p ihp =>
        rw [Nat.succ_mul, ← List.drop_drop, ihp (by omega)]
        have hDropP : (List.finRange k).drop p =
            ⟨p, by omega⟩ :: (List.finRange k).drop (p + 1) := by
          rw [← List.getElem_cons_drop (by simp; omega)]; simp
        rw [hDropP, List.flatMap_cons,
          List.drop_append_of_le_length (by simp [encodeTapeBits_length])]
        simp [encodeTapeBits_length]
    have hDrop : ((List.finRange k).drop m) =
        ⟨m, by omega⟩ :: (List.finRange k).drop (m + 1) := by
      rw [← List.getElem_cons_drop (by simp; omega)]; simp
    have hEqTake : ((List.finRange k).flatMap (fun t => encodeTapeBits Γ (tapesB t))).take
          ((m + 1) * tapeBitWidth Γ S) =
        ((List.finRange k).flatMap (fun t => encodeTapeBits Γ (tapesB t))).take
          (m * tapeBitWidth Γ S) ++
        encodeTapeBits Γ (tapesB ⟨m, by omega⟩) := by
      rw [Nat.succ_mul, ← List.take_append_drop (m * tapeBitWidth Γ S)
        (((List.finRange k).flatMap (fun t => encodeTapeBits Γ (tapesB t))).take
          (m * tapeBitWidth Γ S + tapeBitWidth Γ S))]
      congr 1
      · rw [List.take_take, Nat.min_eq_left (by omega)]
      · rw [List.drop_take, show m * tapeBitWidth Γ S + tapeBitWidth Γ S - m * tapeBitWidth Γ S =
          tapeBitWidth Γ S by omega, hFlatDrop, hDrop, List.flatMap_cons,
          List.take_left' (encodeTapeBits_length _ _)]
    rw [hEqTake, ih (by omega)]
    rfl

theorem checkValidB_reachesExit {Q InputAlphabet Γ : Type*} {k n : ℕ}
    [Fintype Q] [Fintype Γ]
    (input : Fin n → InputAlphabet) (bound : Fin 5 → ℕ)
    (S : ℕ) (bs : List Bool) (hLen : bs.length = configBitWidth Q Γ k S)
    (hBoundR : S + 2 ≤ bound tRuler)
    (hBoundB : configBitWidth Q Γ k S + 2 ≤ bound tArgB)
    (hBoundS : S + 2 ≤ bound tScratch)
    (initTapes : Fin 5 → OneSidedTape SimSym) (inHead : Fin (n + 2))
    (hOtherBounds : ∀ j, j ≠ tRuler → j ≠ tArgB → j ≠ tScratch → (initTapes j).head < bound j)
    (hMatchR : TapeMatches (initTapes tRuler)
      (.leftMark :: List.replicate S (.bit true) ++ [.endMark]) 1)
    (hMatchB : TapeMatches (initTapes tArgB)
      (.leftMark :: bs.map SimSym.bit ++ [.endMark]) 1)
    (hMatchS : TapeMatches (initTapes tScratch) [.leftMark] 1) :
    ∃ (res : Bool) (ftR ftB ftS : OneSidedTape SimSym),
      (checkValidB Q InputAlphabet Γ k).ReachesExit input bound initTapes inHead res
        (fun j => if j = tRuler then ftR else if j = tArgB then ftB
          else if j = tScratch then ftS else initTapes j)
        inHead ∧
      TapeMatches ftR (.leftMark :: List.replicate S (.bit true) ++ [.endMark]) 1 ∧
      TapeMatches ftB (.leftMark :: bs.map SimSym.bit ++ [.endMark]) 1 ∧
      TapeMatches ftS [.leftMark] 1 ∧
      (res = true ↔
        ∃ (qB : Q) (inBs : List Bool) (tapesB : Fin k → BoundedTape Γ S),
          inBs.length = S + 2 ∧
          bs = natToBits (qBits Q) (Fintype.equivFin Q qB).val ++ inBs ++
            (List.finRange k).flatMap (fun t => encodeTapeBits Γ (tapesB t)) ++ [true, false]) := by
  let qW := qBits Q
  let inW := S + 2
  let tW := tapeBitWidth Γ S
  let qSlice := bs.take qW
  let inSlice := (bs.drop qW).take inW
  let tapesSlice := (bs.drop (qW + inW)).take (k * tW)
  let tagSlice := bs.drop (qW + inW + k * tW)
  have hQSliceLen : qSlice.length = qW := by
    simp [qSlice, List.length_take, hLen, configBitWidth]; omega
  have hInSliceLen : inSlice.length = inW := by
    simp only [inSlice, List.length_take, List.length_drop, hLen, configBitWidth, inW]
    dsimp only [qW]
    omega
  have hTapesSliceLen : tapesSlice.length = k * tW := by
    simp only [tapesSlice, List.length_take, List.length_drop, hLen, configBitWidth]
    dsimp only [qW, inW, tW]
    omega
  have hTagSliceLen : tagSlice.length = 2 := by
    simp only [tagSlice, List.length_drop, hLen, configBitWidth, qW, inW, tW]
    omega
  have hBsSplit : bs = qSlice ++ inSlice ++ tapesSlice ++ tagSlice := by
    have h1 : bs = bs.take qW ++ bs.drop qW := (List.take_append_drop qW bs).symm
    have h2 : bs.drop qW = inSlice ++ bs.drop (qW + inW) := by
      rw [← List.take_append_drop inW (bs.drop qW), List.drop_drop]
    have h3 : bs.drop (qW + inW) = tapesSlice ++ tagSlice := by
      rw [← List.take_append_drop (k * tW) (bs.drop (qW + inW)), List.drop_drop]
    rw [h1, h2, h3]
    simp [qSlice, List.append_assoc]
  let fullB := SimSym.leftMark :: bs.map SimSym.bit ++ [SimSym.endMark]
  have hFullBLen : fullB.length = configBitWidth Q Γ k S + 2 := by
    simp [fullB, hLen]
  -- Step 1: read qBits Q
  let sQ := (inSlice ++ tapesSlice ++ tagSlice).map SimSym.bit ++ [SimSym.endMark]
  have hFullBQ : fullB = [SimSym.leftMark] ++ qSlice.map SimSym.bit ++ sQ := by
    simp only [fullB, sQ]
    conv_lhs => rw [hBsSplit]
    simp [List.map_append, List.append_assoc]
  have hMB_Q : TapeMatches (initTapes tArgB)
      ([SimSym.leftMark] ++ qSlice.map SimSym.bit ++ sQ) 1 := by
    rw [← hFullBQ]; exact hMatchB
  have hOtherB0 : ∀ j, j ≠ tArgB → (initTapes j).head < bound j := by
    intro j hjB
    by_cases hjR : j = tRuler
    · subst hjR; rw [hMatchR.head_eq]; omega
    · by_cases hjS : j = tScratch
      · subst hjS; rw [hMatchS.head_eq]; omega
      · exact hOtherBounds j hjR hjB hjS
  obtain ⟨ftB1, hReadQ, hFB1⟩ :=
    readFixedBits1_reachesExit qW tArgB input bound [SimSym.leftMark] sQ qSlice hQSliceLen
      (by simp only [List.length_singleton]; unfold configBitWidth at hBoundB; omega)
      initTapes inHead hOtherB0 hMB_Q
  let t1 := fun j => if j = tArgB then ftB1 else initTapes j
  let fQ : Fin qW → Bool := fun idx => qSlice[idx.val]'(by rw [hQSliceLen]; exact idx.isLt)
  let qOk := (decodeBitsOpt qW Q fQ).isSome
  have hQOkIff : qOk = true ↔ ∃ qB : Q, qSlice = natToBits qW (Fintype.equivFin Q qB).val := by
    have hPow : Fintype.card Q + 1 ≤ 2 ^ qW := Nat.le_pow_clog (by decide) _
    have hOfFn : List.ofFn fQ = qSlice := by
      apply List.ext_getElem
      · simp [hQSliceLen]
      · intro idx _ _; simp [fQ]
    simp only [qOk, Option.isSome_iff_exists, decodeBitsOpt_eq_some_iff hPow, hOfFn]
    constructor
    · rintro ⟨qB, hq⟩; exact ⟨qB, hq.symm⟩
    · rintro ⟨qB, hq⟩; exact ⟨qB, hq.symm⟩
  -- Step 2: skip S + 2 (2 + S * 1)
  have hT1B : TapeMatches (t1 tArgB) fullB (1 + qW) := by
    simpa [t1, hFullBQ] using hFB1
  have hT1OtherB : ∀ j, j ≠ tArgB → (t1 j).head < bound j := by
    intro j hjB; simp [t1, hjB, hOtherB0 j hjB]
  obtain ⟨ftB2, hSkip2, hFB2⟩ :=
    skipFixedBits1_reachesExit 2 tArgB input bound fullB (1 + qW)
      (by rw [hFullBLen]; unfold configBitWidth; omega)
      (by unfold configBitWidth at hBoundB; omega)
      t1 inHead hT1OtherB hT1B
  let t2 := fun j => if j = tArgB then ftB2 else t1 j
  have hT2OtherRB : ∀ j, j ≠ tRuler → j ≠ tArgB → (t2 j).head < bound j := by
    intro j hjR hjB; simp [t2, t1, hjB, hOtherB0 j hjB]
  have hT2MR : TapeMatches (t2 tRuler)
      (.leftMark :: List.replicate S (.bit true) ++ [.endMark]) 1 := by
    have hNe : tRuler ≠ tArgB := by decide
    simpa [t2, t1, hNe] using hMatchR
  obtain ⟨ftR3, ftB3, hSkipS, hFR3, hFB3⟩ :=
    skipRulerScaledB_reachesExit 1 input bound S fullB (1 + qW + 2)
      hBoundR (by rw [hFullBLen]; unfold configBitWidth; omega)
      (by unfold configBitWidth at hBoundB; omega)
      t2 inHead hT2OtherRB hT2MR (by simpa [t2] using hFB2)
  let t3 := fun j => if j = tRuler then ftR3 else if j = tArgB then ftB3 else t2 j
  have hSeqSkip := TMComponent.seq_reachesExit (skipFixedBits1 InputAlphabet 2 tArgB)
    (skipRulerScaledB InputAlphabet 1) input bound hSkip2 hSkipS
  have hT3Eq : t3 = fun j => if j = tRuler then ftR3 else if j = tArgB then ftB3
      else initTapes j := by
    funext j
    by_cases hjR : j = tRuler
    · subst hjR; simp [t3]
    · by_cases hjB : j = tArgB
      · subst hjB; simp [t3, hjR]
      · simp [t3, t2, t1, hjR, hjB]
  dsimp only [t3] at hT3Eq
  rw [hT3Eq] at hSeqSkip
  -- Step 3: loop k times over work tapes
  let loopTrueBranch := fun (st : Fin (k + 1) × Bool) =>
    bindComponent (copySFromBToScratch InputAlphabet) fun _ =>
      bindComponent (testScratchLtS InputAlphabet) fun hdOk =>
        bindComponent (checkCellsDecode InputAlphabet Γ) fun cellsOk =>
          TMComponent.atom fun (_ : InputSymbol InputAlphabet) (scanned : Fin 5 → SimSym) =>
            mkWorkAction
              (.inl (⟨min (st.1.val + 1) k, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩,
                st.2 && hdOk && cellsOk) :
                Fin (k + 1) × Bool ⊕ Bool)
              scanned (fun _ => .stay)
  let loopFalseBranch := fun (st : Fin (k + 1) × Bool) =>
    TMComponent.atom fun (_ : InputSymbol InputAlphabet) (scanned : Fin 5 → SimSym) =>
      mkWorkAction (.inr st.2 : Fin (k + 1) × Bool ⊕ Bool) scanned (fun _ => .stay)
  let loopBody := fun (st : Fin (k + 1) × Bool) =>
    TMComponent.branch
      (TMComponent.atom fun (_ : InputSymbol InputAlphabet) (scanned : Fin 5 → SimSym) =>
        mkWorkAction (decide (st.1.val < k)) scanned (fun _ => .stay))
      (loopTrueBranch st) (loopFalseBranch st)
  let tapeAt : ℕ → List Bool := fun i => (tapesSlice.drop (i * tW)).take tW
  let tapeValid : ℕ → Prop := fun i =>
    ∃ tp : BoundedTape Γ S, tapeAt i = encodeTapeBits Γ tp
  let Inv : Fin (k + 1) × Bool → (Fin 5 → OneSidedTape SimSym) → Fin (n + 2) → Prop :=
    fun st tapes curInHead =>
      st.1.val ≤ k ∧ curInHead = inHead ∧
      (st.2 = true ↔ qOk = true ∧ ∀ i, i < st.1.val → tapeValid i) ∧
      TapeMatches (tapes tRuler) (.leftMark :: List.replicate S (.bit true) ++ [.endMark]) 1 ∧
      TapeMatches (tapes tArgB) fullB (1 + qW + inW + st.1.val * tW) ∧
      TapeMatches (tapes tScratch) [.leftMark] 1 ∧
      (∀ j, j ≠ tRuler → j ≠ tArgB → j ≠ tScratch → tapes j = initTapes j)
  let measure : Fin (k + 1) × Bool → (Fin 5 → OneSidedTape SimSym) → Fin (n + 2) → ℕ :=
    fun st _ _ => k - st.1.val
  let Post : Bool → (Fin 5 → OneSidedTape SimSym) → Fin (n + 2) → Prop :=
    fun res tapes curInHead =>
      curInHead = inHead ∧
      (res = true ↔ qOk = true ∧ ∀ i, i < k → tapeValid i) ∧
      TapeMatches (tapes tRuler) (.leftMark :: List.replicate S (.bit true) ++ [.endMark]) 1 ∧
      TapeMatches (tapes tArgB) fullB (1 + qW + inW + k * tW) ∧
      TapeMatches (tapes tScratch) [.leftMark] 1 ∧
      (∀ j, j ≠ tRuler → j ≠ tArgB → j ≠ tScratch → tapes j = initTapes j)
  have hLoopStep : ∀ st tapes curInHead, Inv st tapes curInHead →
      (∃ st' tapes' curInHead',
        (loopBody st).ReachesExit input bound tapes curInHead (.inl st') tapes' curInHead' ∧
        Inv st' tapes' curInHead' ∧
        measure st' tapes' curInHead' < measure st tapes curInHead) ∨
      (∃ e tapes' curInHead',
        (loopBody st).ReachesExit input bound tapes curInHead (.inr e) tapes' curInHead' ∧
        Post e tapes' curInHead') := by
    rintro ⟨⟨idx, hIdxLt⟩, ok⟩ tapes curInHead ⟨hLe, hCurIn, hOkIff, hMR, hMB, hMS, hOthers⟩
    cases hCurIn
    have hBounds : ∀ j, (tapes j).head < bound j := by
      intro j
      by_cases hjR : j = tRuler
      · subst hjR; rw [hMR.head_eq]; omega
      · by_cases hjB : j = tArgB
        · subst hjB; rw [hMB.head_eq]
          have hLeMul : idx * tW ≤ k * tW := Nat.mul_le_mul_right _ hLe
          dsimp only [qW, inW, tW] at hLeMul ⊢
          unfold configBitWidth at hBoundB
          omega
        · by_cases hjS : j = tScratch
          · subst hjS; rw [hMS.head_eq]; omega
          · rw [hOthers j hjR hjB hjS]; exact hOtherBounds j hjR hjB hjS
    by_cases hIdxK : idx < k
    · left
      have hPeekTrue :
          (TMComponent.atom fun (_ : InputSymbol InputAlphabet) (scanned : Fin 5 → SimSym) =>
            mkWorkAction (decide (((⟨idx, hIdxLt⟩ : Fin (k + 1)), ok).1.val < k)) scanned
              (fun _ => .stay)).ReachesExit
            input bound tapes inHead true tapes inHead := by
        have hDec : decide (((⟨idx, hIdxLt⟩ : Fin (k + 1)), ok).1.val < k) = true := by
          change decide (idx < k) = true; simp [hIdxK]
        convert TMComponent.atom_reachesExit _ input bound tapes inHead hBounds inHead _ tapes _ hBounds
        · simp [mkWorkAction, hDec]
        · simp [mkWorkAction, moveHead]
        · intro j; simpa [mkWorkAction] using OneSidedTape.updateAndMove_stay_self (tapes j)
      let hdSlice := (tapeAt idx).take S
      let cellSlice := (tapeAt idx).drop S
      have hTapeLen : (tapeAt idx).length = tW := by
        simp only [tapeAt, List.length_take, List.length_drop, hTapesSliceLen]
        have hLeMul : (idx + 1) * tW ≤ k * tW := Nat.mul_le_mul_right tW hIdxK
        rw [Nat.succ_mul] at hLeMul
        omega
      have hHdLen : hdSlice.length = S := by
        simp only [hdSlice, List.length_take, hTapeLen, tW, tapeBitWidth]; omega
      have hCellLen : cellSlice.length = S * gammaBits Γ := by
        simp only [cellSlice, List.length_drop, hTapeLen, tW, tapeBitWidth]; omega
      have hPosB : 1 + qW + inW + idx * tW = (SimSym.leftMark ::
          (qSlice ++ inSlice ++ tapesSlice.take (idx * tW)).map SimSym.bit).length := by
        have hLeMul : idx * tW ≤ k * tW := Nat.mul_le_mul_right _ hLe
        simp only [List.length_cons, List.length_map, List.length_append, List.length_take,
          hQSliceLen, hInSliceLen, hTapesSliceLen, Nat.min_eq_left hLeMul]
        omega
      let pCopy := SimSym.leftMark ::
        (qSlice ++ inSlice ++ tapesSlice.take (idx * tW)).map SimSym.bit
      let sCopy := (cellSlice ++ tapesSlice.drop ((idx + 1) * tW) ++ tagSlice).map SimSym.bit ++
        [SimSym.endMark]
      have hTapeSplit : tapesSlice =
          tapesSlice.take (idx * tW) ++ tapeAt idx ++ tapesSlice.drop ((idx + 1) * tW) := by
        have h1 : idx * tW + tW = (idx + 1) * tW := (Nat.succ_mul idx tW).symm
        conv_lhs =>
          rw [← List.take_append_drop (idx * tW) tapesSlice,
            ← List.take_append_drop tW (tapesSlice.drop (idx * tW)), List.drop_drop, h1]
        simp only [tapeAt, List.append_assoc]
      have hFullBCopy : fullB = pCopy ++ hdSlice.map SimSym.bit ++ sCopy := by
        simp only [fullB, pCopy, sCopy]
        conv_lhs => rw [hBsSplit, hTapeSplit]
        have hTS : tapeAt idx = hdSlice ++ cellSlice := (List.take_append_drop S (tapeAt idx)).symm
        rw [hTS]
        simp [List.map_append, List.append_assoc]
      have hMBCopy : TapeMatches (tapes tArgB)
          (pCopy ++ hdSlice.map SimSym.bit ++ sCopy) pCopy.length := by
        rw [← hFullBCopy, ← hPosB]; exact hMB
      have hPCopyLen : pCopy.length = 1 + qW + inW + idx * tW := hPosB.symm
      have hCopyBoundB : pCopy.length + S < bound tArgB := by
        rw [hPCopyLen]
        have hLeMul : (idx + 1) * tW ≤ k * tW := Nat.mul_le_mul_right tW hIdxK
        rw [Nat.succ_mul] at hLeMul
        dsimp only [qW, inW, tW, tapeBitWidth] at hLeMul ⊢
        unfold configBitWidth at hBoundB
        dsimp only [tapeBitWidth] at hBoundB
        omega
      obtain ⟨ftR1, ftB1', ftS1, hCopyRun, hFR1, hFB1', hFS1⟩ :=
        copySFromBToScratch_reachesExit input bound S pCopy sCopy hdSlice hHdLen
          hBoundR hCopyBoundB hBoundS tapes inHead
          (fun j hjR hjB hjS => hBounds j) hMR hMBCopy hMS
      let ta := fun j => if j = tRuler then ftR1 else if j = tArgB then ftB1'
        else if j = tScratch then ftS1 else tapes j
      have hTaOtherRS : ∀ j, j ≠ tRuler → j ≠ tScratch → (ta j).head < bound j := by
        intro j hjR hjS
        by_cases hjB : j = tArgB
        · subst hjB; simp only [ta, hjR, ↓reduceIte]; rw [hFB1'.head_eq]; exact hCopyBoundB
        · simp [ta, hjR, hjB, hjS, hBounds j]
      obtain ⟨ftR2, ftS2, hTestRun, hFR2, hFS2⟩ :=
        testScratchLtS_reachesExit input bound S hdSlice hHdLen hBoundR hBoundS
          ta inHead hTaOtherRS (by simpa [ta] using hFR1)
          (by simpa [ta, show tScratch ≠ tRuler by decide, show tScratch ≠ tArgB by decide] using hFS1)
      let tb := fun j => if j = tRuler then ftR2 else if j = tScratch then ftS2 else ta j
      let pCells := pCopy ++ hdSlice.map SimSym.bit
      let sCells := (tapesSlice.drop ((idx + 1) * tW) ++ tagSlice).map SimSym.bit ++
        [SimSym.endMark]
      have hFullBCells : fullB = pCells ++ cellSlice.map SimSym.bit ++ sCells := by
        simp only [hFullBCopy, pCells, sCells, sCopy, List.map_append, List.append_assoc]
      have hTbMB : TapeMatches (tb tArgB) (pCells ++ cellSlice.map SimSym.bit ++ sCells) pCells.length := by
        have hNe1 : tArgB ≠ tRuler := by decide
        have hNe2 : tArgB ≠ tScratch := by decide
        simpa [tb, ta, hNe1, hNe2, pCells, sCells, sCopy, List.map_append, List.append_assoc, hHdLen] using hFB1'
      have hCellsBoundB : pCells.length + S * gammaBits Γ < bound tArgB := by
        simp only [pCells, List.length_append, List.length_map, hHdLen, hPCopyLen]
        have hLeMul : (idx + 1) * tW ≤ k * tW := Nat.mul_le_mul_right tW hIdxK
        rw [Nat.succ_mul] at hLeMul
        dsimp only [qW, inW, tW, tapeBitWidth] at hLeMul ⊢
        unfold configBitWidth at hBoundB
        dsimp only [tapeBitWidth] at hBoundB
        omega
      have hTbOtherRB : ∀ j, j ≠ tRuler → j ≠ tArgB → (tb j).head < bound j := by
        intro j hjR hjB
        by_cases hjS : j = tScratch
        · subst hjS; simp only [tb, hjR, ↓reduceIte]; rw [hFS2.head_eq]; omega
        · simp [tb, ta, hjR, hjB, hjS, hBounds j]
      obtain ⟨cellsOk, ftR3', ftB3', hCellsRun, hFR3', hFB3', hCellsIff⟩ :=
        checkCellsDecode_reachesExit input bound S pCells sCells cellSlice hCellLen
          hBoundR hCellsBoundB tb inHead hTbOtherRB (by simpa [tb] using hFR2) hTbMB
      let tc := fun j => if j = tRuler then ftR3' else if j = tArgB then ftB3' else tb j
      have hTcBounds : ∀ j, (tc j).head < bound j := by
        intro j
        by_cases hjR : j = tRuler
        · subst hjR; simp only [tc, ↓reduceIte]; rw [hFR3'.head_eq]; omega
        · by_cases hjB : j = tArgB
          · subst hjB; simp only [tc, hjR, ↓reduceIte]; rw [hFB3'.head_eq]; exact hCellsBoundB
          · simp only [tc, hjR, hjB, ↓reduceIte]; exact hTbOtherRB j hjR hjB
      have hStayAtom : (TMComponent.atom fun (_ : InputSymbol InputAlphabet) (scanned : Fin 5 → SimSym) =>
          mkWorkAction
            (.inl (⟨idx + 1, by omega⟩, ok && decide (bitsToNat hdSlice < S) && cellsOk) :
              Fin (k + 1) × Bool ⊕ Bool)
            scanned (fun _ => .stay)).ReachesExit
          input bound tc inHead
          (.inl (⟨idx + 1, by omega⟩, ok && decide (bitsToNat hdSlice < S) && cellsOk)) tc inHead := by
        convert TMComponent.atom_reachesExit _ input bound tc inHead hTcBounds inHead _ tc _ hTcBounds
        · simp [mkWorkAction]
        · simp [mkWorkAction, moveHead]
        · intro j; simpa [mkWorkAction] using OneSidedTape.updateAndMove_stay_self (tc j)
      have hB3 := bindComponent_reachesExit (checkCellsDecode InputAlphabet Γ)
        (fun cOk => TMComponent.atom fun _ scanned =>
          mkWorkAction (.inl (⟨idx + 1, by omega⟩, ok && decide (bitsToNat hdSlice < S) && cOk) :
            Fin (k + 1) × Bool ⊕ Bool) scanned (fun _ => .stay))
        input bound hCellsRun hStayAtom
      have hB2 := bindComponent_reachesExit (testScratchLtS InputAlphabet)
        (fun hdOk => bindComponent (checkCellsDecode InputAlphabet Γ) fun cOk =>
          TMComponent.atom fun _ scanned =>
            mkWorkAction (.inl (⟨idx + 1, by omega⟩, ok && hdOk && cOk) :
              Fin (k + 1) × Bool ⊕ Bool) scanned (fun _ => .stay))
        input bound hTestRun hB3
      have hB1 := bindComponent_reachesExit (copySFromBToScratch InputAlphabet)
        (fun _ => bindComponent (testScratchLtS InputAlphabet) fun hdOk =>
          bindComponent (checkCellsDecode InputAlphabet Γ) fun cOk =>
            TMComponent.atom fun _ scanned =>
              mkWorkAction (.inl (⟨idx + 1, by omega⟩, ok && hdOk && cOk) :
                Fin (k + 1) × Bool ⊕ Bool) scanned (fun _ => .stay))
        input bound hCopyRun hB2
      have hMinEq : (⟨min (idx + 1) k, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩ : Fin (k + 1)) =
          ⟨idx + 1, by omega⟩ := by
        ext; simp [Nat.min_eq_left (by omega : idx + 1 ≤ k)]
      have hB1' : (loopTrueBranch ((⟨idx, hIdxLt⟩ : Fin (k + 1)), ok)).ReachesExit input bound tapes inHead
          (.inl (⟨idx + 1, by omega⟩, ok && decide (bitsToNat hdSlice < S) && cellsOk)) tc inHead := by
        dsimp only [loopTrueBranch]
        simpa [hMinEq] using hB1
      have hBranch := TMComponent.branch_reachesExit
        (TMComponent.atom fun (_ : InputSymbol InputAlphabet) (scanned : Fin 5 → SimSym) =>
          mkWorkAction (decide (((⟨idx, hIdxLt⟩ : Fin (k + 1)), ok).1.val < k)) scanned
            (fun _ => .stay))
        (loopTrueBranch ((⟨idx, hIdxLt⟩ : Fin (k + 1)), ok))
        (loopFalseBranch ((⟨idx, hIdxLt⟩ : Fin (k + 1)), ok))
        input bound true hPeekTrue hB1'
      have hTapeValidIff : (decide (bitsToNat hdSlice < S) && cellsOk) = true ↔ tapeValid idx := by
        simp only [Bool.and_eq_true, decide_eq_true_eq, hCellsIff, tapeValid]
        constructor
        · rintro ⟨hHdLt, cells, hCellsEq⟩
          refine ⟨{ cells := cells, head := ⟨bitsToNat hdSlice, hHdLt⟩ }, ?_⟩
          have hTS : tapeAt idx = hdSlice ++ cellSlice := (List.take_append_drop S (tapeAt idx)).symm
          rw [hTS, hCellsEq, encodeTapeBits]
          congr 1
          conv_lhs => rw [← natToBits_bitsToNat hdSlice, hHdLen]
        · rintro ⟨tp, hTpEq⟩
          have hHdEq : hdSlice = natToBits S tp.head.val := by
            simp only [hdSlice, hTpEq, encodeTapeBits, List.take_left' (natToBits_length S tp.head.val)]
          have hCellsEq : cellSlice = (List.finRange S).flatMap (fun c =>
              natToBits (gammaBits Γ) (Fintype.equivFin Γ (tp.cells c)).val) := by
            simp only [cellSlice, hTpEq, encodeTapeBits]
            rw [List.drop_append_of_le_length (by rw [natToBits_length]),
              List.drop_of_length_le (by rw [natToBits_length]), List.nil_append]
          refine ⟨?_, tp.cells, hCellsEq⟩
          rw [hHdEq, bitsToNat_natToBits_of_lt]
          · exact tp.head.isLt
          · exact lt_of_lt_of_le tp.head.isLt (Nat.lt_pow_self (by decide : 1 < 2)).le
      have hOkIff' : (ok && decide (bitsToNat hdSlice < S) && cellsOk) = true ↔
          qOk = true ∧ ∀ i, i < idx + 1 → tapeValid i := by
        rw [Bool.and_assoc, Bool.and_eq_true, hOkIff, hTapeValidIff]
        constructor
        · rintro ⟨⟨hq, hPrev⟩, hCur⟩
          refine ⟨hq, fun i hi => ?_⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hiLt | rfl
          · exact hPrev i hiLt
          · exact hCur
        · rintro ⟨hq, hAll⟩
          exact ⟨⟨hq, fun i hi => hAll i (Nat.lt_succ_of_lt hi)⟩, hAll idx (Nat.lt_succ_self idx)⟩
      have hTcR : TapeMatches (tc tRuler)
          (.leftMark :: List.replicate S (.bit true) ++ [.endMark]) 1 := by
        simpa [tc] using hFR3'
      have hTcB : TapeMatches (tc tArgB) fullB (1 + qW + inW + (idx + 1) * tW) := by
        have hNe : tArgB ≠ tRuler := by decide
        have hPosEq : pCells.length + S * gammaBits Γ = 1 + qW + inW + (idx + 1) * tW := by
          simp only [pCells, List.length_append, List.length_map, hHdLen, hPCopyLen]
          dsimp only [tW, tapeBitWidth]
          rw [Nat.succ_mul]
          omega
        simpa [tc, hNe, ← hFullBCells, hPosEq] using hFB3'
      have hTcS : TapeMatches (tc tScratch) [.leftMark] 1 := by
        have hNe1 : tScratch ≠ tRuler := by decide
        have hNe2 : tScratch ≠ tArgB := by decide
        simpa [tc, tb, hNe1, hNe2] using hFS2
      have hTcOthers : ∀ j, j ≠ tRuler → j ≠ tArgB → j ≠ tScratch → tc j = initTapes j := by
        intro j hjR hjB hjS
        simp [tc, tb, ta, hjR, hjB, hjS, hOthers j hjR hjB hjS]
      refine ⟨(⟨idx + 1, by omega⟩, ok && decide (bitsToNat hdSlice < S) && cellsOk),
        tc, inHead, hBranch, ⟨by omega, rfl, hOkIff', hTcR, hTcB, hTcS, hTcOthers⟩, ?_⟩
      change k - (idx + 1) < k - idx
      omega
    · right
      have hIdxEq : idx = k := by omega
      have hPeekFalse :
          (TMComponent.atom fun (_ : InputSymbol InputAlphabet) (scanned : Fin 5 → SimSym) =>
            mkWorkAction (decide (((⟨idx, hIdxLt⟩ : Fin (k + 1)), ok).1.val < k)) scanned
              (fun _ => .stay)).ReachesExit
            input bound tapes inHead false tapes inHead := by
        have hDec : decide (((⟨idx, hIdxLt⟩ : Fin (k + 1)), ok).1.val < k) = false := by
          change decide (idx < k) = false; simp [hIdxK]
        convert TMComponent.atom_reachesExit _ input bound tapes inHead hBounds inHead _ tapes _ hBounds
        · simp [mkWorkAction, hDec]
        · simp [mkWorkAction, moveHead]
        · intro j; simpa [mkWorkAction] using OneSidedTape.updateAndMove_stay_self (tapes j)
      have hStayAtom : (loopFalseBranch ((⟨idx, hIdxLt⟩ : Fin (k + 1)), ok)).ReachesExit
          input bound tapes inHead (.inr ok) tapes inHead := by
        dsimp only [loopFalseBranch]
        convert TMComponent.atom_reachesExit _ input bound tapes inHead hBounds inHead _ tapes _ hBounds
        · simp [mkWorkAction]
        · simp [mkWorkAction, moveHead]
        · intro j; simpa [mkWorkAction] using OneSidedTape.updateAndMove_stay_self (tapes j)
      have hBranch := TMComponent.branch_reachesExit
        (TMComponent.atom fun (_ : InputSymbol InputAlphabet) (scanned : Fin 5 → SimSym) =>
          mkWorkAction (decide (((⟨idx, hIdxLt⟩ : Fin (k + 1)), ok).1.val < k)) scanned
            (fun _ => .stay))
        (loopTrueBranch ((⟨idx, hIdxLt⟩ : Fin (k + 1)), ok))
        (loopFalseBranch ((⟨idx, hIdxLt⟩ : Fin (k + 1)), ok))
        input bound false hPeekFalse hStayAtom
      refine ⟨ok, tapes, inHead, hBranch, rfl, by simpa [hIdxEq] using hOkIff, hMR,
        by simpa [hIdxEq] using hMB, hMS, hOthers⟩
  have hInitInv : Inv ((⟨0, Nat.zero_lt_succ k⟩ : Fin (k + 1)), qOk)
      (fun j => if j = tRuler then ftR3 else if j = tArgB then ftB3 else initTapes j) inHead := by
    refine ⟨Nat.zero_le k, rfl, ?_, by simpa using hFR3, ?_, ?_, ?_⟩
    · simp
    · have hNe : tArgB ≠ tRuler := by decide
      simp only [hNe, ↓reduceIte]
      rw [show 1 + qW + inW + (((⟨0, Nat.zero_lt_succ k⟩ : Fin (k + 1)), qOk).1.val) * tW =
        1 + qW + 2 + S * 1 by dsimp only [inW]; omega]
      exact hFB3
    · have hNe1 : tScratch ≠ tRuler := by decide
      have hNe2 : tScratch ≠ tArgB := by decide
      simpa [hNe1, hNe2] using hMatchS
    · intro j hjR hjB hjS; simp [hjR, hjB]
  obtain ⟨tapesOk, tLoop, finalInHead, hLoop, hHead, hResIff, hRL, hBL, hSL, hOthersL⟩ :=
    loopWithState_reachesExit (⟨0, Nat.zero_lt_succ k⟩, qOk) loopBody input bound
      Inv measure Post hLoopStep
      (fun j => if j = tRuler then ftR3 else if j = tArgB then ftB3 else initTapes j)
      inHead hInitInv
  subst finalInHead
  -- Step 4: read 2-bit suffix and rewind tArgB
  let pTag := SimSym.leftMark :: (qSlice ++ inSlice ++ tapesSlice).map SimSym.bit
  have hFullBTag : fullB = pTag ++ tagSlice.map SimSym.bit ++ [SimSym.endMark] := by
    simp only [fullB, pTag]
    conv_lhs => rw [hBsSplit]
    simp [List.map_append, List.append_assoc]
  have hPTagLen : pTag.length = 1 + qW + inW + k * tW := by
    simp [pTag, hQSliceLen, hInSliceLen, hTapesSliceLen]
    omega
  have hTLoopOtherB : ∀ j, j ≠ tArgB → (tLoop j).head < bound j := by
    intro j hjB
    by_cases hjR : j = tRuler
    · subst hjR; rw [hRL.head_eq]; omega
    · by_cases hjS : j = tScratch
      · subst hjS; rw [hSL.head_eq]; omega
      · rw [hOthersL j hjR hjB hjS]; exact hOtherBounds j hjR hjB hjS
  obtain ⟨ftB4, hReadTag, hFB4⟩ :=
    readFixedBits1_reachesExit 2 tArgB input bound pTag [SimSym.endMark] tagSlice hTagSliceLen
      (by rw [hPTagLen]; dsimp only [qW, inW, tW]; unfold configBitWidth at hBoundB; omega)
      tLoop inHead hTLoopOtherB (by rw [hPTagLen, ← hFullBTag]; exact hBL)
  let t4 := fun j => if j = tArgB then ftB4 else tLoop j
  have hT4OtherB : ∀ j, j ≠ tArgB → (t4 j).head < bound j := by
    intro j hjB; simp [t4, hjB, hTLoopOtherB j hjB]
  have hFullBNoLeft : ∀ i, 1 ≤ i → i < fullB.length → fullB[i]? ≠ some SimSym.leftMark := by
    intro i hi1 hiLt
    cases i with
    | zero => omega
    | succ i =>
      simp only [fullB, List.length_append, List.length_cons, List.length_map,
        List.length_nil, hLen] at hiLt
      by_cases hiW : i < configBitWidth Q Γ k S
      · simp only [fullB]
        rw [List.getElem?_append_left (by simp [hLen]; omega), List.getElem?_cons_succ,
          List.getElem?_eq_getElem (by simp [hLen, hiW])]
        simp
      · have hiEq : i = configBitWidth Q Γ k S := by omega
        subst hiEq
        simp only [fullB]
        rw [List.getElem?_append_right (by simp [hLen])]
        simp [hLen]
  obtain ⟨ftB5, hRewB, hFB5, hOthersRewB⟩ :=
    rewindTape_reachesExit (InputAlphabet := InputAlphabet) tArgB input bound
      fullB (by simp [fullB]) (by simp [fullB]) hFullBNoLeft
      (by rw [hFullBLen]; exact hBoundB) t4 inHead hT4OtherB (pTag.length + 2)
      (by omega)
      (by rw [hFullBLen, hPTagLen]; dsimp only [qW, inW, tW]; unfold configBitWidth; omega)
      (by simpa [t4, ← hFullBTag] using hFB4)
  let fTag : Fin 2 → Bool := fun idx => tagSlice[idx.val]'(by rw [hTagSliceLen]; exact idx.isLt)
  let tagOk := fTag ⟨0, Nat.zero_lt_two⟩ && !fTag ⟨1, Nat.one_lt_two⟩
  have hMapRew := TMComponent.mapExit_reachesExit (rewindTape InputAlphabet tArgB)
    (fun _ => tapesOk && tagOk) input bound hRewB
  dsimp only [t4] at hMapRew
  have hBindTag := bindComponent_reachesExit (readFixedBits1 InputAlphabet 2 tArgB)
    (fun tagOpt =>
      let tagOk' := match tagOpt with
        | some f => f ⟨0, Nat.zero_lt_two⟩ && !f ⟨1, Nat.one_lt_two⟩
        | none => false
      (rewindTape InputAlphabet tArgB).mapExit (fun _ => tapesOk && tagOk'))
    input bound hReadTag hMapRew
  have hBindLoop := bindComponent_reachesExit _
    (fun tapesOk' =>
      bindComponent (readFixedBits1 InputAlphabet 2 tArgB) fun tagOpt =>
        let tagOk' := match tagOpt with
          | some f => f ⟨0, Nat.zero_lt_two⟩ && !f ⟨1, Nat.one_lt_two⟩
          | none => false
        (rewindTape InputAlphabet tArgB).mapExit (fun _ => tapesOk' && tagOk'))
    input bound hLoop hBindTag
  have hSeqFull := TMComponent.seq_reachesExit
    ((skipFixedBits1 InputAlphabet 2 tArgB).seq (skipRulerScaledB InputAlphabet 1)) _
    input bound hSeqSkip hBindLoop
  dsimp only [t1] at hSeqFull
  have hFull := bindComponent_reachesExit (readFixedBits1 InputAlphabet (qBits Q) tArgB)
    (fun qOpt =>
      let qOk' := match qOpt with
        | some f => (decodeBitsOpt (qBits Q) Q f).isSome
        | none => false
      ((skipFixedBits1 InputAlphabet 2 tArgB).seq (skipRulerScaledB InputAlphabet 1)).seq
        (bindComponent (loopWithState ((⟨0, Nat.zero_lt_succ k⟩ : Fin (k + 1)), qOk') loopBody)
          fun tapesOk' =>
            bindComponent (readFixedBits1 InputAlphabet 2 tArgB) fun tagOpt =>
              let tagOk' := match tagOpt with
                | some f => f ⟨0, Nat.zero_lt_two⟩ && !f ⟨1, Nat.one_lt_two⟩
                | none => false
              (rewindTape InputAlphabet tArgB).mapExit (fun _ => tapesOk' && tagOk')))
    input bound hReadQ hSeqFull
  have hEndEq : ftB5 = fun j => if j = tRuler then tLoop tRuler
      else if j = tArgB then ftB5 tArgB
      else if j = tScratch then tLoop tScratch else initTapes j := by
    funext j
    by_cases hjB : j = tArgB
    · subst hjB
      have h1 : tArgB ≠ tRuler := by decide
      simp [h1]
    · rw [hOthersRewB j hjB]
      simp only [t4, hjB, ↓reduceIte]
      by_cases hjR : j = tRuler
      · subst hjR; simp
      · by_cases hjS : j = tScratch
        · subst hjS; simp [hjR]
        · simp [hjR, hjS, hOthersL j hjR hjB hjS]
  rw [hEndEq] at hFull
  dsimp only [loopBody, loopTrueBranch, loopFalseBranch] at hFull
  refine ⟨tapesOk && tagOk, tLoop tRuler, ftB5 tArgB, tLoop tScratch,
    by dsimp only [checkValidB]; exact hFull, hRL, hFB5, hSL, ?_⟩
  have hTagIff : tagOk = true ↔ tagSlice = [true, false] := by
    have hTagList : tagSlice = [fTag ⟨0, by decide⟩, fTag ⟨1, by decide⟩] := by
      apply List.ext_getElem
      · simp [hTagSliceLen]
      · intro idx h1 h2
        rcases idx with _ | _ | idx
        · rfl
        · rfl
        · simp [hTagSliceLen] at h1; omega
    rw [hTagList]
    simp only [tagOk, Bool.and_eq_true, Bool.not_eq_true', List.cons.injEq, and_true]
  rw [Bool.and_eq_true, hResIff, hTagIff, hQOkIff]
  constructor
  · rintro ⟨⟨⟨qB, hQ⟩, hTapes⟩, hTag⟩
    choose tps hTps using fun t : Fin k => hTapes t.val t.isLt
    refine ⟨qB, inSlice, tps, hInSliceLen, ?_⟩
    have hTapesEq : tapesSlice = (List.finRange k).flatMap (fun t => encodeTapeBits Γ (tps t)) := by
      have hTake := flatMap_finRange_take_tape tps k (le_refl k)
      have hTakeAll : ((List.finRange k).flatMap (fun t => encodeTapeBits Γ (tps t))).take (k * tW) =
          (List.finRange k).flatMap (fun t => encodeTapeBits Γ (tps t)) := by
        apply List.take_of_length_le
        rw [List.length_flatMap]
        have hC : ∀ t ∈ List.finRange k, (encodeTapeBits Γ (tps t)).length = tW :=
          fun t _ => encodeTapeBits_length Γ (tps t)
        rw [List.map_congr_left hC, List.map_const', List.sum_replicate, List.length_finRange,
          smul_eq_mul]
      rw [hTakeAll] at hTake
      have hEqSlices : tapesSlice = (List.finRange k).flatMap (fun t =>
          encodeTapeBits Γ (tps ⟨t.val, t.isLt⟩)) := by
        -- Prove prefix by induction up to k
        have hPref : ∀ (m : ℕ) (hm : m ≤ k),
            tapesSlice.take (m * tW) = (List.finRange m).flatMap (fun t =>
              encodeTapeBits Γ (tps ⟨t.val, by have := t.isLt; omega⟩)) := by
          intro m hm
          induction m with
          | zero => simp
          | succ m ih =>
            have hFinRangeSucc : List.finRange (m + 1) =
                (List.finRange m).map Fin.castSucc ++ [Fin.last m] := by
              apply List.ext_getElem
              · simp
              · intro idx hi1 hi2
                by_cases hIdx : idx < m
                · simp [List.getElem_append_left, hIdx]
                · have hEq : idx = m := by simp at hi1; omega
                  subst hEq; rw [List.getElem_append_right (by simp)]; simp [Fin.ext_iff]
            rw [hFinRangeSucc, List.flatMap_append, List.flatMap_map, List.flatMap_singleton]
            have hEqTake : tapesSlice.take ((m + 1) * tW) = tapesSlice.take (m * tW) ++ tapeAt m := by
              rw [Nat.succ_mul, ← List.take_append_drop (m * tW)
                (tapesSlice.take (m * tW + tW))]
              congr 1
              · rw [List.take_take, Nat.min_eq_left (by omega)]
              · rw [List.drop_take, show m * tW + tW - m * tW = tW by omega]
            rw [hEqTake, ih (by omega), hTps ⟨m, by omega⟩]
            rfl
        have hAll := hPref k (le_refl k)
        rwa [List.take_of_length_le hTapesSliceLen.le] at hAll
      exact hEqSlices
    rw [hBsSplit, hQ, hTapesEq, hTag]
  · rintro ⟨qB, inBs, tps, hInLen, hBsEq⟩
    have hQSliceEq : qSlice = natToBits qW (Fintype.equivFin Q qB).val := by
      simp only [qSlice, hBsEq, List.append_assoc]
      rw [List.take_left' (natToBits_length _ _)]
    have hTapesSliceEq : tapesSlice =
        (List.finRange k).flatMap (fun t => encodeTapeBits Γ (tps t)) := by
      have hFlatLen : ((List.finRange k).flatMap (fun t => encodeTapeBits Γ (tps t))).length =
          k * tW := by
        rw [List.length_flatMap]
        have hC : ∀ t ∈ List.finRange k, (encodeTapeBits Γ (tps t)).length = tW :=
          fun t _ => encodeTapeBits_length Γ (tps t)
        rw [List.map_congr_left hC, List.map_const', List.sum_replicate, List.length_finRange,
          smul_eq_mul]
      have hQBitLen : (natToBits (qBits Q) (Fintype.equivFin Q qB).val).length = qW :=
        natToBits_length _ _
      simp only [tapesSlice, hBsEq, List.append_assoc]
      rw [List.drop_append, List.drop_of_length_le (by rw [hQBitLen]; omega), List.nil_append,
        hQBitLen, show qW + inW - qW = inW by omega]
      rw [List.drop_append, List.drop_of_length_le (by rw [hInLen]),
        List.nil_append, hInLen, show inW = S + 2 from rfl, Nat.sub_self, List.drop_zero]
      rw [List.take_append_of_le_length (by rw [hFlatLen]), List.take_of_length_le hFlatLen.le]
    have hTagSliceEq : tagSlice = [true, false] := by
      have hFlatLen : ((List.finRange k).flatMap (fun t => encodeTapeBits Γ (tps t))).length =
          k * tW := by
        rw [List.length_flatMap]
        have hC : ∀ t ∈ List.finRange k, (encodeTapeBits Γ (tps t)).length = tW :=
          fun t _ => encodeTapeBits_length Γ (tps t)
        rw [List.map_congr_left hC, List.map_const', List.sum_replicate, List.length_finRange,
          smul_eq_mul]
      have hQBitLen : (natToBits (qBits Q) (Fintype.equivFin Q qB).val).length = qW :=
        natToBits_length _ _
      simp only [tagSlice, hBsEq, List.append_assoc]
      rw [List.drop_append, List.drop_of_length_le (by rw [hQBitLen]; omega), List.nil_append,
        hQBitLen, show qW + inW + k * tW - qW = inW + k * tW by omega]
      rw [List.drop_append, List.drop_of_length_le (by rw [hInLen]; dsimp only [inW]; omega),
        List.nil_append, hInLen, show inW = S + 2 from rfl,
        show S + 2 + k * tW - (S + 2) = k * tW by omega]
      rw [List.drop_append, List.drop_of_length_le (by rw [hFlatLen]), List.nil_append,
        hFlatLen, Nat.sub_self, List.drop_zero]
    refine ⟨⟨⟨qB, hQSliceEq⟩, ?_⟩, hTagSliceEq⟩
    intro i hi
    refine ⟨tps ⟨i, hi⟩, ?_⟩
    simp only [tapeAt, hTapesSliceEq]
    have hFlatDrop : ((List.finRange k).flatMap (fun t => encodeTapeBits Γ (tps t))).drop (i * tW) =
        ((List.finRange k).drop i).flatMap (fun t => encodeTapeBits Γ (tps t)) := by
      induction i with
      | zero => simp
      | succ p ih =>
        rw [Nat.succ_mul, ← List.drop_drop, ih (by omega)]
        have hDropP : (List.finRange k).drop p = ⟨p, by omega⟩ :: (List.finRange k).drop (p + 1) := by
          rw [← List.getElem_cons_drop (by simp; omega)]; simp
        rw [hDropP, List.flatMap_cons,
          List.drop_append_of_le_length (by rw [encodeTapeBits_length])]
        simp [encodeTapeBits_length, show tW = tapeBitWidth Γ S from rfl]
    rw [hFlatDrop]
    have hDropI : (List.finRange k).drop i = ⟨i, hi⟩ :: (List.finRange k).drop (i + 1) := by
      rw [← List.getElem_cons_drop (by simp; omega)]; simp
    rw [hDropI, List.flatMap_cons, List.take_left' (encodeTapeBits_length _ _)]

end SavitchLemma

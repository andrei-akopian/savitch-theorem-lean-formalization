module

public import SavitchLemma.Simulator.CheckValidB

@[expose] public section

/-!
# Full configuration-validity checker on `tArgB`

1. `testScratchLtS`: tests whether the `S`-bit number on `tScratch` is `< S`
   using `tRuler` and `decScratch`, rewinding `tRuler` and clearing `tScratch`.
2. `checkCellsDecode`: scans `S` cells of `gammaBits Γ` bits on `tArgB`
   using `tRuler`, checking each decodes via `decodeBitsOpt (gammaBits Γ) Γ`.
3. `checkValidB`: checks that a `configBitWidth Q Γ k S`-bit list on `tArgB`
   has a valid `Q` state, `k` valid work-tape heads (`< S`) and cell symbols,
   and the `[true, false]` valid-ID suffix, rewinding `tArgB` afterward.
-/

namespace SavitchLemma

/-! ## 1. Testing `bitsToNat bits < S` on `tScratch` -/

private theorem bitsToNat_eq_zero_of_no_true : ∀ {bs : List Bool}, true ∉ bs → bitsToNat bs = 0
  | [], _ => rfl
  | b :: bs, h => by
    have hb : b = false := by cases b <;> [rfl; exact False.elim (h (by simp))]
    subst hb
    simp [bitsToNat, bitsToNat_eq_zero_of_no_true (fun hIn => h (List.mem_cons_of_mem _ hIn))]

/-- Test whether the `S`-bit little-endian number on `tScratch` is `< S` by
repeatedly stepping `tRuler` right and decrementing `tScratch`. Rewinds
`tRuler` to `1` and clears `tScratch` to `[.leftMark]` at `1`. -/
def testScratchLtS (InputAlphabet : Type*) :=
  bindComponent
    (loopWithState () fun (_ : Unit) =>
      TMComponent.branch
        (TMComponent.atom fun (_ : InputSymbol InputAlphabet) (scanned : Fin 5 → SimSym) =>
          match scanned tRuler with
          | .bit true =>
            mkWorkAction true scanned (fun j => if j = tRuler then .right else .stay)
          | _ =>
            mkWorkAction false scanned (fun _ => .stay))
        (bindComponent (decScratch InputAlphabet tScratch) fun decOk =>
          TMComponent.atom fun _ scanned =>
            mkWorkAction (if decOk then (.inl () : Unit ⊕ Bool) else (.inr true : Unit ⊕ Bool))
              scanned (fun _ => .stay))
        (TMComponent.atom fun _ scanned =>
          mkWorkAction (.inr false : Unit ⊕ Bool) scanned (fun _ => .stay)))
    fun res =>
      ((rewindTape InputAlphabet tRuler).seq (clearTape InputAlphabet tScratch)).mapExit
        (fun _ => res)

private theorem testScratchLtS_loop_reachesExit {InputAlphabet : Type*} {n : ℕ}
    (input : Fin n → InputAlphabet) (bound : Fin 5 → ℕ)
    (S : ℕ) (bits : List Bool) (hLen : bits.length = S)
    (hBoundR : S + 2 ≤ bound tRuler) (hBoundS : S + 2 ≤ bound tScratch)
    (initTapes : Fin 5 → OneSidedTape SimSym) (inHead : Fin (n + 2))
    (hOtherBounds : ∀ j, j ≠ tRuler → j ≠ tScratch → (initTapes j).head < bound j)
    (hMatchR : TapeMatches (initTapes tRuler)
      (.leftMark :: List.replicate S (.bit true) ++ [.endMark]) 1)
    (hMatchS : TapeMatches (initTapes tScratch)
      (.leftMark :: bits.map SimSym.bit ++ [.endMark]) 1) :
    ∃ (posR : ℕ) (ftR ftS : OneSidedTape SimSym) (bits' : List Bool),
      1 ≤ posR ∧ posR ≤ 1 + S ∧ bits'.length = S ∧
      ((loopWithState () fun (_ : Unit) =>
        TMComponent.branch
          (TMComponent.atom fun (_ : InputSymbol InputAlphabet) (scanned : Fin 5 → SimSym) =>
            match scanned tRuler with
            | .bit true =>
              mkWorkAction true scanned (fun j => if j = tRuler then .right else .stay)
            | _ =>
              mkWorkAction false scanned (fun _ => .stay))
          (bindComponent (decScratch InputAlphabet tScratch) fun decOk =>
            TMComponent.atom fun _ scanned =>
              mkWorkAction (if decOk then (.inl () : Unit ⊕ Bool) else (.inr true : Unit ⊕ Bool))
                scanned (fun _ => .stay))
          (TMComponent.atom fun _ scanned =>
            mkWorkAction (.inr false : Unit ⊕ Bool) scanned (fun _ => .stay))).ReachesExit
        input bound initTapes inHead (decide (bitsToNat bits < S))
        (fun j => if j = tRuler then ftR else if j = tScratch then ftS else initTapes j)
        inHead) ∧
      TapeMatches ftR (.leftMark :: List.replicate S (.bit true) ++ [.endMark]) posR ∧
      TapeMatches ftS (.leftMark :: bits'.map SimSym.bit ++ [.endMark]) 1 := by
  let rulerList := SimSym.leftMark :: List.replicate S (SimSym.bit true) ++ [SimSym.endMark]
  have hRLen : rulerList.length = S + 2 := by simp [rulerList]
  let peekAtom : TMComponent Unit InputAlphabet SimSym 5 Bool :=
    TMComponent.atom fun _ scanned =>
      match scanned tRuler with
      | .bit true => mkWorkAction true scanned (fun j => if j = tRuler then .right else .stay)
      | _ => mkWorkAction false scanned (fun _ => .stay)
  let trueBranch :=
    bindComponent (decScratch InputAlphabet tScratch) fun decOk =>
      TMComponent.atom fun _ scanned =>
        mkWorkAction (if decOk then (.inl () : Unit ⊕ Bool) else (.inr true : Unit ⊕ Bool))
          scanned (fun _ => .stay)
  let falseBranch :=
    TMComponent.atom fun (_ : InputSymbol InputAlphabet) (scanned : Fin 5 → SimSym) =>
      mkWorkAction (.inr false : Unit ⊕ Bool) scanned (fun _ => .stay)
  let body : Unit → _ := fun _ => TMComponent.branch peekAtom trueBranch falseBranch
  let Inv : Unit → (Fin 5 → OneSidedTape SimSym) → Fin (n + 2) → Prop :=
    fun _ tapes curInHead =>
      ∃ (i : ℕ) (curBits : List Bool),
        i ≤ S ∧ curBits.length = S ∧ curInHead = inHead ∧
        (bitsToNat bits < S ↔ bitsToNat curBits < S - i) ∧
        TapeMatches (tapes tRuler) rulerList (1 + i) ∧
        TapeMatches (tapes tScratch) (.leftMark :: curBits.map SimSym.bit ++ [.endMark]) 1 ∧
        (∀ j, j ≠ tRuler → j ≠ tScratch → tapes j = initTapes j)
  let measure : Unit → (Fin 5 → OneSidedTape SimSym) → Fin (n + 2) → ℕ :=
    fun _ tapes _ => (1 + S) - (tapes tRuler).head
  let Post : Bool → (Fin 5 → OneSidedTape SimSym) → Fin (n + 2) → Prop :=
    fun res tapes curInHead =>
      ∃ (posR : ℕ) (curBits : List Bool),
        1 ≤ posR ∧ posR ≤ 1 + S ∧ curBits.length = S ∧
        curInHead = inHead ∧ res = decide (bitsToNat bits < S) ∧
        TapeMatches (tapes tRuler) rulerList posR ∧
        TapeMatches (tapes tScratch) (.leftMark :: curBits.map SimSym.bit ++ [.endMark]) 1 ∧
        (∀ j, j ≠ tRuler → j ≠ tScratch → tapes j = initTapes j)
  have hStep : ∀ st tapes curInHead, Inv st tapes curInHead →
      (∃ st' tapes' curInHead',
        (body st).ReachesExit input bound tapes curInHead (.inl st') tapes' curInHead' ∧
        Inv st' tapes' curInHead' ∧
        measure st' tapes' curInHead' < measure st tapes curInHead) ∨
      (∃ e tapes' curInHead',
        (body st).ReachesExit input bound tapes curInHead (.inr e) tapes' curInHead' ∧
        Post e tapes' curInHead') := by
    rintro ⟨⟩ tapes curInHead ⟨i, curBits, hiLe, hCurLen, hCurIn, hIff, hMR, hMS, hOthers⟩
    cases hCurIn
    have hBounds : ∀ j, (tapes j).head < bound j := by
      intro j
      by_cases hjR : j = tRuler
      · subst hjR; rw [hMR.head_eq]; omega
      · by_cases hjS : j = tScratch
        · subst hjS; rw [hMS.head_eq]; omega
        · rw [hOthers j hjR hjS]; exact hOtherBounds j hjR hjS
    by_cases hiLt : i < S
    · have hReadR : (tapes tRuler).cells (tapes tRuler).head = .bit true := by
        rw [hMR.read_lt (by rw [hRLen]; omega)]
        simp only [rulerList, Nat.add_comm 1 i]
        rw [List.getElem_append_left (by simp; omega), List.getElem_cons_succ]
        simp
      obtain ⟨ntR, hUpdR, hFR⟩ := hMR.update_keep .right rfl
      let t1 := fun j => if j = tRuler then ntR else tapes j
      have hT1Bounds : ∀ j, (t1 j).head < bound j := by
        intro j
        by_cases hjR : j = tRuler
        · subst hjR; simpa [t1, hFR.head_eq] using (by omega : 1 + i + 1 < bound tRuler)
        · simp [t1, hjR, hBounds j]
      have hPeek : peekAtom.ReachesExit input bound tapes inHead true t1 inHead := by
        dsimp only [peekAtom]
        convert TMComponent.atom_reachesExit _ input bound tapes inHead hBounds inHead _ t1 _
          hT1Bounds
        · simp [mkWorkAction, hReadR]
        · simp [mkWorkAction, hReadR, moveHead]
        · intro j
          simp only [mkWorkAction, hReadR]
          by_cases hjR : j = tRuler
          · subst hjR; simpa [t1] using hUpdR
          · simp [t1, hjR, OneSidedTape.updateAndMove_stay_self]
      have hT1OtherS : ∀ j, j ≠ tScratch → (t1 j).head < bound j := by
        intro j hjS; exact hT1Bounds j
      have hT1MS : TapeMatches (t1 tScratch)
          (.leftMark :: curBits.map SimSym.bit ++ [.endMark]) 1 := by
        have hNe : tScratch ≠ tRuler := by decide
        simpa [t1, hNe] using hMS
      obtain ⟨decOk, ftS, bits', hBits'Len, hDec, hFS, hDecIff, hDecSucc, hDecFalse⟩ :=
        decScratch_reachesExit tScratch input bound curBits (by rw [hCurLen]; exact hBoundS)
          t1 inHead hT1OtherS hT1MS
      let t2 := fun j => if j = tScratch then ftS else t1 j
      have hT2Bounds : ∀ j, (t2 j).head < bound j := by
        intro j
        by_cases hjS : j = tScratch
        · subst hjS; simpa [t2, hFS.head_eq] using (by omega : 1 < bound tScratch)
        · simp [t2, hjS, hT1Bounds j]
      have hT2R : TapeMatches (t2 tRuler) rulerList (1 + (i + 1)) := by
        have hNe : tRuler ≠ tScratch := by decide
        simpa [t2, hNe, t1, Nat.add_assoc] using hFR
      have hT2S : TapeMatches (t2 tScratch)
          (.leftMark :: bits'.map SimSym.bit ++ [.endMark]) 1 := by
        simpa [t2] using hFS
      have hT2Others : ∀ j, j ≠ tRuler → j ≠ tScratch → t2 j = initTapes j := by
        intro j hjR hjS
        simp [t2, t1, hjR, hjS, hOthers j hjR hjS]
      cases hDecEq : decOk
      · -- decOk = false: curBits is all false, so bitsToNat curBits = 0 < S - i
        right
        have hNoTrue : ¬ true ∈ curBits := by
          intro hIn; have := hDecIff.mpr hIn; rw [hDecEq] at this; cases this
        have hCurZero : bitsToNat curBits = 0 := bitsToNat_eq_zero_of_no_true hNoTrue
        have hLtTrue : bitsToNat bits < S := by
          rw [hIff, hCurZero]; omega
        have hResTrue : true = decide (bitsToNat bits < S) := by
          simp [hLtTrue]
        have hStay : (TMComponent.atom fun _ (scanned : Fin 5 → SimSym) =>
            mkWorkAction (if false then (.inl () : Unit ⊕ Bool) else (.inr true : Unit ⊕ Bool))
              scanned (fun _ => .stay)).ReachesExit
            input bound t2 inHead (.inr true) t2 inHead := by
          convert TMComponent.atom_reachesExit _ input bound t2 inHead hT2Bounds inHead _ t2 _ hT2Bounds
          · simp [mkWorkAction]
          · simp [mkWorkAction, moveHead]
          · intro j; simpa [mkWorkAction] using OneSidedTape.updateAndMove_stay_self (t2 j)
        have hInner := bindComponent_reachesExit (decScratch InputAlphabet tScratch)
          (fun decOk => TMComponent.atom fun _ scanned =>
            mkWorkAction (if decOk then (.inl () : Unit ⊕ Bool) else (.inr true : Unit ⊕ Bool))
              scanned (fun _ => .stay))
          input bound (by simpa [hDecEq] using hDec) hStay
        have hOuter := TMComponent.branch_reachesExit peekAtom trueBranch falseBranch
          input bound true hPeek hInner
        refine ⟨true, t2, inHead, hOuter, 1 + (i + 1), bits', by omega, by omega,
          by omega, rfl, hResTrue, hT2R, hT2S, hT2Others⟩
      · -- decOk = true: bitsToNat bits' + 1 = bitsToNat curBits
        left
        have hSucc := hDecSucc hDecEq
        have hIff' : bitsToNat bits < S ↔ bitsToNat bits' < S - (i + 1) := by
          rw [hIff]; omega
        have hStay : (TMComponent.atom fun _ (scanned : Fin 5 → SimSym) =>
            mkWorkAction (if true then (.inl () : Unit ⊕ Bool) else (.inr true : Unit ⊕ Bool))
              scanned (fun _ => .stay)).ReachesExit
            input bound t2 inHead (.inl ()) t2 inHead := by
          convert TMComponent.atom_reachesExit _ input bound t2 inHead hT2Bounds inHead _ t2 _ hT2Bounds
          · simp [mkWorkAction]
          · simp [mkWorkAction, moveHead]
          · intro j; simpa [mkWorkAction] using OneSidedTape.updateAndMove_stay_self (t2 j)
        have hInner := bindComponent_reachesExit (decScratch InputAlphabet tScratch)
          (fun decOk => TMComponent.atom fun _ scanned =>
            mkWorkAction (if decOk then (.inl () : Unit ⊕ Bool) else (.inr true : Unit ⊕ Bool))
              scanned (fun _ => .stay))
          input bound (by simpa [hDecEq] using hDec) hStay
        have hOuter := TMComponent.branch_reachesExit peekAtom trueBranch falseBranch
          input bound true hPeek hInner
        refine ⟨(), t2, inHead, hOuter,
          ⟨i + 1, bits', by omega, by omega, rfl, hIff', hT2R, hT2S, hT2Others⟩, ?_⟩
        change 1 + S - (t2 tRuler).head < 1 + S - (tapes tRuler).head
        rw [hT2R.head_eq, hMR.head_eq]
        omega
    · -- i = S: tRuler scans .endMark, so bitsToNat curBits < 0 is false
      right
      have hiS : i = S := by omega
      have hReadR : (tapes tRuler).cells (tapes tRuler).head = .endMark := by
        rw [hMR.read_lt (by rw [hRLen]; omega)]
        simp only [rulerList, Nat.add_comm 1 i]
        rw [List.getElem_append_right (by simp [hiS])]
        simp [hiS]
      have hNotLt : ¬ bitsToNat bits < S := by
        rw [hIff, hiS]; omega
      have hResFalse : false = decide (bitsToNat bits < S) := by
        simp [hNotLt]
      have hPeek : peekAtom.ReachesExit input bound tapes inHead false tapes inHead := by
        dsimp only [peekAtom]
        convert TMComponent.atom_reachesExit _ input bound tapes inHead hBounds inHead _ tapes _ hBounds
        · simp [mkWorkAction, hReadR]
        · simp [mkWorkAction, hReadR, moveHead]
        · intro j; simpa [mkWorkAction, hReadR] using OneSidedTape.updateAndMove_stay_self (tapes j)
      have hStay : (TMComponent.atom fun _ (scanned : Fin 5 → SimSym) =>
          mkWorkAction (.inr false : Unit ⊕ Bool) scanned (fun _ => .stay)).ReachesExit
          input bound tapes inHead (.inr false) tapes inHead := by
        convert TMComponent.atom_reachesExit _ input bound tapes inHead hBounds inHead _ tapes _ hBounds
        · simp [mkWorkAction]
        · simp [mkWorkAction, moveHead]
        · intro j; simpa [mkWorkAction] using OneSidedTape.updateAndMove_stay_self (tapes j)
      have hOuter := TMComponent.branch_reachesExit peekAtom trueBranch falseBranch
        input bound false hPeek hStay
      refine ⟨false, tapes, inHead, hOuter, 1 + S, curBits, by omega, by omega, hCurLen,
        rfl, hResFalse, by simpa [hiS] using hMR, hMS, hOthers⟩
  obtain ⟨res, tLoop, finalInHead, hLoop, posR, bits', hPos1, hPosLe, hBits'Len, hHead, hRes,
      hRL, hSL, hOthersL⟩ :=
    loopWithState_reachesExit () body input bound Inv measure Post hStep initTapes inHead
      ⟨0, bits, Nat.zero_le S, hLen, rfl, by simp, hMatchR, hMatchS, fun _ _ _ => rfl⟩
  subst finalInHead
  subst hRes
  have hEndEq : tLoop = fun j => if j = tRuler then tLoop tRuler
      else if j = tScratch then tLoop tScratch else initTapes j := by
    funext j
    by_cases hjR : j = tRuler
    · subst hjR; simp
    · by_cases hjS : j = tScratch
      · subst hjS; simp [hjR]
      · simp [hjR, hjS, hOthersL j hjR hjS]
  rw [hEndEq] at hLoop
  exact ⟨posR, tLoop tRuler, tLoop tScratch, bits', hPos1, hPosLe, hBits'Len, hLoop, hRL, hSL⟩

theorem testScratchLtS_reachesExit {InputAlphabet : Type*} {n : ℕ}
    (input : Fin n → InputAlphabet) (bound : Fin 5 → ℕ)
    (S : ℕ) (bits : List Bool) (hLen : bits.length = S)
    (hBoundR : S + 2 ≤ bound tRuler) (hBoundS : S + 2 ≤ bound tScratch)
    (initTapes : Fin 5 → OneSidedTape SimSym) (inHead : Fin (n + 2))
    (hOtherBounds : ∀ j, j ≠ tRuler → j ≠ tScratch → (initTapes j).head < bound j)
    (hMatchR : TapeMatches (initTapes tRuler)
      (.leftMark :: List.replicate S (.bit true) ++ [.endMark]) 1)
    (hMatchS : TapeMatches (initTapes tScratch)
      (.leftMark :: bits.map SimSym.bit ++ [.endMark]) 1) :
    ∃ ftR ftS,
      (testScratchLtS InputAlphabet).ReachesExit input bound initTapes inHead
        (decide (bitsToNat bits < S))
        (fun j => if j = tRuler then ftR else if j = tScratch then ftS else initTapes j)
        inHead ∧
      TapeMatches ftR (.leftMark :: List.replicate S (.bit true) ++ [.endMark]) 1 ∧
      TapeMatches ftS [.leftMark] 1 := by
  obtain ⟨posR, ftR0, ftS0, bits', hPos1, hPosLe, hBits'Len, hLoop, hMR0, hMS0⟩ :=
    testScratchLtS_loop_reachesExit input bound S bits hLen hBoundR hBoundS
      initTapes inHead hOtherBounds hMatchR hMatchS
  let t1 := fun j => if j = tRuler then ftR0 else if j = tScratch then ftS0 else initTapes j
  let rulerList := SimSym.leftMark :: List.replicate S (SimSym.bit true) ++ [SimSym.endMark]
  let scratchList := SimSym.leftMark :: bits'.map SimSym.bit ++ [SimSym.endMark]
  have hRLen : rulerList.length = S + 2 := by simp [rulerList]
  have hSLen : scratchList.length = S + 2 := by simp [scratchList, hBits'Len]
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
  have hT1OtherR : ∀ j, j ≠ tRuler → (t1 j).head < bound j := by
    intro j hjR
    by_cases hjS : j = tScratch
    · subst hjS; simp only [t1, hjR, ↓reduceIte]; rw [hMS0.head_eq]; omega
    · simp only [t1, hjR, hjS, ↓reduceIte]; exact hOtherBounds j hjR hjS
  obtain ⟨tRewR, hRewR, hRFin, hOthersR⟩ :=
    rewindTape_reachesExit (InputAlphabet := InputAlphabet) tRuler input bound
      rulerList (by simp [rulerList]) (by simp [rulerList]) hRulerNoLeft
      (by rw [hRLen]; exact hBoundR) t1 inHead hT1OtherR posR hPos1
      (by rw [hRLen]; omega) (by simpa [t1, rulerList, List.append_assoc] using hMR0)
  have hRewROtherS : ∀ j, j ≠ tScratch → (tRewR j).head < bound j := by
    intro j hjS
    by_cases hjR : j = tRuler
    · subst hjR; rw [hRFin.head_eq]; omega
    · rw [hOthersR j hjR]; exact hT1OtherR j hjR
  have hMS0' : TapeMatches (tRewR tScratch) scratchList 1 := by
    rw [hOthersR tScratch (by decide)]
    simpa [t1, scratchList, List.append_assoc, show tScratch ≠ tRuler by decide] using hMS0
  obtain ⟨tClrS, hClrS, hSFin⟩ :=
    clearTape_reachesExit (InputAlphabet := InputAlphabet) tScratch input bound
      (bits'.map SimSym.bit) (by simp [hBits'Len]; exact hBoundS)
      (by intro s hs; rcases List.mem_map.mp hs with ⟨b, _, rfl⟩; simp)
      tRewR inHead hRewROtherS hMS0'
  have hSeqRC := TMComponent.seq_reachesExit (rewindTape InputAlphabet tRuler)
    (clearTape InputAlphabet tScratch) input bound hRewR hClrS
  have hMap := TMComponent.mapExit_reachesExit _ (fun _ => decide (bitsToNat bits < S))
    input bound hSeqRC
  dsimp only [t1] at hMap
  have hFull := bindComponent_reachesExit _
    (fun res => ((rewindTape InputAlphabet tRuler).seq (clearTape InputAlphabet tScratch)).mapExit
      (fun _ => res))
    input bound hLoop hMap
  have hEndEq : (fun j => if j = tScratch then tClrS else tRewR j) =
      fun j => if j = tRuler then tRewR tRuler
      else if j = tScratch then tClrS else initTapes j := by
    funext j
    by_cases hjS : j = tScratch
    · subst hjS
      have hNe : tScratch ≠ tRuler := by decide
      simp [hNe]
    · simp only [hjS, ↓reduceIte]
      by_cases hjR : j = tRuler
      · subst hjR; simp
      · rw [hOthersR j hjR]; simp [t1, hjR, hjS]
  rw [hEndEq] at hFull
  exact ⟨tRewR tRuler, tClrS, hFull, hRFin, hSFin⟩

end SavitchLemma

module

public import SavitchLemma.Simulator.Step.StepScanInput

@[expose] public section

/-!
# Per-tape cell scanner (`scanTapeCells`)

Sweeps `S` serialized cells on `tArgA` and `tArgB` in lockstep with `tRuler`
and the unary head-match counter on `tScratch`, computing `CellScanState Γ`
(scanned/written symbols and non-head equality) for `StepScanner`.
-/

namespace SavitchLemma

/-! ## 3. Per-tape cell scanner and `TapeSummary` computation -/

/-- State carried across the `S`-cell sweep of one work tape. -/
structure CellScanState (Γ : Type*) where
  hms : HeadMatchState
  ok : Bool
  scanned : Γ
  written : Γ
  valid : Bool
  deriving DecidableEq

instance {Γ : Type*} [Fintype Γ] : Fintype (CellScanState Γ) :=
  Fintype.ofEquiv (HeadMatchState × Bool × Γ × Γ × Bool)
    { toFun := fun ⟨h, o, s, w, v⟩ => ⟨h, o, s, w, v⟩
      invFun := fun st => (st.hms, st.ok, st.scanned, st.written, st.valid)
      left_inv := fun ⟨_, _, _, _, _⟩ => rfl
      right_inv := fun st => by cases st; rfl }

/-- Update `CellScanState` after reading one cell's `gammaBits Γ` bit-pair. -/
noncomputable def updateCellScanState {Γ : Type*} [Fintype Γ] [DecidableEq Γ]
    (st : CellScanState Γ) (hms' : HeadMatchState)
    (res : Option ((Fin (gammaBits Γ) → Bool) × (Fin (gammaBits Γ) → Bool))) :
    CellScanState Γ :=
  match res with
  | none => { st with hms := hms', valid := false }
  | some (fA, fB) =>
    match decodeBitsOpt (gammaBits Γ) Γ fA, decodeBitsOpt (gammaBits Γ) Γ fB with
    | some a, some b =>
      match hms' with
      | .atHead => { st with hms := hms', scanned := a, written := b }
      | .before | .pastHead =>
        { st with hms := hms', ok := st.ok && decide (a = b) }
    | _, _ => { st with hms := hms', valid := false }

/-- Advance `HeadMatchState` by one cell, decrementing `tScratch` only while
`hms = .before`. -/
def advanceHeadMatch (InputAlphabet : Type*) (hms : HeadMatchState) :=
  TMComponent.branch
    (TMComponent.atom fun _ scanned =>
      mkWorkAction (decide (hms = .before)) scanned (fun _ => .stay))
    ((decScratch InputAlphabet tScratch).mapExit fun b =>
      if b then HeadMatchState.before else HeadMatchState.atHead)
    (TMComponent.atom fun _ scanned =>
      mkWorkAction HeadMatchState.pastHead scanned (fun _ => .stay))

theorem advanceHeadMatch_before_reachesExit {InputAlphabet : Type*} {n : ℕ}
    (input : Fin n → InputAlphabet) (bound : Fin 5 → ℕ)
    (bits : List Bool) (hBound : bits.length + 2 ≤ bound tScratch)
    (initTapes : Fin 5 → OneSidedTape SimSym) (inHead : Fin (n + 2))
    (hOtherBounds : ∀ j, j ≠ tScratch → (initTapes j).head < bound j)
    (hMatch : TapeMatches (initTapes tScratch)
      (.leftMark :: bits.map SimSym.bit ++ [.endMark]) 1) :
    ∃ res ftS bits',
      bits'.length = bits.length ∧
      (advanceHeadMatch InputAlphabet .before).ReachesExit input bound initTapes inHead
        (if res then HeadMatchState.before else HeadMatchState.atHead)
        (fun j => if j = tScratch then ftS else initTapes j) inHead ∧
      TapeMatches ftS (.leftMark :: bits'.map SimSym.bit ++ [.endMark]) 1 ∧
      (res = true ↔ true ∈ bits) ∧
      (res = true → bitsToNat bits' + 1 = bitsToNat bits) ∧
      (res = false → bits' = bits) := by
  have hBounds : ∀ j, (initTapes j).head < bound j := by
    intro j
    by_cases hj : j = tScratch
    · subst hj; rw [hMatch.head_eq]; omega
    · exact hOtherBounds j hj
  have hAtom :
      (TMComponent.atom fun (_ : InputSymbol InputAlphabet) (scanned : Fin 5 → SimSym) =>
        mkWorkAction (decide (HeadMatchState.before = .before)) scanned (fun _ => .stay)).ReachesExit
        input bound initTapes inHead true initTapes inHead := by
    apply TMComponent.atom_reachesExit _ input bound initTapes inHead hBounds inHead
    · simp [mkWorkAction, moveHead]
    · intro j; exact OneSidedTape.updateAndMove_stay_self (initTapes j)
    · exact hBounds
  obtain ⟨res, ftS, bits', hLen', hDec, hMS', hHasTrue, hDecVal, hEqBits⟩ :=
    decScratch_reachesExit tScratch input bound bits hBound initTapes inHead hOtherBounds hMatch
  have hMap := TMComponent.mapExit_reachesExit (decScratch InputAlphabet tScratch)
    (fun b => if b then HeadMatchState.before else HeadMatchState.atHead) input bound hDec
  have hBranch := TMComponent.branch_reachesExit
    (TMComponent.atom fun _ scanned =>
      mkWorkAction (decide (HeadMatchState.before = .before)) scanned (fun _ => .stay))
    ((decScratch InputAlphabet tScratch).mapExit fun b =>
      if b then HeadMatchState.before else HeadMatchState.atHead)
    (TMComponent.atom fun _ scanned =>
      mkWorkAction HeadMatchState.pastHead scanned (fun _ => .stay))
    input bound true hAtom (by simpa using hMap)
  exact ⟨res, ftS, bits', hLen', hBranch, hMS', hHasTrue, hDecVal, hEqBits⟩

theorem advanceHeadMatch_not_before_reachesExit {InputAlphabet : Type*} {n : ℕ}
    (hms : HeadMatchState) (hNe : hms ≠ .before)
    (input : Fin n → InputAlphabet) (bound : Fin 5 → ℕ)
    (initTapes : Fin 5 → OneSidedTape SimSym) (inHead : Fin (n + 2))
    (hBounds : ∀ j, (initTapes j).head < bound j) :
    (advanceHeadMatch InputAlphabet hms).ReachesExit input bound initTapes inHead
      .pastHead initTapes inHead := by
  have hDecide : decide (hms = .before) = false := decide_eq_false hNe
  have hAtom0 :
      (TMComponent.atom fun (_ : InputSymbol InputAlphabet) (scanned : Fin 5 → SimSym) =>
        mkWorkAction (decide (hms = .before)) scanned (fun _ => .stay)).ReachesExit
        input bound initTapes inHead false initTapes inHead := by
    rw [← hDecide]
    apply TMComponent.atom_reachesExit _ input bound initTapes inHead hBounds inHead
    · simp [mkWorkAction, moveHead]
    · intro j; exact OneSidedTape.updateAndMove_stay_self (initTapes j)
    · exact hBounds
  have hAtom1 :
      (TMComponent.atom fun (_ : InputSymbol InputAlphabet) (scanned : Fin 5 → SimSym) =>
        mkWorkAction HeadMatchState.pastHead scanned (fun _ => .stay)).ReachesExit
        input bound initTapes inHead .pastHead initTapes inHead := by
    apply TMComponent.atom_reachesExit _ input bound initTapes inHead hBounds inHead
    · simp [mkWorkAction, moveHead]
    · intro j; exact OneSidedTape.updateAndMove_stay_self (initTapes j)
    · exact hBounds
  exact TMComponent.branch_reachesExit _ _ _ input bound false hAtom0 (by simpa using hAtom1)

/-- One cell iteration of the work-tape scanner: if `tRuler` is on `.bit true`,
advance `HeadMatchState`, read `gammaBits Γ` bits from `tArgA`/`tArgB`, update
`CellScanState`, and advance `tRuler`; otherwise exit with `st`. -/
noncomputable def scanCellStep (InputAlphabet Γ : Type*) [Fintype Γ] [DecidableEq Γ]
    (st : CellScanState Γ) :=
  TMComponent.branch
    (TMComponent.atom fun _ scanned =>
      mkWorkAction (decide (scanned tRuler = .bit true)) scanned (fun _ => .stay))
    (bindComponent (advanceHeadMatch InputAlphabet st.hms) fun hms' =>
      bindComponent (readFixedBits InputAlphabet (gammaBits Γ) tArgA tArgB) fun res =>
        (stepRightAtom InputAlphabet tRuler).mapExit fun _ =>
          Sum.inl (updateCellScanState st hms' res))
    (TMComponent.atom fun _ scanned =>
      mkWorkAction (Sum.inr st) scanned (fun _ => .stay))

/-- Scan all `S` cells of one work tape using `tRuler` and `tScratch`. -/
noncomputable def scanTapeCells (InputAlphabet Γ : Type*) [Fintype Γ] [DecidableEq Γ]
    (blank : Γ) :=
  loopWithState
    ({ hms := .before, ok := true, scanned := blank, written := blank, valid := true } :
      CellScanState Γ)
    (scanCellStep InputAlphabet Γ)

private theorem bitsToNat_replicate_false (m : ℕ) :
    bitsToNat (List.replicate m false) = 0 := by
  induction m with
  | zero => rfl
  | succ m ih => simp [List.replicate_succ, bitsToNat, ih]

theorem scanTapeCells_reachesExit {InputAlphabet Γ : Type*} {n : ℕ}
    [Fintype Γ] [DecidableEq Γ]
    (input : Fin n → InputAlphabet) (bound : Fin 5 → ℕ)
    (S : ℕ) (blank : Γ) (tapeA tapeB : BoundedTape Γ S)
    (pA sA pB sB : List SimSym)
    (hBoundR : S + 2 ≤ bound tRuler)
    (hBoundA : pA.length + S * gammaBits Γ < bound tArgA)
    (hBoundB : pB.length + S * gammaBits Γ < bound tArgB)
    (hBoundS : S + 2 ≤ bound tScratch)
    (initTapes : Fin 5 → OneSidedTape SimSym) (inHead : Fin (n + 2))
    (hOther : (initTapes tRegs).head < bound tRegs)
    (hMatchR : TapeMatches (initTapes tRuler)
      (.leftMark :: List.replicate S (.bit true) ++ [.endMark]) 1)
    (hMatchA : TapeMatches (initTapes tArgA)
      (pA ++ ((List.finRange S).flatMap (fun c =>
        natToBits (gammaBits Γ) (Fintype.equivFin Γ (tapeA.cells c)).val)).map SimSym.bit ++ sA)
      pA.length)
    (hMatchB : TapeMatches (initTapes tArgB)
      (pB ++ ((List.finRange S).flatMap (fun c =>
        natToBits (gammaBits Γ) (Fintype.equivFin Γ (tapeB.cells c)).val)).map SimSym.bit ++ sB)
      pB.length)
    (hMatchS : TapeMatches (initTapes tScratch)
      (.leftMark :: (natToBits S tapeA.head.val).map SimSym.bit ++ [.endMark]) 1) :
    ∃ st finalTapes,
      (scanTapeCells InputAlphabet Γ blank).ReachesExit input bound initTapes inHead st
        finalTapes inHead ∧
      st.valid = true ∧
      (st.ok = true ↔ ∀ c : Fin S, c ≠ tapeA.head → tapeB.cells c = tapeA.cells c) ∧
      st.scanned = tapeA.cells tapeA.head ∧
      st.written = tapeB.cells tapeA.head ∧
      TapeMatches (finalTapes tRuler)
        (.leftMark :: List.replicate S (.bit true) ++ [.endMark]) (1 + S) ∧
      TapeMatches (finalTapes tArgA)
        (pA ++ ((List.finRange S).flatMap (fun c =>
          natToBits (gammaBits Γ) (Fintype.equivFin Γ (tapeA.cells c)).val)).map SimSym.bit ++ sA)
        (pA.length + S * gammaBits Γ) ∧
      TapeMatches (finalTapes tArgB)
        (pB ++ ((List.finRange S).flatMap (fun c =>
          natToBits (gammaBits Γ) (Fintype.equivFin Γ (tapeB.cells c)).val)).map SimSym.bit ++ sB)
        (pB.length + S * gammaBits Γ) ∧
      TapeMatches (finalTapes tScratch)
        (.leftMark :: (List.replicate S false).map SimSym.bit ++ [.endMark]) 1 ∧
      finalTapes tRegs = initTapes tRegs := by
  let fA : Fin S → List Bool := fun c =>
    natToBits (gammaBits Γ) (Fintype.equivFin Γ (tapeA.cells c)).val
  let fB : Fin S → List Bool := fun c =>
    natToBits (gammaBits Γ) (Fintype.equivFin Γ (tapeB.cells c)).val
  let rulerList := SimSym.leftMark :: List.replicate S (SimSym.bit true) ++ [SimSym.endMark]
  let fullA := pA ++ ((List.finRange S).flatMap fA).map SimSym.bit ++ sA
  let fullB := pB ++ ((List.finRange S).flatMap fB).map SimSym.bit ++ sB
  have hTakeLen : ∀ (f : Fin S → List Bool), (∀ c, (f c).length = gammaBits Γ) →
      ∀ i : ℕ, i ≤ S → (((List.finRange S).take i).flatMap f).length = i * gammaBits Γ := by
    intro f hf i hi
    rw [List.length_flatMap, List.map_congr_left (fun c _ => hf c), List.map_const',
      List.sum_replicate, List.length_take, List.length_finRange, Nat.min_eq_left hi, smul_eq_mul]
  have hFA_len : ∀ c, (fA c).length = gammaBits Γ := fun c => natToBits_length _ _
  have hFB_len : ∀ c, (fB c).length = gammaBits Γ := fun c => natToBits_length _ _
  have hSplitRange : ∀ i (hi : i < S),
      List.finRange S = (List.finRange S).take i ++ ⟨i, hi⟩ :: (List.finRange S).drop (i + 1) := by
    intro i hi
    have h1 := (List.take_append_drop i (List.finRange S)).symm
    have h2 : (List.finRange S).drop i =
        (List.finRange S)[i]'(by simp [hi]) :: (List.finRange S).drop (i + 1) :=
      List.drop_eq_getElem_cons (by simp [hi])
    simpa [h2, List.getElem_finRange] using h1
  let Inv : CellScanState Γ → (Fin 5 → OneSidedTape SimSym) → Fin (n + 2) → Prop :=
    fun st tapes curInHead =>
      ∃ i : ℕ, i ≤ S ∧
        curInHead = inHead ∧
        st.valid = true ∧
        (st.ok = true ↔ ∀ c : Fin S, c.val < i → c ≠ tapeA.head → tapeB.cells c = tapeA.cells c) ∧
        (i ≤ tapeA.head.val →
          st.hms = .before ∧
          TapeMatches (tapes tScratch)
            (.leftMark :: (natToBits S (tapeA.head.val - i)).map SimSym.bit ++ [.endMark]) 1) ∧
        (i = tapeA.head.val + 1 →
          st.hms = .atHead ∧
          st.scanned = tapeA.cells tapeA.head ∧
          st.written = tapeB.cells tapeA.head ∧
          TapeMatches (tapes tScratch)
            (.leftMark :: (List.replicate S false).map SimSym.bit ++ [.endMark]) 1) ∧
        (tapeA.head.val + 1 < i →
          st.hms = .pastHead ∧
          st.scanned = tapeA.cells tapeA.head ∧
          st.written = tapeB.cells tapeA.head ∧
          TapeMatches (tapes tScratch)
            (.leftMark :: (List.replicate S false).map SimSym.bit ++ [.endMark]) 1) ∧
        TapeMatches (tapes tRuler) rulerList (1 + i) ∧
        TapeMatches (tapes tArgA) fullA (pA.length + i * gammaBits Γ) ∧
        TapeMatches (tapes tArgB) fullB (pB.length + i * gammaBits Γ) ∧
        tapes tRegs = initTapes tRegs
  let measure : CellScanState Γ → (Fin 5 → OneSidedTape SimSym) → Fin (n + 2) → ℕ :=
    fun _ tapes _ => (1 + S) - (tapes tRuler).head
  let Post : CellScanState Γ → (Fin 5 → OneSidedTape SimSym) → Fin (n + 2) → Prop :=
    fun st tapes curInHead =>
      curInHead = inHead ∧
      st.valid = true ∧
      (st.ok = true ↔ ∀ c : Fin S, c ≠ tapeA.head → tapeB.cells c = tapeA.cells c) ∧
      st.scanned = tapeA.cells tapeA.head ∧
      st.written = tapeB.cells tapeA.head ∧
      TapeMatches (tapes tRuler) rulerList (1 + S) ∧
      TapeMatches (tapes tArgA) fullA (pA.length + S * gammaBits Γ) ∧
      TapeMatches (tapes tArgB) fullB (pB.length + S * gammaBits Γ) ∧
      TapeMatches (tapes tScratch)
        (.leftMark :: (List.replicate S false).map SimSym.bit ++ [.endMark]) 1 ∧
      tapes tRegs = initTapes tRegs
  have hStep : ∀ st tapes curInHead, Inv st tapes curInHead →
      (∃ st' tapes' curInHead',
        (scanCellStep InputAlphabet Γ st).ReachesExit input bound tapes curInHead
          (.inl st') tapes' curInHead' ∧
        Inv st' tapes' curInHead' ∧
        measure st' tapes' curInHead' < measure st tapes curInHead) ∨
      (∃ e tapes' curInHead',
        (scanCellStep InputAlphabet Γ st).ReachesExit input bound tapes curInHead
          (.inr e) tapes' curInHead' ∧
        Post e tapes' curInHead') := by
    intro st tapes curInHead hInv
    rcases hInv with ⟨i, hiLe, hCurIn, hValid, hOkIff, hBef, hAt, hPast, hMR, hMA, hMB, hReg⟩
    cases hCurIn
    have hScratchBounds : (tapes tScratch).head < bound tScratch := by
      by_cases hi1 : i ≤ tapeA.head.val
      · rw [(hBef hi1).2.head_eq]; omega
      · by_cases hi2 : i = tapeA.head.val + 1
        · rw [(hAt hi2).2.2.2.head_eq]; omega
        · rw [(hPast (by omega)).2.2.2.head_eq]; omega
    have hBounds : ∀ j, (tapes j).head < bound j := by
      intro j
      match j with
      | ⟨0, _⟩ => change (tapes tRuler).head < bound tRuler; rw [hMR.head_eq]; omega
      | ⟨1, _⟩ => change (tapes tRegs).head < bound tRegs; rw [hReg]; exact hOther
      | ⟨2, _⟩ =>
        change (tapes tArgA).head < bound tArgA
        rw [hMA.head_eq]
        have : i * gammaBits Γ ≤ S * gammaBits Γ := Nat.mul_le_mul_right _ hiLe
        omega
      | ⟨3, _⟩ =>
        change (tapes tArgB).head < bound tArgB
        rw [hMB.head_eq]
        have : i * gammaBits Γ ≤ S * gammaBits Γ := Nat.mul_le_mul_right _ hiLe
        omega
      | ⟨4, _⟩ => exact hScratchBounds
    have hRLen : rulerList.length = S + 2 := by simp [rulerList]
    by_cases hiLt : i < S
    · left
      have hReadR : (tapes tRuler).cells (tapes tRuler).head = .bit true := by
        rw [hMR.read_lt (by rw [hRLen]; omega)]
        simp only [rulerList, Nat.add_comm 1 i]
        rw [List.getElem_append_left (by simp; omega), List.getElem_cons_succ]
        simp
      have hDecR : decide ((tapes tRuler).cells (tapes tRuler).head = .bit true) = true := by
        rw [hReadR]; decide
      have hAtomBranch :
          (TMComponent.atom fun (_ : InputSymbol InputAlphabet) (scanned : Fin 5 → SimSym) =>
            mkWorkAction (decide (scanned tRuler = .bit true)) scanned (fun _ => .stay)).ReachesExit
            input bound tapes inHead true tapes inHead := by
        have hTmp :
            (TMComponent.atom fun (_ : InputSymbol InputAlphabet) (scanned : Fin 5 → SimSym) =>
              mkWorkAction (decide (scanned tRuler = .bit true)) scanned (fun _ => .stay)).ReachesExit
              input bound tapes inHead
              (decide ((tapes tRuler).cells (tapes tRuler).head = .bit true)) tapes inHead := by
          apply TMComponent.atom_reachesExit _ input bound tapes inHead hBounds inHead
          · simp [mkWorkAction, moveHead]
          · intro j; exact OneSidedTape.updateAndMove_stay_self (tapes j)
          · exact hBounds
        rwa [hDecR] at hTmp
      -- Step 1: advanceHeadMatch
      have hAdv : ∃ hms' t1,
          (advanceHeadMatch InputAlphabet st.hms).ReachesExit input bound tapes inHead hms' t1 inHead ∧
          (i < tapeA.head.val → hms' = .before ∧
            TapeMatches (t1 tScratch)
              (.leftMark :: (natToBits S (tapeA.head.val - (i + 1))).map SimSym.bit ++ [.endMark]) 1) ∧
          (i = tapeA.head.val → hms' = .atHead ∧
            TapeMatches (t1 tScratch)
              (.leftMark :: (List.replicate S false).map SimSym.bit ++ [.endMark]) 1) ∧
          (tapeA.head.val < i → hms' = .pastHead ∧
            TapeMatches (t1 tScratch)
              (.leftMark :: (List.replicate S false).map SimSym.bit ++ [.endMark]) 1) ∧
          (∀ j, j ≠ tScratch → t1 j = tapes j) := by
        by_cases hiHead : i ≤ tapeA.head.val
        · obtain ⟨hHms, hMS⟩ := hBef hiHead
          rw [hHms]
          obtain ⟨res, ftS, bits', hLen', hAdvRun, hMS', hHasTrue, hDecVal, hEqBits⟩ :=
            advanceHeadMatch_before_reachesExit input bound (natToBits S (tapeA.head.val - i))
              (by rw [natToBits_length]; exact hBoundS) tapes inHead
              (fun j hj => hBounds j) hMS
          refine ⟨if res then .before else .atHead, fun j => if j = tScratch then ftS else tapes j,
            hAdvRun, ?_, ?_, ?_, fun j hj => by simp [hj]⟩
          · intro hiLtH
            have hSubPos : 0 < tapeA.head.val - i := by omega
            have hSubLt : tapeA.head.val - i < 2 ^ S := by
              have := tapeA.head.isLt
              have := Nat.lt_two_pow_self (n := S)
              omega
            have hPosNat : 0 < bitsToNat (natToBits S (tapeA.head.val - i)) := by
              rw [bitsToNat_natToBits_of_lt hSubLt]; exact hSubPos
            have hResT : res = true := hHasTrue.mpr ((true_mem_iff_bitsToNat_pos _).mpr hPosNat)
            have hVal1 : bitsToNat bits' = tapeA.head.val - (i + 1) := by
              have := hDecVal hResT
              rw [bitsToNat_natToBits_of_lt hSubLt] at this
              omega
            have hBitsEq : bits' = natToBits S (tapeA.head.val - (i + 1)) := by
              have hId := natToBits_bitsToNat bits'
              rw [hLen', natToBits_length, hVal1] at hId
              exact hId.symm
            simp only [hResT, ↓reduceIte]
            exact ⟨trivial, by simpa [hBitsEq] using hMS'⟩
          · intro hiEqH
            have hSubZero : tapeA.head.val - i = 0 := by omega
            have hNoTrue : true ∉ natToBits S (tapeA.head.val - i) := by
              rw [true_mem_iff_bitsToNat_pos, hSubZero, natToBits_zero,
                bitsToNat_replicate_false]
              omega
            have hResF : res = false := by
              cases hR : res
              · rfl
              · exact False.elim (hNoTrue (hHasTrue.mp hR))
            have hBitsEq : bits' = List.replicate S false := by
              rw [hEqBits hResF, hSubZero, natToBits_zero]
            simp only [hResF, Bool.false_eq_true, ↓reduceIte]
            exact ⟨trivial, by simpa [hBitsEq] using hMS'⟩
          · intro hGt; omega
        · have hHmsNe : st.hms ≠ .before := by
            by_cases hiEq1 : i = tapeA.head.val + 1
            · rw [(hAt hiEq1).1]; decide
            · rw [(hPast (by omega)).1]; decide
          have hAdvRun := advanceHeadMatch_not_before_reachesExit st.hms hHmsNe input bound
            tapes inHead hBounds
          refine ⟨.pastHead, tapes, hAdvRun, fun h => by omega, fun h => by omega, ?_, fun _ _ => rfl⟩
          intro _
          refine ⟨rfl, ?_⟩
          by_cases hiEq1 : i = tapeA.head.val + 1
          · exact (hAt hiEq1).2.2.2
          · exact (hPast (by omega)).2.2.2
      rcases hAdv with ⟨hms', t1, hAdvRun, hAdvBef, hAdvAt, hAdvPast, hT1Others⟩
      have hT1ScratchBound : (t1 tScratch).head < bound tScratch := by
        by_cases h1 : i < tapeA.head.val
        · rw [(hAdvBef h1).2.head_eq]; omega
        · by_cases h2 : i = tapeA.head.val
          · rw [(hAdvAt h2).2.head_eq]; omega
          · rw [(hAdvPast (by omega)).2.head_eq]; omega
      have hT1Bounds : ∀ j, (t1 j).head < bound j := by
        intro j
        by_cases hj : j = tScratch
        · subst hj; exact hT1ScratchBound
        · rw [hT1Others j hj]; exact hBounds j
      -- Step 2: readFixedBits
      let cIdx : Fin S := ⟨i, hiLt⟩
      let sliceA := fA cIdx
      let sliceB := fB cIdx
      let prefA' := pA ++ (((List.finRange S).take i).flatMap fA).map SimSym.bit
      let sufA' := (((List.finRange S).drop (i + 1)).flatMap fA).map SimSym.bit ++ sA
      let prefB' := pB ++ (((List.finRange S).take i).flatMap fB).map SimSym.bit
      let sufB' := (((List.finRange S).drop (i + 1)).flatMap fB).map SimSym.bit ++ sB
      have hFullAEq : fullA = prefA' ++ sliceA.map SimSym.bit ++ sufA' := by
        simp only [fullA, prefA', sufA', sliceA]
        conv_lhs => rw [hSplitRange i hiLt]
        rw [List.flatMap_append, List.flatMap_cons, List.map_append, List.map_append]
        simp only [List.append_assoc]
        rfl
      have hFullBEq : fullB = prefB' ++ sliceB.map SimSym.bit ++ sufB' := by
        simp only [fullB, prefB', sufB', sliceB]
        conv_lhs => rw [hSplitRange i hiLt]
        rw [List.flatMap_append, List.flatMap_cons, List.map_append, List.map_append]
        simp only [List.append_assoc]
        rfl
      have hPrefALen : prefA'.length = pA.length + i * gammaBits Γ := by
        simp [prefA', hTakeLen fA hFA_len i hiLe]
      have hPrefBLen : prefB'.length = pB.length + i * gammaBits Γ := by
        simp [prefB', hTakeLen fB hFB_len i hiLe]
      have hNeAB : tArgA ≠ tArgB := by decide
      have hMA1 : TapeMatches (t1 tArgA) (prefA' ++ sliceA.map SimSym.bit ++ sufA') prefA'.length := by
        rw [← hFullAEq, hPrefALen, hT1Others tArgA (by decide)]
        exact hMA
      have hMB1 : TapeMatches (t1 tArgB) (prefB' ++ sliceB.map SimSym.bit ++ sufB') prefB'.length := by
        rw [← hFullBEq, hPrefBLen, hT1Others tArgB (by decide)]
        exact hMB
      have hBoundA' : prefA'.length + gammaBits Γ < bound tArgA := by
        rw [hPrefALen]
        have : (i + 1) * gammaBits Γ ≤ S * gammaBits Γ :=
          Nat.mul_le_mul_right _ (by omega)
        rw [Nat.add_mul, Nat.one_mul] at this
        omega
      have hBoundB' : prefB'.length + gammaBits Γ < bound tArgB := by
        rw [hPrefBLen]
        have : (i + 1) * gammaBits Γ ≤ S * gammaBits Γ :=
          Nat.mul_le_mul_right _ (by omega)
        rw [Nat.add_mul, Nat.one_mul] at this
        omega
      obtain ⟨ftA, ftB, hReadBits, hFA2, hFB2, _, _⟩ :=
        readFixedBits_reachesExit (gammaBits Γ) tArgA tArgB hNeAB input bound
          prefA' sufA' prefB' sufB' sliceA sliceB (hFA_len cIdx) (hFB_len cIdx)
          hBoundA' hBoundB' t1 inHead (fun j hj1 hj2 => hT1Bounds j) hMA1 hMB1
      let t2 := fun j => if j = tArgA then ftA else if j = tArgB then ftB else t1 j
      have hT2Bounds : ∀ j, j ≠ tRuler → (t2 j).head < bound j := by
        intro j hjR
        match j with
        | ⟨0, _⟩ => exact False.elim (hjR rfl)
        | ⟨1, _⟩ => change (t1 tRegs).head < bound tRegs; exact hT1Bounds tRegs
        | ⟨2, _⟩ => change ftA.head < bound tArgA; rw [hFA2.head_eq]; exact hBoundA'
        | ⟨3, _⟩ => change ftB.head < bound tArgB; rw [hFB2.head_eq]; exact hBoundB'
        | ⟨4, _⟩ => change (t1 tScratch).head < bound tScratch; exact hT1Bounds tScratch
      have hMR2 : TapeMatches (t2 tRuler) rulerList (1 + i) := by
        change TapeMatches (t1 tRuler) rulerList (1 + i)
        rw [hT1Others tRuler (by decide)]
        exact hMR
      -- Step 3: stepRightAtom tRuler
      obtain ⟨ftR, hStepR, hFR3⟩ :=
        stepRightAtom_reachesExit tRuler input bound rulerList (1 + i)
          (by omega) t2 inHead hT2Bounds hMR2
      let t3 := fun j => if j = tRuler then ftR else t2 j
      let rFnA : Fin (gammaBits Γ) → Bool := fun j =>
        sliceA[j.val]'(by rw [hFA_len cIdx]; exact j.isLt)
      let rFnB : Fin (gammaBits Γ) → Bool := fun j =>
        sliceB[j.val]'(by rw [hFB_len cIdx]; exact j.isLt)
      let st' := updateCellScanState st hms' (some (rFnA, rFnB))
      have hPowG : Fintype.card Γ + 1 ≤ 2 ^ gammaBits Γ :=
        Nat.le_pow_clog (by decide : 1 < 2) (Fintype.card Γ + 1)
      have hDecA : decodeBitsOpt (gammaBits Γ) Γ rFnA = some (tapeA.cells cIdx) := by
        apply (decodeBitsOpt_eq_some_iff hPowG rFnA (tapeA.cells cIdx)).mpr
        exact (List.ext_getElem (by simp [natToBits_length])
          (fun j h1 _ => by simp [rFnA, sliceA, fA])).symm
      have hDecB : decodeBitsOpt (gammaBits Γ) Γ rFnB = some (tapeB.cells cIdx) := by
        apply (decodeBitsOpt_eq_some_iff hPowG rFnB (tapeB.cells cIdx)).mpr
        exact (List.ext_getElem (by simp [natToBits_length])
          (fun j h1 _ => by simp [rFnB, sliceB, fB])).symm
      have hMapStepR := TMComponent.mapExit_reachesExit (stepRightAtom InputAlphabet tRuler)
        (fun _ => (Sum.inl st' : CellScanState Γ ⊕ CellScanState Γ)) input bound hStepR
      have hBindRead := bindComponent_reachesExit
        (readFixedBits InputAlphabet (gammaBits Γ) tArgA tArgB)
        (fun res => (stepRightAtom InputAlphabet tRuler).mapExit fun _ =>
          Sum.inl (updateCellScanState st hms' res))
        input bound hReadBits (by simpa [st'] using hMapStepR)
      have hBindAdv := bindComponent_reachesExit (advanceHeadMatch InputAlphabet st.hms)
        (fun hms' => bindComponent (readFixedBits InputAlphabet (gammaBits Γ) tArgA tArgB) fun res =>
          (stepRightAtom InputAlphabet tRuler).mapExit fun _ =>
            Sum.inl (updateCellScanState st hms' res))
        input bound hAdvRun hBindRead
      have hBranch := TMComponent.branch_reachesExit
        (TMComponent.atom fun _ scanned =>
          mkWorkAction (decide (scanned tRuler = .bit true)) scanned (fun _ => .stay))
        (bindComponent (advanceHeadMatch InputAlphabet st.hms) fun hms' =>
          bindComponent (readFixedBits InputAlphabet (gammaBits Γ) tArgA tArgB) fun res =>
            (stepRightAtom InputAlphabet tRuler).mapExit fun _ =>
              Sum.inl (updateCellScanState st hms' res))
        (TMComponent.atom fun _ scanned =>
          mkWorkAction (Sum.inr st) scanned (fun _ => .stay))
        input bound true hAtomBranch (by simpa using hBindAdv)
      refine ⟨st', t3, inHead, hBranch, ⟨i + 1, by omega, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
      · -- st'.valid = true
        cases hms' <;> simp [st', updateCellScanState, hDecA, hDecB, hValid]
      · -- st'.ok = true ↔ ...
        by_cases hEqHead : i = tapeA.head.val
        · have hAtH := (hAdvAt hEqHead).1
          simp only [st', updateCellScanState, hDecA, hDecB, hAtH, hOkIff]
          constructor
          · intro h c hc hcNe
            by_cases hci : c.val < i
            · exact h c hci hcNe
            · have hcEq : c = tapeA.head := Fin.ext (by omega)
              exact False.elim (hcNe hcEq)
          · intro h c hc hcNe
            exact h c (by omega) hcNe
        · have hNotAt : hms' = .before ∨ hms' = .pastHead := by
            by_cases hLtH : i < tapeA.head.val
            · exact Or.inl (hAdvBef hLtH).1
            · exact Or.inr (hAdvPast (by omega)).1
          have hUpdOk : st'.ok = (st.ok && decide (tapeA.cells cIdx = tapeB.cells cIdx)) := by
            rcases hNotAt with hB | hP
            · simp [st', updateCellScanState, hDecA, hDecB, hB]
            · simp [st', updateCellScanState, hDecA, hDecB, hP]
          rw [hUpdOk, Bool.and_eq_true, decide_eq_true_eq, hOkIff]
          constructor
          · rintro ⟨hPrev, hCur⟩ c hc hcNe
            by_cases hci : c.val < i
            · exact hPrev c hci hcNe
            · have hcEq : c = cIdx := Fin.ext (by simp [cIdx]; omega)
              subst hcEq; exact hCur.symm
          · intro h
            refine ⟨fun c hc hcNe => h c (by omega) hcNe, ?_⟩
            have hcNe : cIdx ≠ tapeA.head := fun heq => hEqHead (congrArg Fin.val heq)
            exact (h cIdx (by simp [cIdx]) hcNe).symm
      · -- i + 1 ≤ tapeA.head.val
        intro hi1
        have hLtH : i < tapeA.head.val := by omega
        obtain ⟨h1, h2⟩ := hAdvBef hLtH
        refine ⟨?_, ?_⟩
        · simp [st', updateCellScanState, hDecA, hDecB, h1]
        · simpa [t3, t2, tRuler, tArgA, tArgB, tScratch] using h2
      · -- i + 1 = tapeA.head.val + 1
        intro hi1
        have hEqH : i = tapeA.head.val := by omega
        obtain ⟨h1, h2⟩ := hAdvAt hEqH
        have hcEq : cIdx = tapeA.head := Fin.ext hEqH
        refine ⟨?_, ?_, ?_, ?_⟩
        · simp [st', updateCellScanState, hDecA, hDecB, h1]
        · simp [st', updateCellScanState, hDecA, hDecB, h1, hcEq]
        · simp [st', updateCellScanState, hDecA, hDecB, h1, hcEq]
        · simpa [t3, t2, tRuler, tArgA, tArgB, tScratch] using h2
      · -- tapeA.head.val + 1 < i + 1
        intro hi1
        have hGtH : tapeA.head.val < i := by omega
        have hScanEq : st.scanned = tapeA.cells tapeA.head := by
          by_cases h1 : i = tapeA.head.val + 1
          · exact (hAt h1).2.1
          · exact (hPast (by omega)).2.1
        have hWritEq : st.written = tapeB.cells tapeA.head := by
          by_cases h1 : i = tapeA.head.val + 1
          · exact (hAt h1).2.2.1
          · exact (hPast (by omega)).2.2.1
        obtain ⟨h1, h2⟩ := hAdvPast hGtH
        refine ⟨?_, ?_, ?_, ?_⟩
        · simp [st', updateCellScanState, hDecA, hDecB, h1]
        · simp [st', updateCellScanState, hDecA, hDecB, h1, hScanEq]
        · simp [st', updateCellScanState, hDecA, hDecB, h1, hWritEq]
        · simpa [t3, t2, tRuler, tArgA, tArgB, tScratch] using h2
      · -- TapeMatches tRuler
        simpa [t3, Nat.add_assoc] using hFR3
      · -- TapeMatches tArgA
        have hHeadEq : pA.length + (i + 1) * gammaBits Γ = prefA'.length + gammaBits Γ := by
          rw [hPrefALen, Nat.add_mul, Nat.one_mul, Nat.add_assoc]
        rw [hHeadEq, hFullAEq]
        simpa [t3, t2, tRuler, tArgA, tArgB, tScratch] using hFA2
      · -- TapeMatches tArgB
        have hHeadEq : pB.length + (i + 1) * gammaBits Γ = prefB'.length + gammaBits Γ := by
          rw [hPrefBLen, Nat.add_mul, Nat.one_mul, Nat.add_assoc]
        rw [hHeadEq, hFullBEq]
        simpa [t3, t2, tRuler, tArgA, tArgB, tScratch] using hFB2
      · -- tRegs unchanged
        change t1 tRegs = initTapes tRegs
        rw [hT1Others tRegs (by decide), hReg]
      · -- measure decreases
        change 1 + S - ftR.head < 1 + S - (tapes tRuler).head
        rw [hFR3.head_eq, hMR.head_eq]
        omega
    · -- i = S: ruler is at endMark, exit loop
      right
      have hiS : i = S := by omega
      have hReadR : (tapes tRuler).cells (tapes tRuler).head = .endMark := by
        rw [hMR.read_lt (by rw [hRLen]; omega)]
        simp only [rulerList, Nat.add_comm 1 i]
        rw [List.getElem_append_right (by simp [hiS])]
        simp [hiS]
      have hDecR : decide ((tapes tRuler).cells (tapes tRuler).head = .bit true) = false := by
        rw [hReadR]; decide
      have hAtomBranch :
          (TMComponent.atom fun (_ : InputSymbol InputAlphabet) (scanned : Fin 5 → SimSym) =>
            mkWorkAction (decide (scanned tRuler = .bit true)) scanned (fun _ => .stay)).ReachesExit
            input bound tapes inHead false tapes inHead := by
        have hTmp :
            (TMComponent.atom fun (_ : InputSymbol InputAlphabet) (scanned : Fin 5 → SimSym) =>
              mkWorkAction (decide (scanned tRuler = .bit true)) scanned (fun _ => .stay)).ReachesExit
              input bound tapes inHead
              (decide ((tapes tRuler).cells (tapes tRuler).head = .bit true)) tapes inHead := by
          apply TMComponent.atom_reachesExit _ input bound tapes inHead hBounds inHead
          · simp [mkWorkAction, moveHead]
          · intro j; exact OneSidedTape.updateAndMove_stay_self (tapes j)
          · exact hBounds
        rwa [hDecR] at hTmp
      have hAtomExit :
          (TMComponent.atom fun (_ : InputSymbol InputAlphabet) (scanned : Fin 5 → SimSym) =>
            mkWorkAction (Sum.inr st : CellScanState Γ ⊕ CellScanState Γ) scanned
              (fun _ => .stay)).ReachesExit
            input bound tapes inHead (.inr st) tapes inHead := by
        apply TMComponent.atom_reachesExit _ input bound tapes inHead hBounds inHead
        · simp [mkWorkAction, moveHead]
        · intro j; exact OneSidedTape.updateAndMove_stay_self (tapes j)
        · exact hBounds
      have hBranch := TMComponent.branch_reachesExit
        (TMComponent.atom fun _ scanned =>
          mkWorkAction (decide (scanned tRuler = .bit true)) scanned (fun _ => .stay))
        (bindComponent (advanceHeadMatch InputAlphabet st.hms) fun hms' =>
          bindComponent (readFixedBits InputAlphabet (gammaBits Γ) tArgA tArgB) fun res =>
            (stepRightAtom InputAlphabet tRuler).mapExit fun _ =>
              Sum.inl (updateCellScanState st hms' res))
        (TMComponent.atom fun _ scanned =>
          mkWorkAction (Sum.inr st) scanned (fun _ => .stay))
        input bound false hAtomBranch (by simpa using hAtomExit)
      have hMid : (S = tapeA.head.val + 1 →
            st.scanned = tapeA.cells tapeA.head ∧
            st.written = tapeB.cells tapeA.head ∧
            TapeMatches (tapes tScratch)
              (.leftMark :: (List.replicate S false).map SimSym.bit ++ [.endMark]) 1) ∧
          (tapeA.head.val + 1 < S →
            st.scanned = tapeA.cells tapeA.head ∧
            st.written = tapeB.cells tapeA.head ∧
            TapeMatches (tapes tScratch)
              (.leftMark :: (List.replicate S false).map SimSym.bit ++ [.endMark]) 1) :=
        ⟨fun h => ⟨(hAt (hiS ▸ h)).2.1, (hAt (hiS ▸ h)).2.2.1, (hAt (hiS ▸ h)).2.2.2⟩,
         fun h => ⟨(hPast (hiS ▸ h)).2.1, (hPast (hiS ▸ h)).2.2.1, (hPast (hiS ▸ h)).2.2.2⟩⟩
      have hScanned : st.scanned = tapeA.cells tapeA.head := by
        by_cases h1 : S = tapeA.head.val + 1
        · exact (hMid.1 h1).1
        · exact (hMid.2 (by have := tapeA.head.isLt; omega)).1
      have hWritten : st.written = tapeB.cells tapeA.head := by
        by_cases h1 : S = tapeA.head.val + 1
        · exact (hMid.1 h1).2.1
        · exact (hMid.2 (by have := tapeA.head.isLt; omega)).2.1
      have hScratchF : TapeMatches (tapes tScratch)
          (.leftMark :: (List.replicate S false).map SimSym.bit ++ [.endMark]) 1 := by
        by_cases h1 : S = tapeA.head.val + 1
        · exact (hMid.1 h1).2.2
        · exact (hMid.2 (by have := tapeA.head.isLt; omega)).2.2
      refine ⟨st, tapes, inHead, hBranch, rfl, hValid, ?_, hScanned, hWritten,
        by simpa [hiS] using hMR, by simpa [hiS] using hMA, by simpa [hiS] using hMB,
        hScratchF, hReg⟩
      rw [hOkIff]
      constructor
      · intro h c hcNe; exact h c (hiS ▸ c.isLt) hcNe
      · intro h c _ hcNe; exact h c hcNe
  have hInitInv : Inv
      ({ hms := .before, ok := true, scanned := blank, written := blank, valid := true })
      initTapes inHead := by
    refine ⟨0, Nat.zero_le S, rfl, rfl, ?_, ?_, ?_, ?_, hMatchR, ?_, ?_, rfl⟩
    · simp
    · intro _; exact ⟨rfl, by simpa using hMatchS⟩
    · intro h; omega
    · intro h; omega
    · simpa [fullA, List.append_assoc] using hMatchA
    · simpa [fullB, List.append_assoc] using hMatchB
  obtain ⟨st, finalTapes, finalInHead, hRun, hHead, hValid, hOk, hScan, hWrit, hFR, hFA, hFB,
      hFS, hReg⟩ :=
    loopWithState_reachesExit
      ({ hms := .before, ok := true, scanned := blank, written := blank, valid := true })
      (scanCellStep InputAlphabet Γ) input bound Inv measure Post hStep initTapes inHead hInitInv
  subst finalInHead
  exact ⟨st, finalTapes, hRun, hValid, hOk, hScan, hWrit, hFR, hFA, hFB, hFS, hReg⟩


end SavitchLemma

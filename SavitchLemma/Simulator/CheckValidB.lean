module

public import SavitchLemma.Simulator.ConfigValidity

@[expose] public section

/-!
# Head-range and suffix-marker validator for `tArgB`

Checks that a `configBitWidth Q Γ k S`-bit list on `tArgB` has every work-tape
head `< S` and ends with `[true, false]`.
-/

namespace SavitchLemma

/-! ## 1. Copy `S` bits from `tArgB` to `tScratch` and test `< S` -/

/-- Copy `S` bits from `tArgB` onto `tScratch` (followed by `.endMark`) using
`tRuler`, advancing `tArgB` by `S`, then rewind `tRuler` and `tScratch` to `1`. -/
def copySFromBToScratch (InputAlphabet : Type*) :=
  (loopWithState () fun _ =>
    TMComponent.atom fun _ scanned =>
      match scanned tRuler with
      | .bit true =>
        let b := simBitVal (scanned tArgB)
        mkWorkAction (.inl ())
          (fun j => if j = tScratch then .bit b else scanned j)
          (fun j => if j = tRuler ∨ j = tArgB ∨ j = tScratch then .right else .stay)
      | _ =>
        mkWorkAction (.inr ())
          (fun j => if j = tScratch then .endMark else scanned j)
          (fun _ => .stay)).seq
    ((rewindTape InputAlphabet tRuler).seq (rewindTape InputAlphabet tScratch))

theorem copySFromBToScratch_reachesExit {InputAlphabet : Type*} {n : ℕ}
    (input : Fin n → InputAlphabet) (bound : Fin 5 → ℕ)
    (S : ℕ) (pB sB : List SimSym) (bits : List Bool)
    (hLen : bits.length = S)
    (hBoundR : S + 2 ≤ bound tRuler)
    (hBoundB : pB.length + S < bound tArgB)
    (hBoundS : S + 2 ≤ bound tScratch)
    (initTapes : Fin 5 → OneSidedTape SimSym) (inHead : Fin (n + 2))
    (hOtherBounds : ∀ j, j ≠ tRuler → j ≠ tArgB → j ≠ tScratch → (initTapes j).head < bound j)
    (hMatchR : TapeMatches (initTapes tRuler)
      (.leftMark :: List.replicate S (.bit true) ++ [.endMark]) 1)
    (hMatchB : TapeMatches (initTapes tArgB) (pB ++ bits.map SimSym.bit ++ sB) pB.length)
    (hMatchS : TapeMatches (initTapes tScratch) [.leftMark] 1) :
    ∃ ftR ftB ftS,
      (copySFromBToScratch InputAlphabet).ReachesExit input bound initTapes inHead ()
        (fun j => if j = tRuler then ftR else if j = tArgB then ftB
                  else if j = tScratch then ftS else initTapes j) inHead ∧
      TapeMatches ftR (.leftMark :: List.replicate S (.bit true) ++ [.endMark]) 1 ∧
      TapeMatches ftB (pB ++ bits.map SimSym.bit ++ sB) (pB.length + S) ∧
      TapeMatches ftS (.leftMark :: bits.map SimSym.bit ++ [.endMark]) 1 := by
  let rulerList := SimSym.leftMark :: List.replicate S (SimSym.bit true) ++ [SimSym.endMark]
  let scratchList := SimSym.leftMark :: bits.map SimSym.bit ++ [SimSym.endMark]
  let fullB := pB ++ bits.map SimSym.bit ++ sB
  have hRLen : rulerList.length = S + 2 := by simp [rulerList]
  have hSLen : scratchList.length = S + 2 := by simp [scratchList, hLen]
  let body : Unit → TMComponent Unit InputAlphabet SimSym 5 (Unit ⊕ Unit) := fun _ =>
    TMComponent.atom fun (_ : InputSymbol InputAlphabet) (scanned : Fin 5 → SimSym) =>
      match scanned tRuler with
      | .bit true =>
        let b := simBitVal (scanned tArgB)
        mkWorkAction (.inl ())
          (fun j => if j = tScratch then .bit b else scanned j)
          (fun j => if j = tRuler ∨ j = tArgB ∨ j = tScratch then .right else .stay)
      | _ =>
        mkWorkAction (.inr ())
          (fun j => if j = tScratch then .endMark else scanned j)
          (fun _ => .stay)
  let Inv : Unit → (Fin 5 → OneSidedTape SimSym) → Fin (n + 2) → Prop :=
    fun _ tapes curInHead =>
      ∃ i : ℕ, i ≤ S ∧
        curInHead = inHead ∧
        TapeMatches (tapes tRuler) rulerList (1 + i) ∧
        TapeMatches (tapes tArgB) fullB (pB.length + i) ∧
        TapeMatches (tapes tScratch) (.leftMark :: (bits.take i).map SimSym.bit) (1 + i) ∧
        (∀ j, j ≠ tRuler → j ≠ tArgB → j ≠ tScratch → tapes j = initTapes j)
  let measure : Unit → (Fin 5 → OneSidedTape SimSym) → Fin (n + 2) → ℕ :=
    fun _ tapes _ => (1 + S) - (tapes tRuler).head
  let Post : Unit → (Fin 5 → OneSidedTape SimSym) → Fin (n + 2) → Prop :=
    fun _ tapes curInHead =>
      curInHead = inHead ∧
      TapeMatches (tapes tRuler) rulerList (1 + S) ∧
      TapeMatches (tapes tArgB) fullB (pB.length + S) ∧
      TapeMatches (tapes tScratch) scratchList (1 + S) ∧
      (∀ j, j ≠ tRuler → j ≠ tArgB → j ≠ tScratch → tapes j = initTapes j)
  have hStep : ∀ st tapes curInHead, Inv st tapes curInHead →
      (∃ st' tapes' curInHead',
        (body st).ReachesExit input bound tapes curInHead (.inl st') tapes' curInHead' ∧
        Inv st' tapes' curInHead' ∧
        measure st' tapes' curInHead' < measure st tapes curInHead) ∨
      (∃ e tapes' curInHead',
        (body st).ReachesExit input bound tapes curInHead (.inr e) tapes' curInHead' ∧
        Post e tapes' curInHead') := by
    rintro ⟨⟩ tapes curInHead ⟨i, hiLe, hCurIn, hMR, hMB, hMS, hOthers⟩
    cases hCurIn
    have hBounds : ∀ j, (tapes j).head < bound j := by
      intro j
      by_cases hjR : j = tRuler
      · subst hjR; rw [hMR.head_eq]; omega
      · by_cases hjB : j = tArgB
        · subst hjB; rw [hMB.head_eq]; omega
        · by_cases hjS : j = tScratch
          · subst hjS; rw [hMS.head_eq]; omega
          · rw [hOthers j hjR hjB hjS]; exact hOtherBounds j hjR hjB hjS
    by_cases hiLt : i < S
    · left
      have hReadR : (tapes tRuler).cells (tapes tRuler).head = .bit true := by
        rw [hMR.read_lt (by rw [hRLen]; omega)]
        simp only [rulerList, Nat.add_comm 1 i]
        rw [List.getElem_append_left (by simp; omega), List.getElem_cons_succ]
        simp
      let b := bits[i]'(by omega)
      have hReadB : (tapes tArgB).cells (tapes tArgB).head = .bit b := by
        rw [hMB.read_lt (by simp [fullB, hLen]; omega)]
        rw [List.getElem_append_left (by simp [hLen]; omega),
          List.getElem_append_right (by simp)]
        simp only [Nat.add_sub_cancel_left, List.getElem_map]
        rfl
      obtain ⟨ntR, hUpdR, hFR⟩ := hMR.update_keep .right rfl
      obtain ⟨ntB, hUpdB, hFB⟩ := hMB.update_keep .right rfl
      obtain ⟨ntS, hUpdS, hFS⟩ := hMS.update_append_move
        (by simp [List.length_take, hLen]; omega) (SimSym.bit b) .right rfl
      let t1 := fun j => if j = tRuler then ntR else if j = tArgB then ntB
        else if j = tScratch then ntS else tapes j
      have hT1Bounds : ∀ j, (t1 j).head < bound j := by
        intro j
        match j with
        | ⟨0, _⟩ => change ntR.head < bound tRuler; rw [hFR.head_eq]; omega
        | ⟨1, _⟩ => change (tapes tRegs).head < bound tRegs; exact hBounds tRegs
        | ⟨2, _⟩ => change (tapes tArgA).head < bound tArgA; exact hBounds tArgA
        | ⟨3, _⟩ => change ntB.head < bound tArgB; rw [hFB.head_eq]; omega
        | ⟨4, _⟩ => change ntS.head < bound tScratch; rw [hFS.head_eq]; omega
      have hReaches : (body ()).ReachesExit input bound tapes inHead (.inl ()) t1 inHead := by
        dsimp only [body]
        convert TMComponent.atom_reachesExit _ input bound tapes inHead hBounds inHead _ t1 _ hT1Bounds
        · simp [mkWorkAction, hReadR]
        · simp [mkWorkAction, hReadR, moveHead]
        · intro j
          simp only [mkWorkAction, hReadR, hReadB, simBitVal]
          by_cases hj0 : j = tRuler
          · subst hj0; simpa [t1, tRuler, tArgB, tScratch] using hUpdR
          · by_cases hj3 : j = tArgB
            · subst hj3; simpa [t1, tRuler, tArgB, tScratch] using hUpdB
            · by_cases hj4 : j = tScratch
              · subst hj4; simpa [t1, tRuler, tArgB, tScratch] using hUpdS
              · simpa [t1, hj0, hj3, hj4] using OneSidedTape.updateAndMove_stay_self (tapes j)
      have hTakeSucc : bits.take (i + 1) = bits.take i ++ [b] := List.take_succ_eq_append_getElem (by omega)
      refine ⟨(), t1, inHead, hReaches, ⟨i + 1, by omega, rfl, ?_, ?_, ?_, ?_⟩, ?_⟩
      · simpa [t1, Nat.add_assoc] using hFR
      · simpa [t1, tRuler, tArgB, Nat.add_assoc] using hFB
      · have hNe1 : tScratch ≠ tRuler := by decide
        have hNe2 : tScratch ≠ tArgB := by decide
        simpa [t1, hNe1, hNe2, hTakeSucc, List.map_append, List.append_assoc, Nat.add_assoc] using hFS
      · intro j hjR hjB hjS
        simp only [t1, hjR, hjB, hjS, ↓reduceIte]
        exact hOthers j hjR hjB hjS
      · change 1 + S - ntR.head < 1 + S - (tapes tRuler).head
        rw [hFR.head_eq, hMR.head_eq]
        omega
    · right
      have hiS : i = S := by omega
      have hReadR : (tapes tRuler).cells (tapes tRuler).head = .endMark := by
        rw [hMR.read_lt (by rw [hRLen]; omega)]
        simp only [rulerList, Nat.add_comm 1 i]
        rw [List.getElem_append_right (by simp [hiS])]
        simp [hiS]
      have hTakeAll : bits.take i = bits := by rw [hiS, ← hLen, List.take_length]
      have hMS' : TapeMatches (tapes tScratch) (.leftMark :: bits.map SimSym.bit) (1 + S) := by
        rw [← hTakeAll, ← hiS]; exact hMS
      obtain ⟨ntS, hUpdS, hFS⟩ := hMS'.update_append_move
        (by simp [hLen]; omega) SimSym.endMark .stay rfl
      let t1 := fun j => if j = tScratch then ntS else tapes j
      have hT1Bounds : ∀ j, (t1 j).head < bound j := by
        intro j
        by_cases hj : j = tScratch
        · subst hj; simpa [t1, hFS.head_eq] using (by omega : 1 + S < bound tScratch)
        · simp [t1, hj, hBounds j]
      have hReaches : (body ()).ReachesExit input bound tapes inHead (.inr ()) t1 inHead := by
        dsimp only [body]
        convert TMComponent.atom_reachesExit _ input bound tapes inHead hBounds inHead _ t1 _ hT1Bounds
        · simp [mkWorkAction, hReadR]
        · simp [mkWorkAction, hReadR, moveHead]
        · intro j
          simp only [mkWorkAction, hReadR]
          by_cases hj : j = tScratch
          · subst hj; simpa [t1] using hUpdS
          · simp [t1, hj, OneSidedTape.updateAndMove_stay_self]
      refine ⟨(), t1, inHead, hReaches, rfl, ?_, ?_, ?_, ?_⟩
      · have hNe : tRuler ≠ tScratch := by decide
        simpa [t1, hNe, hiS] using hMR
      · have hNe : tArgB ≠ tScratch := by decide
        simpa [t1, hNe, hiS] using hMB
      · simpa [t1, scratchList, List.append_assoc] using hFS
      · intro j hjR hjB hjS
        simp only [t1, hjS, ↓reduceIte]
        exact hOthers j hjR hjB hjS
  obtain ⟨⟨⟩, tLoop, finalInHead, hLoop, hHead, hRL, hBL, hSL, hOthersL⟩ :=
    loopWithState_reachesExit () body input bound Inv measure Post hStep initTapes inHead
      ⟨0, Nat.zero_le S, rfl, hMatchR, by simpa [fullB, List.append_assoc] using hMatchB,
        by simpa using hMatchS, fun _ _ _ _ => rfl⟩
  subst finalInHead
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
  have hScratchNoLeft : ∀ i, 1 ≤ i → i < scratchList.length →
      scratchList[i]? ≠ some SimSym.leftMark := by
    intro i hi1 hiLt
    cases i with
    | zero => omega
    | succ i =>
      simp only [scratchList, List.length_append, List.length_cons, List.length_map,
        List.length_nil, hLen] at hiLt
      by_cases hiS : i < S
      · simp only [scratchList]
        rw [List.getElem?_append_left (by simp [hLen]; omega), List.getElem?_cons_succ,
          List.getElem?_eq_getElem (by simp [hLen, hiS])]
        simp
      · have hiEq : i = S := by omega
        subst hiEq
        simp only [scratchList]
        rw [List.getElem?_append_right (by simp [hLen])]
        simp [hLen]
  have hTLoopOtherR : ∀ j, j ≠ tRuler → (tLoop j).head < bound j := by
    intro j hjR
    by_cases hjB : j = tArgB
    · subst hjB; rw [hBL.head_eq]; exact hBoundB
    · by_cases hjS : j = tScratch
      · subst hjS; rw [hSL.head_eq]; omega
      · rw [hOthersL j hjR hjB hjS]; exact hOtherBounds j hjR hjB hjS
  obtain ⟨tRewR, hRewR, hRFin, hOthersR⟩ :=
    rewindTape_reachesExit (InputAlphabet := InputAlphabet) tRuler input bound
      rulerList (by simp [rulerList]) (by simp [rulerList]) hRulerNoLeft
      (by rw [hRLen]; exact hBoundR) tLoop inHead hTLoopOtherR (1 + S) (by omega)
      (by rw [hRLen]; omega) hRL
  have hRewROtherS : ∀ j, j ≠ tScratch → (tRewR j).head < bound j := by
    intro j hjS
    by_cases hjR : j = tRuler
    · subst hjR; rw [hRFin.head_eq]; omega
    · rw [hOthersR j hjR]; exact hTLoopOtherR j hjR
  have hSL' : TapeMatches (tRewR tScratch) scratchList (1 + S) := by
    rw [hOthersR tScratch (by decide)]; exact hSL
  obtain ⟨tRewS, hRewS, hSFin, hOthersS⟩ :=
    rewindTape_reachesExit (InputAlphabet := InputAlphabet) tScratch input bound
      scratchList (by simp [scratchList]) (by simp [scratchList]) hScratchNoLeft
      (by rw [hSLen]; exact hBoundS) tRewR inHead hRewROtherS (1 + S) (by omega)
      (by rw [hSLen]; omega) hSL'
  have hSeqRS := TMComponent.seq_reachesExit (rewindTape InputAlphabet tRuler)
    (rewindTape InputAlphabet tScratch) input bound hRewR hRewS
  have hSeqFull := TMComponent.seq_reachesExit (loopWithState () body)
    ((rewindTape InputAlphabet tRuler).seq (rewindTape InputAlphabet tScratch))
    input bound hLoop hSeqRS
  have hEndEq : tRewS = fun j => if j = tRuler then tRewR tRuler
      else if j = tArgB then tLoop tArgB
      else if j = tScratch then tRewS tScratch else initTapes j := by
    funext j
    by_cases hjS : j = tScratch
    · subst hjS
      have h1 : tScratch ≠ tRuler := by decide
      have h2 : tScratch ≠ tArgB := by decide
      simp [h1, h2]
    · rw [hOthersS j hjS]
      by_cases hjR : j = tRuler
      · subst hjR; simp
      · rw [hOthersR j hjR]
        by_cases hjB : j = tArgB
        · subst hjB; simp [hjR]
        · simp [hjR, hjB, hjS, hOthersL j hjR hjB hjS]
  rw [hEndEq] at hSeqFull
  have hRFin' : TapeMatches (tRewR tRuler)
      (.leftMark :: List.replicate S (.bit true) ++ [.endMark]) 1 := hRFin
  exact ⟨tRewR tRuler, tLoop tArgB, tRewS tScratch, hSeqFull, hRFin', hBL, hSFin⟩

end SavitchLemma
